# -*- coding: utf-8 -*-
"""Typed solver producers for the narrow, pure direct-call equivalence lane.

The public entry point accepts analyses and a structural manifest, never an
arbitrary proof stage or SMT query.  Each stage query is constructed here from
the exact call argument and specialized callee return objects that produced the
manifest facts.
"""

from __future__ import annotations

from dataclasses import dataclass, field
import hashlib
import threading
from typing import Any, Dict, List, Mapping, Optional, Sequence, Tuple

from ..analysis.effect_summary import (
    CallArgumentEvidence,
    CallSiteEffectSummaryEvidence,
    StoreEffect,
)
from ..model import (
    Condition,
    Expression,
    ExpressionType,
    FunctionReturnAnalysis,
    ReturnInfo,
    expression_provenance_key,
)
from ..model.signature import get_declared_type_signedness
from ..model.render_smt import (
    collect_unknown_smt_declarations,
    expression_smt_bit_width,
)
from ..smt import SolverStatus
from .call_effect_obligations import (
    InternalSolverProofArtifact,
    SolverProofRecord,
    _INTERNAL_SOLVER_PRODUCER_TOKEN,
    _digest,
)
from .formula.params import (
    build_parameter_constraint,
    build_parameter_pairs,
    build_parameter_semantic_constraints,
    build_symbol_name_mapping,
    collect_param_info,
)
from .call_effect_proof_input import (
    CALL_EFFECT_PRODUCER_KIND,
    PureCallRegionProofInput,
    PureDirectCallProofInput,
)


_PRODUCER_KIND = CALL_EFFECT_PRODUCER_KIND
_STAGES = (
    "guard_relation",
    "argument_relation",
    "return_relation",
    "memory_relation",
    "caller_memory_relation",
)
_TYPED_RENDERER_TOKEN = object()
_QUERY_AUTHORITY_TOKEN = object()
_TOTAL_BINARY_OPERATORS = frozenset(
    {
        "INT_EQUAL",
        "INT_NOTEQUAL",
        "INT_LESS",
        "INT_LESSEQUAL",
        "INT_SLESS",
        "INT_SLESSEQUAL",
        "INT_ADD",
        "INT_SUB",
        "INT_MULT",
        "INT_AND",
        "INT_OR",
        "INT_XOR",
        "BOOL_AND",
        "BOOL_OR",
        "BOOL_XOR",
        "PIECE",
        "SUBPIECE",
    }
)
_TOTAL_UNARY_OPERATORS = frozenset(
    {
        "INT_ZEXT",
        "INT_SEXT",
        "INT_2COMP",
        "INT_NEGATE",
        "BOOL_NEGATE",
        "CAST",
    }
)


@dataclass(frozen=True)
class PureDirectCallProofProduction:
    artifacts: Tuple[InternalSolverProofArtifact, ...]
    failure_causes: Tuple[str, ...] = ()
    v2_blocker_signals: Tuple[Any, ...] = ()
    v2_prerequisite_signals: Tuple[Any, ...] = ()


@dataclass
class V2CallEffectExecutionContext:
    producer_stage_registry: Any
    lifecycle_projection: Any
    result_occurrence_id: str
    q_open_assignments: Sequence[Tuple[Tuple[str, str], Any]]
    execution_refusal_sink: Any = None
    attempt_ordinals: Dict[Tuple[str, str], int] = field(default_factory=dict)
    _attempt_lock: Any = field(default_factory=threading.RLock, repr=False)
    _q_open_rows_by_obligation_stage: Dict[Tuple[str, str], Tuple[Any, ...]] = field(
        default_factory=dict, init=False, repr=False
    )

    def __post_init__(self) -> None:
        from .v2.contracts import VerifiedLifecyclePrefixProjection

        if type(self.lifecycle_projection) is not VerifiedLifecyclePrefixProjection:
            raise TypeError("v2 execution context requires PREFIX lifecycle authority")
        self.lifecycle_projection.validate()
        if self.result_occurrence_id != self.lifecycle_projection.result_occurrence_id:
            raise ValueError("v2 execution context result differs from lifecycle projection")
        grouped: Dict[Tuple[str, str], List[Any]] = {}
        normalized = tuple(self.q_open_assignments)
        for item in normalized:
            if type(item) is not tuple or len(item) != 2:
                raise TypeError("Q_open assignment must be a duplicate-preserving key/row pair")
            key, row = item
            if (
                type(key) is not tuple
                or len(key) != 2
                or any(type(value) is not str or not value for value in key)
            ):
                raise TypeError("Q_open assignment key must be obligation/stage strings")
            if row not in self.lifecycle_projection.q_open_base:
                raise ValueError("Q_open assignment row is not live in lifecycle projection")
            grouped.setdefault(key, []).append(row)
        self.q_open_assignments = normalized
        self._q_open_rows_by_obligation_stage = {
            key: tuple(rows) for key, rows in grouped.items()
        }

    def membership_for(self, query_authority: "CallEffectSolverQueryAuthority") -> Any:
        from .v2.execution_authority import (
            ProducerAttemptMembership,
            issue_call_effect_requirement_assignment,
        )

        key = (query_authority.obligation_id, query_authority.stage)
        candidates = self._q_open_rows_by_obligation_stage.get(key, ())
        if not candidates:
            raise ValueError("v2 solver stage lacks live Q_open assignment")
        if len(candidates) != 1:
            if callable(self.execution_refusal_sink):
                self.execution_refusal_sink(query_authority, candidates)
            raise ValueError("v2 solver stage has ambiguous live Q_open assignments")
        q_open_row = candidates[0]
        assignment = issue_call_effect_requirement_assignment(
            projection=self.lifecycle_projection,
            q_open_row=q_open_row,
            query_authority=query_authority,
        )
        with self._attempt_lock:
            ordinal = self.attempt_ordinals.get(key, 0) + 1
            self.attempt_ordinals[key] = ordinal
        return ProducerAttemptMembership(
            "call-effect-domain-v1",
            "typed-call-effect-solver-v1",
            "1",
            query_authority.stage,
            q_open_row.proof_requirement_id,
            query_authority.obligation_id,
            query_authority.observation_contract_id,
            "attempted",
            f"{self.result_occurrence_id}:{query_authority.obligation_id}:{query_authority.stage}",
            ordinal,
            query_authority.execution_identity_digest,
            assignment,
        )


@dataclass(frozen=True)
class _RenderedStage:
    stage: str
    query_text: str
    normalized_assertion_text: str
    stage_input_payload: Mapping[str, Any]
    precondition_payload: Mapping[str, Any]
    renderer_token: Any = field(default=None, repr=False, compare=False)


@dataclass(frozen=True, init=False)
class CallEffectSolverQueryAuthority:
    stage: str
    obligation_id: str
    observation_contract_id: str
    left_fact_id: str
    right_fact_id: str
    query_text: str
    normalized_assertion_text: str
    stage_input_digest: str
    precondition_digest: str
    execution_identity_digest: str
    authority_digest: str
    _factory_token: Any = field(default=None, init=False, repr=False, compare=False)

    def __init__(self, *, _factory_token: Any = None, **payload: Any) -> None:
        if _factory_token is not _QUERY_AUTHORITY_TOKEN:
            raise TypeError("call-effect query authority must be typed-renderer issued")
        for name, value in payload.items():
            object.__setattr__(self, name, value)
        object.__setattr__(self, "_factory_token", _factory_token)

    def payload(self) -> Mapping[str, Any]:
        return {
            "stage": self.stage,
            "obligation_id": self.obligation_id,
            "observation_contract_id": self.observation_contract_id,
            "left_fact_id": self.left_fact_id,
            "right_fact_id": self.right_fact_id,
            "query_text": self.query_text,
            "normalized_assertion_text": self.normalized_assertion_text,
            "stage_input_digest": self.stage_input_digest,
            "precondition_digest": self.precondition_digest,
            "execution_identity_digest": self.execution_identity_digest,
        }

    def validate(self) -> None:
        if (
            self.stage not in _STAGES or not self.query_text
            or not self.normalized_assertion_text or not self.obligation_id
            or not self.observation_contract_id or not self.left_fact_id
            or not self.right_fact_id or not self.execution_identity_digest
        ):
            raise ValueError("call-effect typed query authority is incomplete")
        if self.authority_digest != _digest(self.payload()):
            raise ValueError("call-effect typed query authority digest mismatch")


def _issue_solver_query_authority(
    rendered: _RenderedStage,
    proof_input: PureDirectCallProofInput | PureCallRegionProofInput,
) -> CallEffectSolverQueryAuthority:
    if type(rendered) is not _RenderedStage or rendered.renderer_token is not _TYPED_RENDERER_TOKEN:
        raise TypeError("solver query authority requires the sealed typed renderer output")
    stage_input_digest = _digest(rendered.stage_input_payload)
    precondition_digest = _digest(rendered.precondition_payload)
    execution_identity_digest = _digest((
        "call_effect_solver_execution_identity_v1",
        rendered.stage,
        proof_input.obligation_id,
        proof_input.observation_contract_id,
        proof_input.left_fact_id,
        proof_input.right_fact_id,
        stage_input_digest,
        precondition_digest,
    ))
    payload = {
        "stage": rendered.stage,
        "obligation_id": proof_input.obligation_id,
        "observation_contract_id": proof_input.observation_contract_id,
        "left_fact_id": proof_input.left_fact_id,
        "right_fact_id": proof_input.right_fact_id,
        "query_text": rendered.query_text,
        "normalized_assertion_text": rendered.normalized_assertion_text,
        "stage_input_digest": stage_input_digest,
        "precondition_digest": precondition_digest,
        "execution_identity_digest": execution_identity_digest,
    }
    value = CallEffectSolverQueryAuthority(
        **payload,
        authority_digest=_digest(payload),
        _factory_token=_QUERY_AUTHORITY_TOKEN,
    )
    value.validate()
    return value


@dataclass(frozen=True)
class _MemoryWriteEvent:
    event_key: Tuple[Any, ...]
    location_key: Tuple[Any, ...]
    effects: Tuple[StoreEffect, ...]
    provenance: Any


def _evidence_pcode_key(evidence: Any) -> Optional[Tuple[Any, ...]]:
    ref = getattr(evidence, "pcode_op_ref", None)
    stable_key = getattr(ref, "stable_key", None)
    if not callable(stable_key):
        return None
    try:
        value = stable_key()
    except Exception:
        return None
    return tuple(value) if isinstance(value, (tuple, list)) else None


def _find_call_argument_evidence(
    analysis: FunctionReturnAnalysis,
    pcode_key: Tuple[Any, ...],
) -> Optional[CallArgumentEvidence]:
    summary = getattr(analysis, "effect_summary", None)
    candidates = tuple(
        evidence
        for evidence in getattr(summary, "call_argument_evidence", {}).values()
        if isinstance(evidence, CallArgumentEvidence)
        and _evidence_pcode_key(evidence) == pcode_key
    )
    return candidates[0] if len(candidates) == 1 else None


def _find_call_effect_evidence(
    analysis: FunctionReturnAnalysis,
    pcode_key: Tuple[Any, ...],
) -> Optional[CallSiteEffectSummaryEvidence]:
    summary = getattr(analysis, "effect_summary", None)
    candidates = tuple(
        evidence
        for evidence in getattr(summary, "call_site_effect_summary_evidence", ()) or ()
        if isinstance(evidence, CallSiteEffectSummaryEvidence)
        and _evidence_pcode_key(evidence) == pcode_key
    )
    return candidates[0] if len(candidates) == 1 else None


def _effect_store_census_count(effects: Sequence[StoreEffect]) -> int:
    producer_keys = set()
    for effect in tuple(effects or ()):
        provenance = getattr(effect, "provenance", None)
        producer_ref = getattr(provenance, "producer_pcode_op_ref", None)
        if producer_ref is not None:
            producer_keys.add(("pcode", tuple(producer_ref.stable_key())))
        else:
            producer_keys.add(
                (
                    "summary_order",
                    int(effect.order_key),
                    _memory_location_semantic_key(effect.location),
                )
            )
    return len(producer_keys)


def _fact_by_id(manifest: Mapping[str, Any], side: str) -> Dict[str, Mapping[str, Any]]:
    return {
        str(item.get("fact_id")): item
        for item in tuple(manifest.get(f"{side}_facts", ()) or ())
        + tuple(manifest.get(f"{side}_regions", ()) or ())
        if isinstance(item, Mapping) and item.get("fact_id")
    }


def _tuple_key(value: Any) -> Optional[Tuple[Any, ...]]:
    if not isinstance(value, (tuple, list)):
        return None
    return tuple(
        _tuple_key(item) if isinstance(item, (tuple, list)) else item
        for item in value
    )


def _build_inputs(
    manifest: Mapping[str, Any],
    analysis1: FunctionReturnAnalysis,
    analysis2: FunctionReturnAnalysis,
) -> Tuple[
    Tuple[PureDirectCallProofInput | PureCallRegionProofInput, ...],
    Tuple[str, ...],
]:
    certificate = manifest.get("structural_coverage_certificate")
    if not isinstance(certificate, Mapping):
        return (), ("structural_coverage_certificate_missing",)
    if certificate.get("status") != "complete" or certificate.get("verification_status") != "verified":
        return (), ("structural_coverage_certificate_incomplete",)
    certificate_id = str(certificate.get("certificate_id") or "")
    if not certificate_id:
        return (), ("structural_coverage_certificate_id_missing",)

    left_by_id = _fact_by_id(manifest, "left")
    right_by_id = _fact_by_id(manifest, "right")
    eligibility_by_id = {
        str(item.get("obligation_id")): item
        for item in manifest.get("phase2_direct_call_eligibility", ()) or ()
        if isinstance(item, Mapping)
    }
    inputs: List[PureDirectCallProofInput | PureCallRegionProofInput] = []
    failures: List[str] = []

    def caller_observation_width(analysis: FunctionReturnAnalysis) -> Optional[int]:
        try:
            width = int(analysis.get_return_value_solver_bit_width())
        except (AttributeError, TypeError, ValueError):
            return None
        return width if width > 0 else None

    def analysis_return_signed(analysis: FunctionReturnAnalysis) -> Optional[bool]:
        try:
            value = get_declared_type_signedness(
                analysis.get_comparison_type_obj(),
                analysis.get_comparison_type_name(),
            )
            return value if isinstance(value, bool) else None
        except (AttributeError, TypeError, ValueError):
            return None

    for obligation in manifest.get("relational_obligations", ()) or ():
        if not isinstance(obligation, Mapping):
            continue
        obligation_id = str(obligation.get("obligation_id") or "")
        eligibility = eligibility_by_id.get(obligation_id, {})
        relation_kind = str(obligation.get("relation_kind") or "")
        if eligibility.get("status") != "candidate":
            continue
        left_fact_id = str(obligation.get("left_fact_id") or "")
        right_fact_id = str(obligation.get("right_fact_id") or "")
        left_fact = left_by_id.get(left_fact_id)
        right_fact = right_by_id.get(right_fact_id)
        if left_fact is None or right_fact is None:
            failures.append(f"{obligation_id}:typed_fact_missing")
            continue
        if relation_kind in {"call_to_region", "region_to_call"}:
            call_on_left = relation_kind == "call_to_region"
            call_fact = left_fact if call_on_left else right_fact
            region_fact = right_fact if call_on_left else left_fact
            call_analysis = analysis1 if call_on_left else analysis2
            region_analysis = analysis2 if call_on_left else analysis1
            if call_fact.get("fact_kind") != "call_site" or region_fact.get("fact_kind") != "region":
                failures.append(f"{obligation_id}:call_region_endpoint_kind_mismatch")
                continue
            call_key = _tuple_key(
                (call_fact.get("identity") or {}).get("pcode_op_key")
                if isinstance(call_fact.get("identity"), Mapping)
                else None
            )
            if call_key is None:
                failures.append(f"{obligation_id}:call_region_pcode_identity_missing")
                continue
            call_arguments = _find_call_argument_evidence(call_analysis, call_key)
            call_effect = _find_call_effect_evidence(call_analysis, call_key)
            if call_arguments is None or not call_arguments.is_usable():
                failures.append(f"{obligation_id}:call_region_argument_evidence_incomplete")
                continue
            if call_effect is None or (
                call_effect.summary_status != "complete"
                or call_effect.has_unsupported_nested_call
                or call_effect.return_summary_status != "complete"
                or not call_effect.return_partitions
            ):
                failures.append(f"{obligation_id}:call_region_callee_summary_incomplete")
                continue
            region_summary = getattr(region_analysis, "effect_summary", None)
            region_profile = getattr(region_summary, "function_control_effect_profile", None)
            region_returns = tuple(region_analysis.returns or ())
            region_effects = tuple(getattr(region_summary, "effects", ()) or ())
            if region_profile is None:
                failures.append(f"{obligation_id}:inline_region_control_profile_missing")
                continue
            if not (
                bool(region_profile.pcode_enumeration_complete)
                and bool(region_profile.cfg_edges_complete)
                and bool(region_profile.cfg_acyclic)
                and bool(region_profile.terminal_return_coverage_complete)
                and int(region_profile.load_count) == 0
                and int(region_profile.store_count)
                == _effect_store_census_count(region_effects)
                and all(
                    int(getattr(region_profile, name, 0) or 0) == 0
                    for name in (
                        "call_count",
                        "callind_count",
                        "callother_count",
                        "branchind_count",
                        "float_op_count",
                        "pcode_after_return_count",
                        "abnormal_terminal_block_count",
                    )
                )
                and bool(region_profile.call_like_identity_complete)
                and not tuple(region_profile.phase2_unsafe_mnemonics or ())
                and not tuple(region_profile.unsupported_mnemonics or ())
            ):
                failures.append(f"{obligation_id}:inline_region_not_total_trap_free_scalar")
                continue
            if len(call_effect.memory_effects) != int(call_effect.memory_effect_count):
                failures.append(f"{obligation_id}:call_region_memory_effect_coverage_incomplete")
                continue
            if bool(getattr(region_summary, "has_unsupported_call", False)):
                failures.append(f"{obligation_id}:inline_region_unsupported_call_present")
                continue
            if bool(getattr(region_summary, "incomplete_reasons", ()) or ()):
                failures.append(f"{obligation_id}:inline_region_effect_summary_incomplete")
                continue
            if not region_returns:
                failures.append(f"{obligation_id}:inline_region_return_partition_missing")
                continue
            if any(
                item.return_kind not in {"exact", "phi_expansion"}
                for item in region_returns
            ):
                failures.append(f"{obligation_id}:inline_region_nonexact_return_present")
                continue
            if any(bool(item.validation_blockers) for item in region_returns):
                failures.append(f"{obligation_id}:inline_region_return_validation_blocked")
                continue
            inputs.append(
                PureCallRegionProofInput(
                    obligation_id=obligation_id,
                    observation_contract_id=str(obligation.get("observation_contract_id") or ""),
                    left_fact_id=left_fact_id,
                    right_fact_id=right_fact_id,
                    structural_certificate_id=certificate_id,
                    left_fact_payload=left_fact,
                    right_fact_payload=right_fact,
                    call_on_left=call_on_left,
                    call_arguments=call_arguments,
                    call_effect=call_effect,
                    region_returns=region_returns,
                    region_effects=region_effects,
                    left_parameters=tuple(analysis1.parameters or ()),
                    right_parameters=tuple(analysis2.parameters or ()),
                    left_caller_observation_bit_width=caller_observation_width(analysis1),
                    right_caller_observation_bit_width=caller_observation_width(analysis2),
                    region_return_signed=analysis_return_signed(region_analysis),
                    left_caller_effects=tuple(
                        getattr(getattr(analysis1, "effect_summary", None), "effects", ()) or ()
                    ),
                    right_caller_effects=tuple(
                        getattr(getattr(analysis2, "effect_summary", None), "effects", ()) or ()
                    ),
                    left_caller_profile=getattr(
                        getattr(analysis1, "effect_summary", None),
                        "function_control_effect_profile",
                        None,
                    ),
                    right_caller_profile=getattr(
                        getattr(analysis2, "effect_summary", None),
                        "function_control_effect_profile",
                        None,
                    ),
                    left_caller_call_effects=tuple(
                        getattr(
                            getattr(analysis1, "effect_summary", None),
                            "call_site_effect_summary_evidence",
                            (),
                        )
                        or ()
                    ),
                    right_caller_call_effects=tuple(
                        getattr(
                            getattr(analysis2, "effect_summary", None),
                            "call_site_effect_summary_evidence",
                            (),
                        )
                        or ()
                    ),
                )
            )
            continue
        if relation_kind != "call_to_call":
            continue
        if (
            left_fact.get("operation_kind") not in {"direct_call", "indirect_call"}
            or right_fact.get("operation_kind") not in {"direct_call", "indirect_call"}
        ):
            failures.append(f"{obligation_id}:pure_producer_requires_resolved_calls")
            continue
        left_key = _tuple_key(
            (left_fact.get("identity") or {}).get("pcode_op_key")
            if isinstance(left_fact.get("identity"), Mapping)
            else None
        )
        right_key = _tuple_key(
            (right_fact.get("identity") or {}).get("pcode_op_key")
            if isinstance(right_fact.get("identity"), Mapping)
            else None
        )
        if left_key is None or right_key is None:
            failures.append(f"{obligation_id}:pcode_identity_missing")
            continue
        left_arguments = _find_call_argument_evidence(analysis1, left_key)
        right_arguments = _find_call_argument_evidence(analysis2, right_key)
        left_effect = _find_call_effect_evidence(analysis1, left_key)
        right_effect = _find_call_effect_evidence(analysis2, right_key)
        if left_arguments is None or right_arguments is None:
            failures.append(f"{obligation_id}:typed_argument_evidence_missing")
            continue
        if not left_arguments.is_usable() or not right_arguments.is_usable():
            failures.append(f"{obligation_id}:typed_argument_evidence_incomplete")
            continue
        if left_effect is None or right_effect is None:
            failures.append(f"{obligation_id}:typed_effect_evidence_missing")
            continue
        if (
            left_effect.summary_status != "complete"
            or right_effect.summary_status != "complete"
            or left_effect.has_unsupported_nested_call
            or right_effect.has_unsupported_nested_call
        ):
            failures.append(f"{obligation_id}:pure_effect_summary_incomplete")
            continue
        if (
            len(left_effect.memory_effects) != int(left_effect.memory_effect_count)
            or len(right_effect.memory_effects) != int(right_effect.memory_effect_count)
        ):
            failures.append(f"{obligation_id}:typed_memory_effect_coverage_incomplete")
            continue
        if left_effect.return_summary_status != "complete" or right_effect.return_summary_status != "complete":
            failures.append(f"{obligation_id}:complete_return_partition_missing")
            continue
        if not left_effect.return_partitions or not right_effect.return_partitions:
            failures.append(f"{obligation_id}:typed_return_partition_missing")
            continue
        if (
            len(left_effect.return_partitions) != len(left_effect.return_value_keys)
            or len(right_effect.return_partitions) != len(right_effect.return_value_keys)
        ):
            failures.append(f"{obligation_id}:return_partition_key_coverage_mismatch")
            continue
        inputs.append(
            PureDirectCallProofInput(
                obligation_id=obligation_id,
                observation_contract_id=str(obligation.get("observation_contract_id") or ""),
                left_fact_id=left_fact_id,
                right_fact_id=right_fact_id,
                structural_certificate_id=certificate_id,
                left_fact_payload=left_fact,
                right_fact_payload=right_fact,
                left_arguments=left_arguments,
                right_arguments=right_arguments,
                left_effect=left_effect,
                right_effect=right_effect,
                left_parameters=tuple(analysis1.parameters or ()),
                right_parameters=tuple(analysis2.parameters or ()),
                left_caller_observation_bit_width=caller_observation_width(analysis1),
                right_caller_observation_bit_width=caller_observation_width(analysis2),
                left_caller_effects=tuple(
                    getattr(getattr(analysis1, "effect_summary", None), "effects", ()) or ()
                ),
                right_caller_effects=tuple(
                    getattr(getattr(analysis2, "effect_summary", None), "effects", ()) or ()
                ),
                left_caller_profile=getattr(
                    getattr(analysis1, "effect_summary", None),
                    "function_control_effect_profile",
                    None,
                ),
                right_caller_profile=getattr(
                    getattr(analysis2, "effect_summary", None),
                    "function_control_effect_profile",
                    None,
                ),
                left_caller_call_effects=tuple(
                    getattr(
                        getattr(analysis1, "effect_summary", None),
                        "call_site_effect_summary_evidence",
                        (),
                    )
                    or ()
                ),
                right_caller_call_effects=tuple(
                    getattr(
                        getattr(analysis2, "effect_summary", None),
                        "call_site_effect_summary_evidence",
                        (),
                    )
                    or ()
                ),
            )
        )
    return tuple(inputs), tuple(failures)


def _deferred_call_pcode_key(expr: Optional[Expression]) -> Optional[Tuple[Any, ...]]:
    if not isinstance(expr, Expression) or expr.expr_type != ExpressionType.UNKNOWN:
        return None
    runtime_ref = getattr(expr, "runtime_ref", None)
    deferred_ref = getattr(runtime_ref, "deferred_call_ref", None)
    op_ref = getattr(deferred_ref, "pcode_op_ref", None)
    stable_key = getattr(op_ref, "stable_key", None)
    if not callable(stable_key):
        return None
    key = stable_key()
    return tuple(key) if key is not None else None


def _pure_scalar_expression_supported(
    expr: Optional[Expression],
    *,
    allowed_deferred_call_keys: frozenset[Tuple[Any, ...]] = frozenset(),
) -> bool:
    if not isinstance(expr, Expression):
        return False
    if expr.expr_type in {ExpressionType.CONSTANT, ExpressionType.PARAMETER}:
        return int(expression_smt_bit_width(expr) or 0) > 0
    if expr.expr_type == ExpressionType.UNKNOWN:
        key = _deferred_call_pcode_key(expr)
        return (
            key is not None
            and key in allowed_deferred_call_keys
            and int(expression_smt_bit_width(expr) or 0) > 0
        )
    if expr.expr_type not in {ExpressionType.BINARY_OP, ExpressionType.UNARY_OP}:
        return False
    operator = str(getattr(expr, "operator", "") or "")
    if expr.expr_type == ExpressionType.BINARY_OP and operator not in _TOTAL_BINARY_OPERATORS:
        return False
    if expr.expr_type == ExpressionType.UNARY_OP and operator not in _TOTAL_UNARY_OPERATORS:
        return False
    operands = tuple(getattr(expr, "operands", ()) or ())
    return bool(operands) and all(
        _pure_scalar_expression_supported(
            item,
            allowed_deferred_call_keys=allowed_deferred_call_keys,
        )
        for item in operands
    )


def _condition_supported(
    condition: Condition,
    *,
    allowed_deferred_call_keys: frozenset[Tuple[Any, ...]] = frozenset(),
) -> bool:
    return isinstance(condition, Condition) and _pure_scalar_expression_supported(
        condition.expression,
        allowed_deferred_call_keys=allowed_deferred_call_keys,
    )


def _and(*terms: str) -> str:
    values = tuple(term for term in terms if term and term != "true")
    if any(term == "false" for term in terms):
        return "false"
    if not values:
        return "true"
    return values[0] if len(values) == 1 else f"(and {' '.join(values)})"


def _or(terms: Sequence[str]) -> str:
    values = tuple(term for term in terms if term and term != "false")
    if any(term == "true" for term in terms):
        return "true"
    if not values:
        return "false"
    return values[0] if len(values) == 1 else f"(or {' '.join(values)})"


def _render_condition_group(
    conditions: Sequence[Condition],
    symbol_mapping: Mapping[str, str],
    *,
    allowed_deferred_call_keys: frozenset[Tuple[Any, ...]] = frozenset(),
) -> str:
    if not all(
        _condition_supported(
            condition,
            allowed_deferred_call_keys=allowed_deferred_call_keys,
        )
        for condition in conditions
    ):
        raise ValueError("unsupported_guard_expression")
    return _and(
        *(
            condition.to_smt(symbol_name_mapping=symbol_mapping, float_mode="fp")
            for condition in conditions
        )
    )


def _render_reachability(
    evidence: CallArgumentEvidence,
    symbol_mapping: Mapping[str, str],
) -> str:
    path_groups = tuple(evidence.path_conditions or ())
    if not path_groups:
        return "true"
    return _or(
        tuple(
            _render_condition_group(group, symbol_mapping)
            for group in path_groups
        )
    )


def _parameter_prelude(
    proof_input: PureDirectCallProofInput | PureCallRegionProofInput,
):
    left_infos = collect_param_info(list(proof_input.left_parameters), "_1")
    right_infos = collect_param_info(list(proof_input.right_parameters), "_2")
    if len({item.original_name for item in left_infos}) != len(left_infos):
        raise ValueError("left_parameter_names_ambiguous")
    if len({item.original_name for item in right_infos}) != len(right_infos):
        raise ValueError("right_parameter_names_ambiguous")
    pairs = build_parameter_pairs(left_infos, right_infos)
    if any(pair.param1 is None or pair.param2 is None for pair in pairs):
        raise ValueError("caller_parameter_relation_incomplete")
    if (left_infos or right_infos) and not pairs:
        raise ValueError("caller_parameter_relation_missing")
    lines = ["(set-logic QF_BV)"]
    lines.extend(
        f"(declare-const {item.smt_name} (_ BitVec {item.bit_width}))"
        for item in tuple(left_infos) + tuple(right_infos)
    )
    lines.extend(build_parameter_semantic_constraints(left_infos))
    lines.extend(build_parameter_semantic_constraints(right_infos))
    for pair in pairs:
        lines.extend(build_parameter_constraint(pair))
    return (
        lines,
        build_symbol_name_mapping(left_infos),
        build_symbol_name_mapping(right_infos),
    )


def _call_region_parameter_prelude(proof_input: PureCallRegionProofInput):
    lines, left_mapping, right_mapping = _parameter_prelude(proof_input)
    region_mapping = dict(right_mapping if proof_input.call_on_left else left_mapping)
    region_parameters = (
        proof_input.right_parameters
        if proof_input.call_on_left
        else proof_input.left_parameters
    )
    observed_widths: Dict[str, set[int]] = {}

    def collect(expression: Expression) -> None:
        if expression.expr_type == ExpressionType.PARAMETER:
            bits = int(expression_smt_bit_width(expression) or 0)
            if expression.name and bits > 0:
                observed_widths.setdefault(str(expression.name), set()).add(bits)
        for operand in tuple(expression.operands or ()):
            collect(operand)

    for item in proof_input.region_returns:
        collect(item.value)
        for condition in item.conditions:
            collect(condition.expression)
    parameters_by_name = {
        str(item.get("name") or f"param_{item.get('index', 0)}"): item
        for item in region_parameters
    }
    for name, widths in observed_widths.items():
        if len(widths) != 1 or name not in parameters_by_name or name not in region_mapping:
            raise ValueError("inline_region_parameter_width_relation_ambiguous")
        observed_bits = next(iter(widths))
        parameter = parameters_by_name[name]
        declared_bits = int(parameter.get("size", 0) or 0) * 8
        if declared_bits <= 0:
            raise ValueError("inline_region_parameter_width_missing")
        if observed_bits == declared_bits:
            continue
        base_symbol = region_mapping[name]
        auxiliary = f"{base_symbol}_region_{observed_bits}"
        lines.append(f"(declare-const {auxiliary} (_ BitVec {observed_bits}))")
        if observed_bits < declared_bits:
            relation = (
                f"(= {auxiliary} "
                f"((_ extract {observed_bits - 1} 0) {base_symbol}))"
            )
        else:
            if "is_signed" not in parameter:
                raise ValueError("inline_region_parameter_signedness_missing")
            extension = "sign_extend" if bool(parameter.get("is_signed")) else "zero_extend"
            relation = (
                f"(= {auxiliary} "
                f"((_ {extension} {observed_bits - declared_bits}) {base_symbol}))"
            )
        lines.append(f"(assert {relation})")
        region_mapping[name] = auxiliary
    if proof_input.call_on_left:
        return lines, left_mapping, region_mapping
    return lines, region_mapping, right_mapping


def _stage_payload(
    proof_input: PureDirectCallProofInput | PureCallRegionProofInput,
    stage: str,
) -> Dict[str, Any]:
    def condition_key(condition: Condition) -> Tuple[Any, ...]:
        structural_key = getattr(condition, "structural_key", None)
        value = structural_key() if callable(structural_key) else None
        return (
            "condition",
            bool(getattr(condition, "negated", False)),
            value,
        )

    def argument_payload(evidence: CallArgumentEvidence) -> Dict[str, Any]:
        return {
            "pcode_op_key": _evidence_pcode_key(evidence),
            "callee_param_identities": evidence.callee_param_identities,
            "arguments": tuple(
                expression_provenance_key(argument)
                for argument in evidence.arguments or ()
            ),
            "path_conditions": tuple(
                tuple(condition_key(condition) for condition in group)
                for group in evidence.path_conditions or ()
            ),
            "coverage_complete": bool(evidence.coverage_complete),
            "recovery_status": evidence.recovery_status,
        }

    def effect_payload(evidence: CallSiteEffectSummaryEvidence) -> Dict[str, Any]:
        return {
            "stable_key": evidence.stable_key(),
            "return_summary_status": evidence.return_summary_status,
            "return_semantic_bit_width": evidence.return_semantic_bit_width,
            "return_signed": evidence.return_signed,
            "return_partitions": tuple(
                (
                    tuple(condition_key(condition) for condition in conditions),
                    expression_provenance_key(value),
                )
                for conditions, value in evidence.return_partitions or ()
            ),
            "memory_effects": tuple(
                {
                    "location": effect.location.stable_key(),
                    "value": expression_provenance_key(effect.value),
                    "conditions": tuple(
                        condition_key(condition)
                        for condition in effect.conditions or ()
                    ),
                    "order_key": int(effect.order_key),
                    "provenance": (
                        effect.provenance.stable_key()
                        if effect.provenance is not None
                        else None
                    ),
                }
                for effect in evidence.memory_effects or ()
            ),
        }

    common = {
        "producer_contract": "typed_pure_direct_call_v1",
        "stage": stage,
        "obligation_id": proof_input.obligation_id,
        "left_fact": proof_input.left_fact_payload,
        "right_fact": proof_input.right_fact_payload,
        "caller_observation_bit_widths": (
            proof_input.left_caller_observation_bit_width,
            proof_input.right_caller_observation_bit_width,
        ),
        "left_parameters": proof_input.left_parameters,
        "right_parameters": proof_input.right_parameters,
        "left_caller_effects": tuple(
            {
                "location": effect.location.stable_key(),
                "value": expression_provenance_key(effect.value),
                "conditions": tuple(
                    condition_key(condition) for condition in effect.conditions or ()
                ),
                "order_key": int(effect.order_key),
                "provenance": (
                    effect.provenance.stable_key()
                    if effect.provenance is not None
                    else None
                ),
            }
            for effect in proof_input.left_caller_effects
        ),
        "right_caller_effects": tuple(
            {
                "location": effect.location.stable_key(),
                "value": expression_provenance_key(effect.value),
                "conditions": tuple(
                    condition_key(condition) for condition in effect.conditions or ()
                ),
                "order_key": int(effect.order_key),
                "provenance": (
                    effect.provenance.stable_key()
                    if effect.provenance is not None
                    else None
                ),
            }
            for effect in proof_input.right_caller_effects
        ),
    }
    if isinstance(proof_input, PureDirectCallProofInput):
        common.update(
            {
                "left_argument_evidence": argument_payload(proof_input.left_arguments),
                "right_argument_evidence": argument_payload(proof_input.right_arguments),
                "left_effect_evidence": effect_payload(proof_input.left_effect),
                "right_effect_evidence": effect_payload(proof_input.right_effect),
            }
        )
        return common
    common.update(
        {
            "producer_contract": "typed_pure_call_region_v1",
            "call_on_left": proof_input.call_on_left,
            "call_argument_evidence": argument_payload(proof_input.call_arguments),
            "call_effect_evidence": effect_payload(proof_input.call_effect),
            "region_return_signed": proof_input.region_return_signed,
            "region_returns": tuple(
                {
                    "address": item.address,
                    "conditions": tuple(condition_key(c) for c in item.conditions),
                    "value": expression_provenance_key(item.value),
                    "return_kind": item.return_kind,
                    "acceptance_status": item.acceptance_status,
                    "validation_blockers": tuple(item.validation_blockers or ()),
                }
                for item in proof_input.region_returns
            ),
            "region_effects": tuple(
                {
                    "location": item.location.stable_key(),
                    "value": expression_provenance_key(item.value),
                    "conditions": tuple(
                        condition_key(condition)
                        for condition in item.conditions or ()
                    ),
                    "order_key": int(item.order_key),
                }
                for item in proof_input.region_effects
            ),
        }
    )
    return common


def _render_call_region_guard_stage(
    proof_input: PureCallRegionProofInput,
) -> _RenderedStage:
    lines, left_mapping, right_mapping = _call_region_parameter_prelude(proof_input)
    call_mapping = left_mapping if proof_input.call_on_left else right_mapping
    region_mapping = right_mapping if proof_input.call_on_left else left_mapping
    reach = _render_reachability(proof_input.call_arguments, call_mapping)
    callee_guards = tuple(
        _and(reach, _render_condition_group(conditions, call_mapping))
        for conditions, _ in proof_input.call_effect.return_partitions
    )
    region_guards = tuple(
        _and(reach, _render_condition_group(item.conditions, region_mapping))
        for item in proof_input.region_returns
    )
    if not callee_guards or not region_guards:
        raise ValueError("call_region_return_partition_missing")
    violation = _or(
        (
            _and(reach, f"(not {_or(callee_guards)})"),
            _and(reach, f"(not {_or(region_guards)})"),
        )
    )
    lines.extend((f"(assert {violation})", "(check-sat)"))
    return _RenderedStage(
        stage="guard_relation",
        query_text="\n".join(lines),
        normalized_assertion_text=violation,
        stage_input_payload=_stage_payload(proof_input, "guard_relation"),
        precondition_payload={
            "structural_certificate_id": proof_input.structural_certificate_id,
        },
        renderer_token=_TYPED_RENDERER_TOKEN,
    )


def _region_parameter_expressions(
    parameters: Sequence[Mapping[str, Any]],
) -> Tuple[Expression, ...]:
    ordered = sorted(parameters, key=lambda item: int(item.get("index", 0)))
    result: List[Expression] = []
    for parameter in ordered:
        size = int(parameter.get("size", 0) or 0)
        if size <= 0:
            raise ValueError("call_region_parameter_width_missing")
        result.append(
            Expression.parameter(
                str(parameter.get("name") or f"param_{parameter.get('index', 0)}"),
                int(parameter.get("index", 0)),
                size=size,
            )
        )
    return tuple(result)


def _render_call_region_argument_stage(
    proof_input: PureCallRegionProofInput,
    dependency_ids: Tuple[str, ...],
) -> _RenderedStage:
    # This stage relates the call argument to the effective caller ABI input.
    # Region-expression widening is introduced only where those expressions
    # are rendered (guard/return stages).
    lines, left_mapping, right_mapping = _parameter_prelude(proof_input)
    call_mapping = left_mapping if proof_input.call_on_left else right_mapping
    region_mapping = right_mapping if proof_input.call_on_left else left_mapping
    region_parameters = (
        proof_input.right_parameters
        if proof_input.call_on_left
        else proof_input.left_parameters
    )
    reach = _render_reachability(proof_input.call_arguments, call_mapping)
    arguments = tuple(proof_input.call_arguments.arguments or ())
    region_inputs = _region_parameter_expressions(region_parameters)
    if len(arguments) != len(region_inputs):
        raise ValueError("call_region_argument_arity_relation_missing")
    mismatches: List[str] = []
    for argument, region_input in zip(arguments, region_inputs):
        if not _pure_scalar_expression_supported(argument):
            raise ValueError("unsupported_call_region_argument_expression")
        argument_bits = int(expression_smt_bit_width(argument) or 0)
        region_bits = int(expression_smt_bit_width(region_input) or 0)
        if argument_bits <= 0 or region_bits <= 0 or argument_bits > region_bits:
            raise ValueError("call_region_argument_abi_width_relation_missing")
        argument_smt = argument.to_smt(
            symbol_name_mapping=call_mapping, float_mode="fp"
        )
        region_smt = region_input.to_smt(
            symbol_name_mapping=region_mapping, float_mode="fp"
        )
        if argument_bits < region_bits:
            region_smt = f"((_ extract {argument_bits - 1} 0) {region_smt})"
        mismatches.append(f"(not (= {argument_smt} {region_smt}))")
    violation = _and(reach, _or(mismatches))
    lines.extend((f"(assert {violation})", "(check-sat)"))
    return _RenderedStage(
        stage="argument_relation",
        query_text="\n".join(lines),
        normalized_assertion_text=violation,
        stage_input_payload=_stage_payload(proof_input, "argument_relation"),
        precondition_payload={
            "structural_certificate_id": proof_input.structural_certificate_id,
            "dependency_proof_ids": dependency_ids,
        },
        renderer_token=_TYPED_RENDERER_TOKEN,
    )


def _render_call_region_return_stage(
    proof_input: PureCallRegionProofInput,
    dependency_ids: Tuple[str, ...],
) -> _RenderedStage:
    lines, left_mapping, right_mapping = _call_region_parameter_prelude(proof_input)
    call_mapping = left_mapping if proof_input.call_on_left else right_mapping
    region_mapping = right_mapping if proof_input.call_on_left else left_mapping
    reach = _render_reachability(proof_input.call_arguments, call_mapping)
    left_observed = proof_input.left_caller_observation_bit_width
    right_observed = proof_input.right_caller_observation_bit_width
    if (
        left_observed is None
        or right_observed is None
        or int(left_observed) <= 0
        or int(right_observed) <= 0
    ):
        raise ValueError("caller_return_observation_width_relation_missing")
    call_observed = int(left_observed if proof_input.call_on_left else right_observed)
    region_observed = int(right_observed if proof_input.call_on_left else left_observed)
    if call_observed > region_observed:
        raise ValueError("call_region_return_width_relation_direction_unsupported")
    observation_bits = call_observed
    width_relation = None
    if call_observed != region_observed:
        if proof_input.region_return_signed is None:
            raise ValueError("call_region_return_width_relation_signedness_missing")
        semantic_bits = proof_input.call_effect.return_semantic_bit_width
        if semantic_bits is None or int(semantic_bits) < call_observed:
            raise ValueError("call_region_return_width_relation_semantic_width_missing")
        width_relation = {
            "narrow_bits": call_observed,
            "wide_bits": region_observed,
            "wide_side": "right" if proof_input.call_on_left else "left",
            "extension": (
                "sign_extend" if proof_input.region_return_signed else "zero_extend"
            ),
            "proof_basis": "typed_region_return_producer_and_declared_signedness",
        }

    def render_value(
        value: Expression,
        mapping: Mapping[str, str],
        signed: Optional[bool],
        active_guard: str,
    ) -> Tuple[str, int, str]:
        if not _pure_scalar_expression_supported(value):
            raise ValueError("unsupported_call_region_return_expression")
        value_bits = int(expression_smt_bit_width(value) or 0)
        if value_bits <= 0:
            raise ValueError("call_region_return_width_missing")
        value_smt = value.to_smt(symbol_name_mapping=mapping, float_mode="fp")
        extension_violation = "false"
        if value_bits > observation_bits:
            if signed is None:
                raise ValueError("call_region_return_signedness_missing")
            extension = "sign_extend" if signed else "zero_extend"
            canonical = (
                f"((_ {extension} {value_bits - observation_bits}) "
                f"((_ extract {observation_bits - 1} 0) {value_smt}))"
            )
            extension_violation = _and(
                active_guard, f"(not (= {value_smt} {canonical}))"
            )
            value_smt = (
                f"((_ extract {observation_bits - 1} 0) {value_smt})"
            )
        elif value_bits < observation_bits:
            if signed is None:
                raise ValueError("call_region_return_signedness_missing")
            extension = "sign_extend" if signed else "zero_extend"
            value_smt = (
                f"((_ {extension} {observation_bits - value_bits}) {value_smt})"
            )
        return value_smt, observation_bits, extension_violation

    call_cases = []
    for conditions, value in proof_input.call_effect.return_partitions:
        guard = _and(reach, _render_condition_group(conditions, call_mapping))
        rendered_value, bits, extension_violation = render_value(
            value,
            call_mapping,
            proof_input.call_effect.return_signed,
            guard,
        )
        call_cases.append((guard, rendered_value, bits, extension_violation))
    region_cases = []
    for item in proof_input.region_returns:
        guard = _and(reach, _render_condition_group(item.conditions, region_mapping))
        rendered_value, bits, extension_violation = render_value(
            item.value,
            region_mapping,
            proof_input.region_return_signed,
            guard,
        )
        region_cases.append((guard, rendered_value, bits, extension_violation))
    if not call_cases or not region_cases:
        raise ValueError("call_region_return_partition_missing")

    violations: List[str] = [
        _and(reach, f"(not {_or(tuple(item[0] for item in call_cases))})"),
        _and(reach, f"(not {_or(tuple(item[0] for item in region_cases))})"),
    ]
    violations.extend(item[3] for item in call_cases + region_cases)
    for call_guard, call_value, _, _ in call_cases:
        for region_guard, region_value, _, _ in region_cases:
            violations.append(
                _and(
                    call_guard,
                    region_guard,
                    f"(not (= {call_value} {region_value}))",
                )
            )
    for cases in (call_cases, region_cases):
        for index, (first_guard, first_value, _, _) in enumerate(cases):
            for second_guard, second_value, _, _ in cases[index + 1 :]:
                violations.append(
                    _and(
                        first_guard,
                        second_guard,
                        f"(not (= {first_value} {second_value}))",
                    )
                )
    violation = _or(tuple(violations))
    lines.extend((f"(assert {violation})", "(check-sat)"))
    return _RenderedStage(
        stage="return_relation",
        query_text="\n".join(lines),
        normalized_assertion_text=violation,
        stage_input_payload=_stage_payload(proof_input, "return_relation"),
        precondition_payload={
            "structural_certificate_id": proof_input.structural_certificate_id,
            "dependency_proof_ids": dependency_ids,
            "return_width_relation": width_relation,
        },
        renderer_token=_TYPED_RENDERER_TOKEN,
    )


def _render_guard_stage(proof_input: PureDirectCallProofInput) -> _RenderedStage:
    lines, left_mapping, right_mapping = _parameter_prelude(proof_input)
    left_reach = _render_reachability(proof_input.left_arguments, left_mapping)
    right_reach = _render_reachability(proof_input.right_arguments, right_mapping)
    violation = f"(xor {left_reach} {right_reach})"
    lines.extend((f"(assert {violation})", "(check-sat)"))
    return _RenderedStage(
        stage="guard_relation",
        query_text="\n".join(lines),
        normalized_assertion_text=violation,
        stage_input_payload=_stage_payload(proof_input, "guard_relation"),
        precondition_payload={
            "structural_certificate_id": proof_input.structural_certificate_id,
        },
        renderer_token=_TYPED_RENDERER_TOKEN,
    )


def _render_argument_stage(
    proof_input: PureDirectCallProofInput,
    dependency_ids: Tuple[str, ...],
) -> _RenderedStage:
    lines, left_mapping, right_mapping = _parameter_prelude(proof_input)
    left_reach = _render_reachability(proof_input.left_arguments, left_mapping)
    right_reach = _render_reachability(proof_input.right_arguments, right_mapping)
    left_args = tuple(proof_input.left_arguments.arguments or ())
    right_args = tuple(proof_input.right_arguments.arguments or ())
    if len(left_args) != len(right_args):
        raise ValueError("argument_arity_relation_missing")
    mismatches: List[str] = []
    for left, right in zip(left_args, right_args):
        if not _pure_scalar_expression_supported(left) or not _pure_scalar_expression_supported(right):
            raise ValueError("unsupported_argument_expression")
        left_bits = int(expression_smt_bit_width(left) or 0)
        right_bits = int(expression_smt_bit_width(right) or 0)
        if left_bits <= 0 or left_bits != right_bits:
            raise ValueError("argument_abi_width_relation_missing")
        left_smt = left.to_smt(symbol_name_mapping=left_mapping, float_mode="fp")
        right_smt = right.to_smt(symbol_name_mapping=right_mapping, float_mode="fp")
        mismatches.append(f"(not (= {left_smt} {right_smt}))")
    violation = _and(left_reach, right_reach, _or(mismatches))
    lines.extend((f"(assert {violation})", "(check-sat)"))
    return _RenderedStage(
        stage="argument_relation",
        query_text="\n".join(lines),
        normalized_assertion_text=violation,
        stage_input_payload=_stage_payload(proof_input, "argument_relation"),
        precondition_payload={
            "structural_certificate_id": proof_input.structural_certificate_id,
            "dependency_proof_ids": dependency_ids,
        },
        renderer_token=_TYPED_RENDERER_TOKEN,
    )


def _render_return_stage(
    proof_input: PureDirectCallProofInput,
    dependency_ids: Tuple[str, ...],
) -> _RenderedStage:
    lines, left_mapping, right_mapping = _parameter_prelude(proof_input)
    left_reach = _render_reachability(proof_input.left_arguments, left_mapping)
    right_reach = _render_reachability(proof_input.right_arguments, right_mapping)

    left_semantic_bits = proof_input.left_effect.return_semantic_bit_width
    right_semantic_bits = proof_input.right_effect.return_semantic_bit_width
    if (left_semantic_bits is None) != (right_semantic_bits is None):
        raise ValueError("return_semantic_width_evidence_incomplete")
    if left_semantic_bits is not None and (
        int(left_semantic_bits) <= 0 or int(right_semantic_bits) <= 0
    ):
        raise ValueError("return_semantic_width_invalid")
    left_observed = proof_input.left_caller_observation_bit_width
    right_observed = proof_input.right_caller_observation_bit_width
    if left_observed is not None or right_observed is not None:
        if (
            left_observed is None
            or right_observed is None
            or int(left_observed) <= 0
            or int(left_observed) != int(right_observed)
        ):
            raise ValueError("caller_return_observation_width_relation_missing")
        semantic_bits = int(left_observed)
        if left_semantic_bits is not None and (
            semantic_bits > int(left_semantic_bits)
            or semantic_bits > int(right_semantic_bits)
        ):
            raise ValueError("caller_observation_exceeds_callee_return_width")
    elif left_semantic_bits is not None and int(left_semantic_bits) == int(right_semantic_bits):
        semantic_bits = int(left_semantic_bits)
    else:
        raise ValueError("return_semantic_width_relation_missing")

    def render_cases(effect, reach, mapping):
        rendered = []
        for conditions, value in effect.return_partitions:
            if not _pure_scalar_expression_supported(value):
                raise ValueError("unsupported_return_expression")
            guard = _render_condition_group(conditions, mapping)
            value_bits = int(expression_smt_bit_width(value) or 0)
            value_smt = value.to_smt(symbol_name_mapping=mapping, float_mode="fp")
            rendered_bits = value_bits
            extension_violation = "false"
            if semantic_bits is not None and value_bits > semantic_bits:
                if effect.return_signed is None:
                    raise ValueError("return_extension_signedness_missing")
                extension = "sign_extend" if effect.return_signed else "zero_extend"
                canonical_extension = (
                    f"((_ {extension} {value_bits - semantic_bits}) "
                    f"((_ extract {semantic_bits - 1} 0) {value_smt}))"
                )
                extension_violation = _and(
                    _and(reach, guard),
                    f"(not (= {value_smt} {canonical_extension}))",
                )
                value_smt = f"((_ extract {semantic_bits - 1} 0) {value_smt})"
                rendered_bits = semantic_bits
            elif semantic_bits is not None and value_bits < semantic_bits:
                if effect.return_signed is None:
                    raise ValueError("return_extension_signedness_missing")
                extension = "sign_extend" if effect.return_signed else "zero_extend"
                value_smt = (
                    f"((_ {extension} {semantic_bits - value_bits}) {value_smt})"
                )
                rendered_bits = semantic_bits
            rendered.append(
                (
                    _and(reach, guard),
                    value_smt,
                    rendered_bits,
                    extension_violation,
                )
            )
        return tuple(rendered)

    left_cases = render_cases(proof_input.left_effect, left_reach, left_mapping)
    right_cases = render_cases(proof_input.right_effect, right_reach, right_mapping)
    if not left_cases or not right_cases:
        raise ValueError("return_partition_missing")
    widths = {bits for _, _, bits, _ in left_cases + right_cases}
    if len(widths) != 1 or next(iter(widths)) <= 0:
        raise ValueError("return_width_relation_missing")

    violations: List[str] = [
        f"(xor {left_reach} {right_reach})",
        _and(left_reach, f"(not {_or(tuple(guard for guard, _, _, _ in left_cases))})"),
        _and(right_reach, f"(not {_or(tuple(guard for guard, _, _, _ in right_cases))})"),
    ]
    violations.extend(item[3] for item in left_cases + right_cases)
    for left_guard, left_value, _, _ in left_cases:
        for right_guard, right_value, _, _ in right_cases:
            violations.append(
                _and(
                    left_guard,
                    right_guard,
                    f"(not (= {left_value} {right_value}))",
                )
            )
    for cases in (left_cases, right_cases):
        for index, (first_guard, first_value, _, _) in enumerate(cases):
            for second_guard, second_value, _, _ in cases[index + 1 :]:
                violations.append(
                    _and(
                        first_guard,
                        second_guard,
                        f"(not (= {first_value} {second_value}))",
                    )
                )
    violation = _or(tuple(violations))
    lines.extend((f"(assert {violation})", "(check-sat)"))
    return _RenderedStage(
        stage="return_relation",
        query_text="\n".join(lines),
        normalized_assertion_text=violation,
        stage_input_payload=_stage_payload(proof_input, "return_relation"),
        precondition_payload={
            "structural_certificate_id": proof_input.structural_certificate_id,
            "dependency_proof_ids": dependency_ids,
        },
        renderer_token=_TYPED_RENDERER_TOKEN,
    )


def _memory_location_semantic_key(location: Any) -> Tuple[Any, ...]:
    base_ref = getattr(location, "base_ref", None)
    semantic_key = getattr(base_ref, "semantic_key", None)
    base_key = semantic_key() if callable(semantic_key) else None
    if base_key is None:
        raise ValueError("memory_effect_location_relation_missing")
    steps = tuple(
        step.stable_key() for step in tuple(getattr(location, "steps", ()) or ())
    )
    size = int(getattr(location, "size", 0) or 0)
    if size <= 0:
        raise ValueError("memory_effect_width_missing")
    return (
        tuple(base_key),
        steps,
        int(getattr(location, "offset", 0) or 0),
        size,
    )


def _memory_event_key(effect: StoreEffect) -> Tuple[Any, ...]:
    provenance = getattr(effect, "provenance", None)
    producer_ref = getattr(provenance, "producer_pcode_op_ref", None)
    if producer_ref is not None:
        return (
            "provenance",
            getattr(provenance, "source_kind", None),
            tuple(producer_ref.stable_key()),
            getattr(provenance, "callee_effect_index", None),
        )
    return (
        "summary_order_location",
        int(effect.order_key),
        _memory_location_semantic_key(effect.location),
    )


def _call_derived_effects_for_evidence(
    caller_effects: Sequence[StoreEffect],
    evidence: CallSiteEffectSummaryEvidence,
) -> Tuple[StoreEffect, ...]:
    pcode_key = _evidence_pcode_key(evidence)
    if pcode_key is None:
        raise ValueError("memory_effect_callsite_identity_missing")
    selected: List[StoreEffect] = []
    indexes = set()
    for effect in tuple(caller_effects or ()):
        provenance = getattr(effect, "provenance", None)
        producer_ref = getattr(provenance, "producer_pcode_op_ref", None)
        if (
            provenance is None
            or getattr(provenance, "source_kind", None) != "call_derived"
            or producer_ref is None
            or tuple(producer_ref.stable_key()) != pcode_key
        ):
            continue
        if getattr(provenance, "call_target_ref", None) != evidence.target_ref:
            raise ValueError("memory_effect_call_target_relation_missing")
        index = getattr(provenance, "callee_effect_index", None)
        if index is None:
            raise ValueError("memory_effect_substitution_provenance_incomplete")
        indexes.add(int(index))
        selected.append(effect)
    expected_indexes = set(range(int(evidence.memory_effect_count)))
    if indexes != expected_indexes:
        raise ValueError("memory_effect_substitution_coverage_missing")
    return tuple(selected)


def _memory_write_events(
    effects: Sequence[StoreEffect],
    *,
    failure_prefix: str,
) -> Tuple[_MemoryWriteEvent, ...]:
    grouped: Dict[Tuple[Any, ...], List[StoreEffect]] = {}
    for effect in tuple(effects or ()):
        grouped.setdefault(_memory_event_key(effect), []).append(effect)
    events: List[_MemoryWriteEvent] = []
    for event_key, variants in grouped.items():
        locations = {
            _memory_location_semantic_key(effect.location) for effect in variants
        }
        orders = {int(effect.order_key) for effect in variants}
        if len(locations) != 1:
            raise ValueError(f"{failure_prefix}_event_location_relation_missing")
        if len(orders) != 1:
            raise ValueError(f"{failure_prefix}_event_order_relation_missing")
        provenance = getattr(variants[0], "provenance", None)
        if provenance is None or not provenance.is_complete():
            raise ValueError(f"{failure_prefix}_execution_provenance_incomplete")
        events.append(
            _MemoryWriteEvent(
                event_key=event_key,
                location_key=next(iter(locations)),
                effects=tuple(variants),
                provenance=provenance,
            )
        )
    return tuple(sorted(events, key=lambda item: repr(item.event_key)))


def _concrete_storage_range(location_key: Tuple[Any, ...]) -> Optional[Tuple[Any, ...]]:
    base_key, steps, offset, size = location_key
    if steps or not isinstance(base_key, tuple) or not base_key:
        return None
    if base_key[0] != "storage" or len(base_key) != 5:
        return None
    try:
        return (
            base_key[1],
            base_key[2],
            int(base_key[3]) + int(offset),
            int(size),
        )
    except (TypeError, ValueError):
        return None


def _memory_alias_relation(
    left_key: Tuple[Any, ...],
    right_key: Tuple[Any, ...],
) -> str:
    if left_key == right_key:
        return "exact"
    left_base, left_steps, left_offset, left_size = left_key
    right_base, right_steps, right_offset, right_size = right_key
    if left_base == right_base:
        if left_steps != right_steps:
            return "unknown"
        left_end = int(left_offset) + int(left_size)
        right_end = int(right_offset) + int(right_size)
        if left_end <= int(right_offset) or right_end <= int(left_offset):
            return "disjoint"
        return "partial_overlap"
    left_storage = _concrete_storage_range(left_key)
    right_storage = _concrete_storage_range(right_key)
    if left_storage is not None and right_storage is not None:
        if left_storage[:2] != right_storage[:2]:
            return "disjoint"
        left_end = int(left_storage[2]) + int(left_storage[3])
        right_end = int(right_storage[2]) + int(right_storage[3])
        if left_end <= int(right_storage[2]) or right_end <= int(left_storage[2]):
            return "disjoint"
        return "partial_overlap"
    if (
        isinstance(left_base, tuple)
        and isinstance(right_base, tuple)
        and left_base
        and right_base
        and left_base[0] == "stack_frame"
        and right_base[0] == "storage"
    ) or (
        isinstance(left_base, tuple)
        and isinstance(right_base, tuple)
        and left_base
        and right_base
        and left_base[0] == "storage"
        and right_base[0] == "stack_frame"
    ):
        return "disjoint"
    return "unknown"


def _pcode_sequence_key(ref: Any) -> Optional[Tuple[int, int, int]]:
    if ref is None:
        return None
    try:
        if ref.seq_time is None or ref.seq_order is None:
            return None
        return (
            int(ref.seq_time),
            int(ref.seq_order),
            int(ref.local_op_ordinal or 0),
        )
    except (TypeError, ValueError):
        return None


def _cfg_reachable(
    source: Tuple[Any, ...],
    target: Tuple[Any, ...],
    edges: Sequence[Tuple[Tuple[Any, ...], Tuple[Any, ...]]],
) -> bool:
    adjacency: Dict[Tuple[Any, ...], set[Tuple[Any, ...]]] = {}
    for edge_source, edge_target in tuple(edges or ()):
        adjacency.setdefault(tuple(edge_source), set()).add(tuple(edge_target))
    pending = list(adjacency.get(tuple(source), ()))
    visited = set()
    while pending:
        current = tuple(pending.pop())
        if current == tuple(target):
            return True
        if current in visited:
            continue
        visited.add(current)
        pending.extend(adjacency.get(current, ()))
    return False


def _call_effect_for_provenance(
    provenance: Any,
    call_effects: Sequence[CallSiteEffectSummaryEvidence],
) -> Optional[CallSiteEffectSummaryEvidence]:
    producer_ref = getattr(provenance, "producer_pcode_op_ref", None)
    if producer_ref is None:
        return None
    producer_key = tuple(producer_ref.stable_key())
    candidates = tuple(
        evidence
        for evidence in tuple(call_effects or ())
        if _evidence_pcode_key(evidence) == producer_key
        and evidence.target_ref == getattr(provenance, "call_target_ref", None)
    )
    return candidates[0] if len(candidates) == 1 else None


def _event_order_relation(
    left_event: _MemoryWriteEvent,
    right_event: _MemoryWriteEvent,
    profile: Any,
    call_effects: Sequence[CallSiteEffectSummaryEvidence],
) -> str:
    left_provenance = left_event.provenance
    right_provenance = right_event.provenance
    left_outer_ref = left_provenance.producer_pcode_op_ref
    right_outer_ref = right_provenance.producer_pcode_op_ref
    same_callsite = bool(
        left_provenance.source_kind == "call_derived"
        and right_provenance.source_kind == "call_derived"
        and tuple(left_outer_ref.stable_key()) == tuple(right_outer_ref.stable_key())
        and left_provenance.call_target_ref == right_provenance.call_target_ref
    )
    if same_callsite:
        left_nested = left_provenance.nested_effect_provenance
        right_nested = right_provenance.nested_effect_provenance
        evidence = _call_effect_for_provenance(left_provenance, call_effects)
        if left_nested is None or right_nested is None or evidence is None:
            return "unproven"
        left_ref = left_nested.producer_pcode_op_ref
        right_ref = right_nested.producer_pcode_op_ref
        left_block = left_nested.producer_block_ref
        right_block = right_nested.producer_block_ref
        edges = tuple(evidence.callee_cfg_edge_keys or ())
        cfg_complete = bool(evidence.callee_ordered_scalar_store_candidate)
    else:
        left_ref = left_outer_ref
        right_ref = right_outer_ref
        left_block = left_provenance.producer_block_ref
        right_block = right_provenance.producer_block_ref
        edges = tuple(getattr(profile, "region_cfg_edge_keys", ()) or ())
        cfg_complete = bool(
            profile is not None
            and getattr(profile, "cfg_edges_complete", False)
            and getattr(profile, "cfg_acyclic", False)
        )
    if left_block is None or right_block is None:
        return "unproven"
    left_block_key = tuple(left_block.stable_key())
    right_block_key = tuple(right_block.stable_key())
    if left_block_key == right_block_key:
        left_sequence = _pcode_sequence_key(left_ref)
        right_sequence = _pcode_sequence_key(right_ref)
        if left_sequence is None or right_sequence is None or left_sequence == right_sequence:
            return "unproven"
        return "before" if left_sequence < right_sequence else "after"
    if not cfg_complete:
        return "unproven"
    left_reaches_right = _cfg_reachable(left_block_key, right_block_key, edges)
    right_reaches_left = _cfg_reachable(right_block_key, left_block_key, edges)
    if left_reaches_right == right_reaches_left:
        return "exclusive_candidate" if not left_reaches_right else "unproven"
    return "before" if left_reaches_right else "after"


def _memory_partial_order_certificate(
    events: Sequence[_MemoryWriteEvent],
    profile: Any,
    call_effects: Sequence[CallSiteEffectSummaryEvidence],
    *,
    side: str,
    failure_prefix: str,
) -> Dict[str, Any]:
    edges: List[Tuple[int, int, str]] = []
    disjoint_pairs: List[Tuple[int, int]] = []
    guard_exclusivity_pairs: List[Tuple[int, int]] = []
    for left_index, left_event in enumerate(events):
        for right_index in range(left_index + 1, len(events)):
            right_event = events[right_index]
            relation = _memory_alias_relation(
                left_event.location_key,
                right_event.location_key,
            )
            if relation == "unknown":
                raise ValueError(f"{failure_prefix}_alias_relation_missing")
            if relation == "partial_overlap":
                raise ValueError(f"{failure_prefix}_partial_overlap_unsupported")
            if relation == "disjoint":
                disjoint_pairs.append((left_index, right_index))
                continue
            order_relation = _event_order_relation(
                left_event,
                right_event,
                profile,
                call_effects,
            )
            if order_relation == "unproven":
                raise ValueError(f"{failure_prefix}_order_relation_missing")
            if order_relation == "exclusive_candidate":
                guard_exclusivity_pairs.append((left_index, right_index))
            elif order_relation == "before":
                edges.append((left_index, right_index, "must_happen_before"))
            else:
                edges.append((right_index, left_index, "must_happen_before"))
    return {
        "side": side,
        "status": "complete",
        "event_count": len(events),
        "events": tuple(
            {
                "event_index": index,
                "event_key": event.event_key,
                "location_key": event.location_key,
                "variant_count": len(event.effects),
                "producer_block_key": event.provenance.producer_block_ref.stable_key(),
                "producer_sequence_key": _pcode_sequence_key(
                    event.provenance.producer_pcode_op_ref
                ),
            }
            for index, event in enumerate(events)
        ),
        "dependency_edges": tuple(edges),
        "proven_disjoint_pairs": tuple(disjoint_pairs),
        "guard_exclusivity_proof_pairs": tuple(guard_exclusivity_pairs),
    }


def _final_memory_cases(
    events: Sequence[_MemoryWriteEvent],
    dependency_edges: Sequence[Tuple[int, int, str]],
    mapping: Mapping[str, str],
    reach: str,
    *,
    failure_prefix: str,
    allowed_deferred_call_keys: frozenset[Tuple[Any, ...]] = frozenset(),
) -> Dict[Tuple[Any, ...], Tuple[Tuple[str, str], ...]]:
    by_location: Dict[Tuple[Any, ...], List[Tuple[str, str]]] = {}
    must_happen_before = {
        (int(source), int(target))
        for source, target, relation in tuple(dependency_edges or ())
        if relation == "must_happen_before"
    }
    for event_index, event in enumerate(events):
        later_guards: List[str] = []
        for later_index, later_event in enumerate(events):
            if (event_index, later_index) not in must_happen_before:
                continue
            if later_event.location_key != event.location_key:
                continue
            later_guards.extend(
                _and(
                    reach,
                    _render_condition_group(
                        effect.conditions,
                        mapping,
                        allowed_deferred_call_keys=allowed_deferred_call_keys,
                    ),
                )
                for effect in later_event.effects
            )
        later_active = _or(tuple(later_guards))
        expected_bits = int(event.location_key[3]) * 8
        for effect in event.effects:
            if not _pure_scalar_expression_supported(
                effect.value,
                allowed_deferred_call_keys=allowed_deferred_call_keys,
            ):
                raise ValueError(f"{failure_prefix}_value_relation_unsupported")
            bits = int(expression_smt_bit_width(effect.value) or 0)
            if bits <= 0 or bits != expected_bits:
                raise ValueError(f"{failure_prefix}_value_width_relation_missing")
            guard = _and(
                reach,
                _render_condition_group(
                    effect.conditions,
                    mapping,
                    allowed_deferred_call_keys=allowed_deferred_call_keys,
                ),
            )
            if later_guards:
                guard = _and(guard, f"(not {later_active})")
            value = effect.value.to_smt(
                symbol_name_mapping=mapping,
                float_mode="fp",
            )
            by_location.setdefault(event.location_key, []).append((guard, value))
    return {key: tuple(value) for key, value in by_location.items()}


def _render_final_post_state_relation(
    left_effects: Sequence[StoreEffect],
    right_effects: Sequence[StoreEffect],
    left_mapping: Mapping[str, str],
    right_mapping: Mapping[str, str],
    left_reach: str,
    right_reach: str,
    left_profile: Any,
    right_profile: Any,
    left_call_effects: Sequence[CallSiteEffectSummaryEvidence],
    right_call_effects: Sequence[CallSiteEffectSummaryEvidence],
    *,
    failure_prefix: str,
    left_allowed_deferred_call_keys: frozenset[Tuple[Any, ...]] = frozenset(),
    right_allowed_deferred_call_keys: frozenset[Tuple[Any, ...]] = frozenset(),
) -> Tuple[List[str], Dict[str, Any], Dict[str, Any]]:
    left_events = _memory_write_events(left_effects, failure_prefix=failure_prefix)
    right_events = _memory_write_events(right_effects, failure_prefix=failure_prefix)
    if not left_events or not right_events:
        raise ValueError(f"{failure_prefix}_count_relation_missing")
    left_certificate = _memory_partial_order_certificate(
        left_events,
        left_profile,
        left_call_effects,
        side="left",
        failure_prefix=failure_prefix,
    )
    right_certificate = _memory_partial_order_certificate(
        right_events,
        right_profile,
        right_call_effects,
        side="right",
        failure_prefix=failure_prefix,
    )
    left_final = _final_memory_cases(
        left_events,
        left_certificate["dependency_edges"],
        left_mapping,
        left_reach,
        failure_prefix=failure_prefix,
        allowed_deferred_call_keys=left_allowed_deferred_call_keys,
    )
    right_final = _final_memory_cases(
        right_events,
        right_certificate["dependency_edges"],
        right_mapping,
        right_reach,
        failure_prefix=failure_prefix,
        allowed_deferred_call_keys=right_allowed_deferred_call_keys,
    )
    if set(left_final) != set(right_final):
        raise ValueError(f"{failure_prefix}_location_relation_missing")

    violations: List[str] = []
    for events, mapping, reach, certificate, allowed_call_keys in (
        (
            left_events,
            left_mapping,
            left_reach,
            left_certificate,
            left_allowed_deferred_call_keys,
        ),
        (
            right_events,
            right_mapping,
            right_reach,
            right_certificate,
            right_allowed_deferred_call_keys,
        ),
    ):
        for left_index, right_index in certificate[
            "guard_exclusivity_proof_pairs"
        ]:
            left_active = _or(
                tuple(
                    _and(
                        reach,
                        _render_condition_group(
                            effect.conditions,
                            mapping,
                            allowed_deferred_call_keys=allowed_call_keys,
                        ),
                    )
                    for effect in events[left_index].effects
                )
            )
            right_active = _or(
                tuple(
                    _and(
                        reach,
                        _render_condition_group(
                            effect.conditions,
                            mapping,
                            allowed_deferred_call_keys=allowed_call_keys,
                        ),
                    )
                    for effect in events[right_index].effects
                )
            )
            violations.append(_and(left_active, right_active))
    for location_key in sorted(left_final, key=repr):
        left_cases = left_final[location_key]
        right_cases = right_final[location_key]
        left_active = _or(tuple(guard for guard, _ in left_cases))
        right_active = _or(tuple(guard for guard, _ in right_cases))
        violations.append(f"(xor {left_active} {right_active})")
        for left_guard, left_value in left_cases:
            for right_guard, right_value in right_cases:
                violations.append(
                    _and(
                        left_guard,
                        right_guard,
                        f"(not (= {left_value} {right_value}))",
                    )
                )
        for cases in (left_cases, right_cases):
            for index, (first_guard, first_value) in enumerate(cases):
                for second_guard, second_value in cases[index + 1 :]:
                    violations.append(
                        _and(
                            first_guard,
                            second_guard,
                            f"(not (= {first_value} {second_value}))",
                        )
                    )
    return violations, left_certificate, right_certificate


def _render_memory_stage(
    proof_input: PureDirectCallProofInput,
    dependency_ids: Tuple[str, ...],
) -> _RenderedStage:
    lines, left_mapping, right_mapping = _parameter_prelude(proof_input)
    left_reach = _render_reachability(proof_input.left_arguments, left_mapping)
    right_reach = _render_reachability(proof_input.right_arguments, right_mapping)
    violations, left_partial_order, right_partial_order = _render_final_post_state_relation(
        _call_derived_effects_for_evidence(
            proof_input.left_caller_effects,
            proof_input.left_effect,
        ),
        _call_derived_effects_for_evidence(
            proof_input.right_caller_effects,
            proof_input.right_effect,
        ),
        left_mapping,
        right_mapping,
        left_reach,
        right_reach,
        proof_input.left_caller_profile,
        proof_input.right_caller_profile,
        proof_input.left_caller_call_effects,
        proof_input.right_caller_call_effects,
        failure_prefix="memory_effect",
    )
    violation = _or(tuple((f"(xor {left_reach} {right_reach})", *violations)))
    lines.extend((f"(assert {violation})", "(check-sat)"))
    return _RenderedStage(
        stage="memory_relation",
        query_text="\n".join(lines),
        normalized_assertion_text=violation,
        stage_input_payload=_stage_payload(proof_input, "memory_relation"),
        precondition_payload={
            "structural_certificate_id": proof_input.structural_certificate_id,
            "dependency_proof_ids": dependency_ids,
            "memory_observation_policy": "alias_aware_final_post_state",
            "left_partial_order_certificate": left_partial_order,
            "right_partial_order_certificate": right_partial_order,
        },
        renderer_token=_TYPED_RENDERER_TOKEN,
    )


def _render_call_region_memory_stage(
    proof_input: PureCallRegionProofInput,
    dependency_ids: Tuple[str, ...],
) -> _RenderedStage:
    lines, left_mapping, right_mapping = _call_region_parameter_prelude(proof_input)
    call_mapping = left_mapping if proof_input.call_on_left else right_mapping
    region_mapping = right_mapping if proof_input.call_on_left else left_mapping
    reach = _render_reachability(proof_input.call_arguments, call_mapping)
    if proof_input.call_on_left:
        left_effects, right_effects = (
            _call_derived_effects_for_evidence(
                proof_input.left_caller_effects,
                proof_input.call_effect,
            ),
            proof_input.region_effects,
        )
    else:
        left_effects, right_effects = (
            proof_input.region_effects,
            _call_derived_effects_for_evidence(
                proof_input.right_caller_effects,
                proof_input.call_effect,
            ),
        )
    violations, left_partial_order, right_partial_order = _render_final_post_state_relation(
        left_effects,
        right_effects,
        left_mapping,
        right_mapping,
        reach,
        reach,
        proof_input.left_caller_profile,
        proof_input.right_caller_profile,
        proof_input.left_caller_call_effects,
        proof_input.right_caller_call_effects,
        failure_prefix="memory_effect",
    )
    violation = _or(tuple(violations))
    lines.extend((f"(assert {violation})", "(check-sat)"))
    return _RenderedStage(
        stage="memory_relation",
        query_text="\n".join(lines),
        normalized_assertion_text=violation,
        stage_input_payload=_stage_payload(proof_input, "memory_relation"),
        precondition_payload={
            "structural_certificate_id": proof_input.structural_certificate_id,
            "dependency_proof_ids": dependency_ids,
            "memory_observation_policy": "alias_aware_final_post_state",
            "left_partial_order_certificate": left_partial_order,
            "right_partial_order_certificate": right_partial_order,
        },
        renderer_token=_TYPED_RENDERER_TOKEN,
    )


def _caller_effect_coverage_payload(
    effects: Sequence[StoreEffect],
    profile: Any,
    call_effects: Sequence[CallSiteEffectSummaryEvidence],
    *,
    side: str,
) -> Dict[str, Any]:
    """Certify that the full caller write set has explicit object provenance."""

    if profile is None:
        raise ValueError(f"{side}_caller_effect_profile_missing")
    if not all(
        bool(getattr(profile, attribute, False))
        for attribute in (
            "pcode_enumeration_complete",
            "cfg_edges_complete",
            "terminal_return_coverage_complete",
            "call_like_identity_complete",
        )
    ):
        raise ValueError(f"{side}_caller_effect_census_incomplete")
    if not bool(getattr(profile, "cfg_acyclic", False)):
        raise ValueError(f"{side}_caller_effect_order_not_acyclic")

    call_keys = tuple(
        tuple(key)
        for key in tuple(getattr(profile, "call_like_pcode_op_keys", ()) or ())
    )
    evidence_by_key: Dict[Tuple[Any, ...], CallSiteEffectSummaryEvidence] = {}
    for evidence in tuple(call_effects or ()):
        key = _evidence_pcode_key(evidence)
        if key is None or key in evidence_by_key:
            raise ValueError(f"{side}_caller_call_effect_identity_incomplete")
        evidence_by_key[key] = evidence
        if (
            evidence.summary_status != "complete"
            or evidence.has_unsupported_nested_call
            or tuple(evidence.incomplete_reasons or ())
            or len(tuple(evidence.memory_effects or ()))
            != int(evidence.memory_effect_count)
        ):
            raise ValueError(f"{side}_caller_call_effect_summary_incomplete")
    if len(set(call_keys)) != len(call_keys) or set(call_keys) != set(evidence_by_key):
        raise ValueError(f"{side}_caller_call_effect_census_mismatch")

    local_refs = set()
    derived_indexes: Dict[Tuple[Any, ...], set[int]] = {}
    for effect in tuple(effects or ()):
        provenance = effect.provenance
        if provenance is None or not provenance.is_complete():
            raise ValueError(f"{side}_caller_store_provenance_incomplete")
        producer_ref = provenance.producer_pcode_op_ref
        producer_key = tuple(producer_ref.stable_key())
        mnemonic = str(getattr(producer_ref, "mnemonic", "") or "").upper()
        if provenance.source_kind == "local_store":
            if mnemonic != "STORE":
                raise ValueError(f"{side}_caller_local_store_identity_mismatch")
            local_refs.add(producer_key)
            continue
        if mnemonic not in {"CALL", "CALLIND"} or producer_key not in evidence_by_key:
            raise ValueError(f"{side}_caller_derived_store_identity_mismatch")
        evidence = evidence_by_key[producer_key]
        if provenance.call_target_ref != evidence.target_ref:
            raise ValueError(f"{side}_caller_derived_store_target_mismatch")
        derived_indexes.setdefault(producer_key, set()).add(
            int(provenance.callee_effect_index)
        )

    if len(local_refs) != int(getattr(profile, "store_count", -1)):
        raise ValueError(f"{side}_caller_local_store_census_mismatch")
    for key, evidence in evidence_by_key.items():
        expected = set(range(int(evidence.memory_effect_count)))
        if derived_indexes.get(key, set()) != expected:
            raise ValueError(f"{side}_caller_derived_store_census_mismatch")

    return {
        "side": side,
        "status": "complete",
        "profile_key": profile.stable_key(),
        "local_store_pcode_keys": tuple(sorted(local_refs, key=repr)),
        "call_pcode_keys": tuple(sorted(call_keys, key=repr)),
        "call_derived_effect_indexes": tuple(
            (key, tuple(sorted(indexes)))
            for key, indexes in sorted(derived_indexes.items(), key=lambda item: repr(item[0]))
        ),
        "effect_count": len(tuple(effects or ())),
    }


def _iter_expression_nodes(expr: Optional[Expression]):
    if not isinstance(expr, Expression):
        return
    yield expr
    for operand in tuple(getattr(expr, "operands", ()) or ()):
        yield from _iter_expression_nodes(operand)
    value = getattr(expr, "value", None)
    if isinstance(value, (tuple, list)):
        for item in value:
            if isinstance(item, (tuple, list)) and len(item) == 2:
                yield from _iter_expression_nodes(getattr(item[0], "expression", None))
                yield from _iter_expression_nodes(item[1])


def _render_call_result_value(
    value: Expression,
    mapping: Mapping[str, str],
    *,
    observed_bits: int,
    signed: Optional[bool],
) -> str:
    if not _pure_scalar_expression_supported(value):
        raise ValueError("caller_memory_call_return_expression_unsupported")
    value_bits = int(expression_smt_bit_width(value) or 0)
    if value_bits <= 0 or observed_bits <= 0:
        raise ValueError("caller_memory_call_return_width_missing")
    rendered = value.to_smt(symbol_name_mapping=mapping, float_mode="fp")
    if value_bits > observed_bits:
        return f"((_ extract {observed_bits - 1} 0) {rendered})"
    if value_bits < observed_bits:
        if signed is None:
            raise ValueError("caller_memory_call_return_signedness_missing")
        extension = "sign_extend" if signed else "zero_extend"
        return f"((_ {extension} {observed_bits - value_bits}) {rendered})"
    return rendered


def _caller_call_result_definitions(
    effects: Sequence[StoreEffect],
    call_effects: Sequence[CallSiteEffectSummaryEvidence],
    mapping: Mapping[str, str],
    *,
    side: str,
) -> Tuple[List[str], frozenset[Tuple[Any, ...]], Dict[str, Any]]:
    """Bind deferred call-result UNKNOWNs used by caller effects to typed summaries."""

    evidence_by_key: Dict[Tuple[Any, ...], CallSiteEffectSummaryEvidence] = {}
    for evidence in tuple(call_effects or ()):
        key = _evidence_pcode_key(evidence)
        if key is None or key in evidence_by_key:
            raise ValueError(f"{side}_caller_call_result_identity_incomplete")
        evidence_by_key[key] = evidence

    unknowns: Dict[str, Tuple[Expression, Tuple[Any, ...]]] = {}
    for effect in tuple(effects or ()):
        roots = [effect.value]
        roots.extend(
            getattr(condition, "expression", None)
            for condition in tuple(effect.conditions or ())
        )
        for root in roots:
            for node in _iter_expression_nodes(root):
                key = _deferred_call_pcode_key(node)
                if key is None:
                    continue
                symbol = node.to_smt(symbol_name_mapping=mapping, float_mode="fp")
                previous = unknowns.get(symbol)
                if previous is not None and previous[1] != key:
                    raise ValueError(f"{side}_caller_call_result_symbol_collision")
                unknowns[symbol] = (node, key)

    lines: List[str] = []
    bindings = []
    allowed = set()
    for symbol, (unknown, key) in sorted(unknowns.items()):
        evidence = evidence_by_key.get(key)
        if evidence is None:
            raise ValueError(f"{side}_caller_call_result_summary_missing")
        partitions = tuple(evidence.return_partitions or ())
        if (
            evidence.summary_status != "complete"
            or evidence.return_summary_status != "complete"
            or not partitions
            or evidence.has_unsupported_nested_call
        ):
            raise ValueError(f"{side}_caller_call_result_summary_incomplete")
        declarations = collect_unknown_smt_declarations(unknown)
        if len(declarations) != 1 or declarations[0][0] != symbol:
            raise ValueError(f"{side}_caller_call_result_declaration_incomplete")
        declared_symbol, observed_bits = declarations[0]
        lines.append(
            f"(declare-const {declared_symbol} (_ BitVec {int(observed_bits)}))"
        )
        guards = []
        for conditions, value in partitions:
            guard = _render_condition_group(conditions, mapping)
            rendered_value = _render_call_result_value(
                value,
                mapping,
                observed_bits=int(observed_bits),
                signed=evidence.return_signed,
            )
            lines.append(f"(assert (=> {guard} (= {symbol} {rendered_value})))")
            guards.append(guard)
        allowed.add(key)
        bindings.append(
            (
                key,
                symbol,
                int(observed_bits),
                tuple(guards),
                tuple(expression_provenance_key(value) for _conditions, value in partitions),
            )
        )
    return lines, frozenset(allowed), {
        "side": side,
        "status": "complete",
        "binding_count": len(bindings),
        "bindings": tuple(bindings),
        "proof_basis": "typed_call_site_return_partitions",
    }


def _render_caller_memory_stage(
    proof_input: PureDirectCallProofInput | PureCallRegionProofInput,
    dependency_ids: Tuple[str, ...],
) -> _RenderedStage:
    lines, left_mapping, right_mapping = _parameter_prelude(proof_input)
    left_coverage = _caller_effect_coverage_payload(
        proof_input.left_caller_effects,
        proof_input.left_caller_profile,
        proof_input.left_caller_call_effects,
        side="left",
    )
    right_coverage = _caller_effect_coverage_payload(
        proof_input.right_caller_effects,
        proof_input.right_caller_profile,
        proof_input.right_caller_call_effects,
        side="right",
    )
    left_definition_lines, left_call_keys, left_call_result_certificate = (
        _caller_call_result_definitions(
            proof_input.left_caller_effects,
            proof_input.left_caller_call_effects,
            left_mapping,
            side="left",
        )
    )
    right_definition_lines, right_call_keys, right_call_result_certificate = (
        _caller_call_result_definitions(
            proof_input.right_caller_effects,
            proof_input.right_caller_call_effects,
            right_mapping,
            side="right",
        )
    )
    lines.extend(left_definition_lines)
    lines.extend(right_definition_lines)
    violations, left_partial_order, right_partial_order = _render_final_post_state_relation(
        proof_input.left_caller_effects,
        proof_input.right_caller_effects,
        left_mapping,
        right_mapping,
        "true",
        "true",
        proof_input.left_caller_profile,
        proof_input.right_caller_profile,
        proof_input.left_caller_call_effects,
        proof_input.right_caller_call_effects,
        failure_prefix="caller_memory_effect",
        left_allowed_deferred_call_keys=left_call_keys,
        right_allowed_deferred_call_keys=right_call_keys,
    )
    violation = _or(tuple(violations))
    lines.extend((f"(assert {violation})", "(check-sat)"))
    return _RenderedStage(
        stage="caller_memory_relation",
        query_text="\n".join(lines),
        normalized_assertion_text=violation,
        stage_input_payload=_stage_payload(proof_input, "caller_memory_relation"),
        precondition_payload={
            "structural_certificate_id": proof_input.structural_certificate_id,
            "dependency_proof_ids": dependency_ids,
            "memory_observation_policy": "complete_alias_aware_final_post_state",
            "left_coverage_certificate": left_coverage,
            "right_coverage_certificate": right_coverage,
            "left_call_result_certificate": left_call_result_certificate,
            "right_call_result_certificate": right_call_result_certificate,
            "left_partial_order_certificate": left_partial_order,
            "right_partial_order_certificate": right_partial_order,
        },
        renderer_token=_TYPED_RENDERER_TOKEN,
    )


def _solver_version(solver_name: str) -> str:
    if solver_name.lower() == "z3":
        try:
            import z3

            return str(z3.get_version_string())
        except Exception:
            pass
    return "runtime-version-unavailable"


def _execute_rendered_stage(
    rendered: _RenderedStage,
    proof_input: PureDirectCallProofInput | PureCallRegionProofInput,
    solver_runner: Any,
    timeout_seconds: int,
    dependency_ids: Tuple[str, ...],
    v2_execution_context: Optional[V2CallEffectExecutionContext] = None,
) -> InternalSolverProofArtifact:
    if rendered.renderer_token is not _TYPED_RENDERER_TOKEN:
        raise ValueError("untrusted_typed_stage_renderer")
    if rendered.stage not in _STAGES:
        raise ValueError("unsupported_typed_proof_stage")
    if rendered.stage_input_payload.get("stage") != rendered.stage:
        raise ValueError("typed_stage_payload_mismatch")
    expected_dependencies = tuple(
        rendered.precondition_payload.get("dependency_proof_ids", ()) or ()
    )
    if expected_dependencies != dependency_ids:
        raise ValueError("typed_stage_dependency_mismatch")
    query_authority = _issue_solver_query_authority(rendered, proof_input)
    v2_execution_receipt = None
    v2_execution_receipts = ()
    v2_membership = None
    if v2_execution_context is not None:
        from .v2.execution_authority import PINNED_SOLVER_EXECUTION_ISSUER

        v2_membership = v2_execution_context.membership_for(query_authority)
        receipts = PINNED_SOLVER_EXECUTION_ISSUER.execute(
            registry=v2_execution_context.producer_stage_registry,
            result_occurrence_id=v2_execution_context.result_occurrence_id,
            membership=v2_membership,
            invocation_identity=(
                f"{proof_input.obligation_id}:{rendered.stage}:"
                f"{v2_membership.attempt_ordinal}"
            ),
            first_invocation_ordinal=1,
            query=rendered.query_text,
            configured_timeout_ms=max(1, int(timeout_seconds)) * 1000,
            query_authority=query_authority,
            lifecycle_projection=v2_execution_context.lifecycle_projection,
        )
        v2_execution_receipts = tuple(receipts)
        v2_execution_receipt = next(
            (item for item in receipts if item.observed_status in {"sat", "unsat"}),
            receipts[0],
        )
        status_name = v2_execution_receipt.observed_status
        solver_name = v2_execution_receipt.solver_identity
    else:
        parallel_result = solver_runner.run_parallel(
            rendered.query_text,
            timeout=max(1, int(timeout_seconds)),
        )
        result = getattr(parallel_result, "first_definitive", None)
        if result is None:
            results = tuple(getattr(parallel_result, "results", ()) or ())
            result = results[0] if results else None
        status_name = (
            str(getattr(getattr(result, "status", None), "name", "UNKNOWN")).lower()
            if result is not None
            else "unknown"
        )
        solver_name = str(getattr(result, "solver_name", "unavailable") or "unavailable")
    if status_name == "unsat":
        record_status = "proven"
        solver_result = "unsat"
    elif status_name == "sat":
        record_status = "refuted"
        solver_result = "sat"
    else:
        record_status = "inconclusive"
        solver_result = status_name
    query_digest = hashlib.sha256(rendered.query_text.encode("utf-8")).hexdigest()
    assertion_digest = hashlib.sha256(
        rendered.normalized_assertion_text.encode("utf-8")
    ).hexdigest()
    stage_input_digest = _digest(rendered.stage_input_payload)
    precondition_digest = _digest(rendered.precondition_payload)
    timeout_ms = max(1, int(timeout_seconds)) * 1000
    proof_id = _digest(
        (
            "solver_proof_record",
            rendered.stage,
            proof_input.obligation_id,
            proof_input.left_fact_id,
            proof_input.right_fact_id,
            proof_input.observation_contract_id,
            query_digest,
            assertion_digest,
            stage_input_digest,
            precondition_digest,
            dependency_ids,
            solver_name,
            _solver_version(solver_name),
            solver_result,
            timeout_ms,
            _PRODUCER_KIND,
        )
    )
    record = SolverProofRecord(
        proof_id=proof_id,
        obligation_id=proof_input.obligation_id,
        proof_stage=rendered.stage,
        observation_contract_id=proof_input.observation_contract_id,
        left_object_id=proof_input.left_fact_id,
        right_object_id=proof_input.right_fact_id,
        status=record_status,
        failure_cause=None if record_status == "proven" else f"solver_{solver_result}",
        normalized_assertion_digest=assertion_digest,
        query_digest=query_digest,
        stage_input_digest=stage_input_digest,
        precondition_digest=precondition_digest,
        solver_name=solver_name,
        solver_version=_solver_version(solver_name),
        solver_result=solver_result,
        dependency_proof_ids=dependency_ids,
        timeout_ms=timeout_ms,
        producer_kind=_PRODUCER_KIND,
    )
    return InternalSolverProofArtifact(
        record=record,
        query_text=rendered.query_text,
        normalized_assertion_text=rendered.normalized_assertion_text,
        stage_input_payload=rendered.stage_input_payload,
        precondition_payload=rendered.precondition_payload,
        query_authority=query_authority,
        v2_execution_receipt=v2_execution_receipt,
        v2_execution_receipts=v2_execution_receipts,
        v2_producer_membership=v2_membership,
        producer_kind=_PRODUCER_KIND,
        producer_token=_INTERNAL_SOLVER_PRODUCER_TOKEN,
    )


def produce_pure_direct_call_proofs(
    manifest: Mapping[str, Any],
    analysis1: FunctionReturnAnalysis,
    analysis2: FunctionReturnAnalysis,
    *,
    solver_runner: Any,
    timeout_seconds: int,
    v2_execution_context: Optional[V2CallEffectExecutionContext] = None,
) -> PureDirectCallProofProduction:
    """Produce fixed semantic stages for eligible pure call relations."""

    proof_inputs, failures = _build_inputs(manifest, analysis1, analysis2)
    from .v2.production_signals import (
        CallEffectBlockerProductionSignal,
        CallEffectPrerequisiteProductionSignal,
        emit_call_effect_signal,
    )
    blocker_signals = tuple(
        CallEffectBlockerProductionSignal.from_proof_input(proof_input)
        for proof_input in proof_inputs
    )
    prerequisite_signals = tuple(
        CallEffectPrerequisiteProductionSignal(
            obligation_id=str(obligation.get("obligation_id") or ""),
            observation_contract_id=str(
                obligation.get("observation_contract_id") or ""
            ),
            left_fact_id=obligation.get("left_fact_id"),
            right_fact_id=obligation.get("right_fact_id"),
            structural_certificate_id=str(
                (manifest.get("structural_coverage_certificate") or {}).get(
                    "certificate_id"
                )
                or ""
            ),
            eligibility_blockers=tuple(eligibility.get("blockers", ()) or ()),
        )
        for obligation in manifest.get("relational_obligations", ()) or ()
        if isinstance(obligation, Mapping)
        for eligibility in (
            next((
                item
                for item in manifest.get("phase2_direct_call_eligibility", ()) or ()
                if isinstance(item, Mapping)
                and item.get("obligation_id") == obligation.get("obligation_id")
            ), {}),
        )
        if eligibility.get("status") == "ineligible"
        and tuple(eligibility.get("blockers", ()) or ())
        == ("phase2_requires_paired_call_sites",)
    )
    for signal in prerequisite_signals:
        emit_call_effect_signal(
            signal,
            producer_site_manifest_id="call-effect-producer-prerequisite",
        )
    for signal in blocker_signals:
        emit_call_effect_signal(
            signal,
            producer_site_manifest_id="call-effect-producer-blocker",
        )
    artifacts: List[InternalSolverProofArtifact] = []
    failure_list = list(failures)
    for proof_input in proof_inputs:
        dependencies: Tuple[str, ...] = ()
        try:
            if isinstance(proof_input, PureCallRegionProofInput):
                first_rendered = _render_call_region_guard_stage(proof_input)
            else:
                first_rendered = _render_guard_stage(proof_input)
            first = _execute_rendered_stage(
                first_rendered,
                proof_input,
                solver_runner,
                timeout_seconds,
                dependencies,
                v2_execution_context,
            )
            artifacts.append(first)
            if first.record.status != "proven":
                failure_list.append(
                    f"{proof_input.obligation_id}:guard_relation_{first.record.solver_result}"
                )
                continue
            dependencies = (first.record.proof_id,)

            if isinstance(proof_input, PureCallRegionProofInput):
                second_rendered = _render_call_region_argument_stage(
                    proof_input, dependencies
                )
            else:
                second_rendered = _render_argument_stage(proof_input, dependencies)
            second = _execute_rendered_stage(
                second_rendered,
                proof_input,
                solver_runner,
                timeout_seconds,
                dependencies,
                v2_execution_context,
            )
            artifacts.append(second)
            if second.record.status != "proven":
                failure_list.append(
                    f"{proof_input.obligation_id}:argument_relation_{second.record.solver_result}"
                )
                continue
            dependencies = (second.record.proof_id,)

            if isinstance(proof_input, PureCallRegionProofInput):
                third_rendered = _render_call_region_return_stage(
                    proof_input, dependencies
                )
            else:
                third_rendered = _render_return_stage(proof_input, dependencies)
            third = _execute_rendered_stage(
                third_rendered,
                proof_input,
                solver_runner,
                timeout_seconds,
                dependencies,
                v2_execution_context,
            )
            artifacts.append(third)
            if third.record.status != "proven":
                failure_list.append(
                    f"{proof_input.obligation_id}:return_relation_{third.record.solver_result}"
                )
                continue
            dependencies = (third.record.proof_id,)
            memory_stage_required = (
                bool(proof_input.region_effects or proof_input.call_effect.memory_effects)
                if isinstance(proof_input, PureCallRegionProofInput)
                else bool(
                    proof_input.left_effect.memory_effects
                    or proof_input.right_effect.memory_effects
                )
            )
            if memory_stage_required:
                fourth_rendered = (
                    _render_call_region_memory_stage(proof_input, dependencies)
                    if isinstance(proof_input, PureCallRegionProofInput)
                    else _render_memory_stage(proof_input, dependencies)
                )
                fourth = _execute_rendered_stage(
                    fourth_rendered,
                    proof_input,
                    solver_runner,
                    timeout_seconds,
                    dependencies,
                    v2_execution_context,
                )
                artifacts.append(fourth)
                if fourth.record.status != "proven":
                    failure_list.append(
                        f"{proof_input.obligation_id}:memory_relation_{fourth.record.solver_result}"
                    )
                    continue
                dependencies = (fourth.record.proof_id,)
            caller_memory_stage_required = bool(
                proof_input.left_caller_effects
                or proof_input.right_caller_effects
                or int(getattr(proof_input.left_caller_profile, "store_count", 0) or 0)
                or int(getattr(proof_input.right_caller_profile, "store_count", 0) or 0)
                or any(
                    int(getattr(evidence, "memory_effect_count", 0) or 0) > 0
                    for evidence in (
                        *proof_input.left_caller_call_effects,
                        *proof_input.right_caller_call_effects,
                    )
                )
            )
            if caller_memory_stage_required:
                caller_memory_rendered = _render_caller_memory_stage(
                    proof_input,
                    dependencies,
                )
                caller_memory = _execute_rendered_stage(
                    caller_memory_rendered,
                    proof_input,
                    solver_runner,
                    timeout_seconds,
                    dependencies,
                    v2_execution_context,
                )
                artifacts.append(caller_memory)
                if caller_memory.record.status != "proven":
                    failure_list.append(
                        f"{proof_input.obligation_id}:caller_memory_relation_"
                        f"{caller_memory.record.solver_result}"
                    )
        except (TypeError, ValueError) as exc:
            failure_list.append(f"{proof_input.obligation_id}:{exc}")
    return PureDirectCallProofProduction(
        artifacts=tuple(artifacts),
        failure_causes=tuple(failure_list),
        v2_blocker_signals=blocker_signals,
        v2_prerequisite_signals=prerequisite_signals,
    )


def produce_v2_pure_direct_call_proofs(
    manifest: Mapping[str, Any],
    analysis1: FunctionReturnAnalysis,
    analysis2: FunctionReturnAnalysis,
    *,
    execution_context: V2CallEffectExecutionContext,
    timeout_seconds: int,
) -> PureDirectCallProofProduction:
    """V2 authority path; solver execution is owned only by the pinned issuer."""

    return produce_pure_direct_call_proofs(
        manifest,
        analysis1,
        analysis2,
        solver_runner=None,
        timeout_seconds=timeout_seconds,
        v2_execution_context=execution_context,
    )


__all__ = [
    "PureDirectCallProofProduction",
    "V2CallEffectExecutionContext",
    "produce_pure_direct_call_proofs",
    "produce_v2_pure_direct_call_proofs",
]

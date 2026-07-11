"""Stateless method implementations extracted from ``scripts.function_tracer_pcode.equivalence.strategies.pairwise``."""

from __future__ import annotations

from typing import Any
from ._shared import (
    ExpressionType,
    UnknownRecoveryActionStatus,
    UnknownRecoveryProofKind,
    UnknownRecoveryProofObligation,
    _UnresolvedDeferredCallLowering,
    expression_contains_unsupported_smt_ops,
    expression_smt_bit_width,
    json,
)

def invoke(_service_name: str, *args: Any, **kwargs: Any) -> Any:
    implementation_function = globals().get(f"_impl_{_service_name}")
    if implementation_function is None:
        raise AttributeError(_service_name)
    return implementation_function(*args, **kwargs)


def implementation(_service_name: str):
    return globals().get(f"_impl_{_service_name}")

def _impl__unresolved_expression_object_target_key(
    self,
    *,
    base_ctx: Dict[str, Any],
    case1: ReturnCase,
    case2: ReturnCase,
    pair_id: str,
) -> Tuple[Any, ...]:
    """Object-derived target key for unresolved-expression diagnostics."""

    target: List[Any] = [
        "unresolved_expression",
        ("pair", pair_id),
        self._unresolved_expression_side_object_key(
            "left",
            base_ctx.get("analysis1"),
            case1,
        ),
        self._unresolved_expression_side_object_key(
            "right",
            base_ctx.get("analysis2"),
            case2,
        ),
    ]
    lowering_diagnostic = self._unresolved_expression_pair_lowering_diagnostic(
        case1,
        case2,
    )
    if lowering_diagnostic is not None:
        target.append(lowering_diagnostic)
    return tuple(target)

def _impl__unresolved_expression_side_object_key(
    self,
    side_label: str,
    analysis: Optional[FunctionReturnAnalysis],
    case: ReturnCase,
) -> Tuple[Any, ...]:
    target = (
        "unresolved_expression_side",
        side_label,
        self._analysis_entry_key(analysis) if analysis is not None else None,
        self._return_storage_object_key(analysis) if analysis is not None else None,
        self._return_case_partition_member_object_key(
            case,
            getattr(case, "return_info", None),
        ),
        (
            "unresolved_locations",
            tuple(self._unresolved_expression_locations(case)),
        ),
    )
    if analysis is not None:
        return self._artifact_stable_key_for_analysis(target, analysis)
    return target

def _impl__unresolved_expression_locations(self, case: ReturnCase) -> Tuple[Any, ...]:
    locations: List[Tuple[Any, ...]] = []
    value_expr = getattr(case, "value_expr", None)
    if self._expression_contains_unresolved(value_expr):
        locations.append(
            (
                "unresolved_location",
                "return_value",
                self._unresolved_expression_location_classification(
                    value_expr,
                    "return_value",
                ),
                self._expression_runtime_object_key(value_expr),
                self._unresolved_expression_typed_lowering_evidence(
                    value_expr,
                    "return_value",
                    case_value_expr=value_expr,
                ),
            )
        )
    case_value_expr = getattr(case, "value_expr", None)
    for index, condition in enumerate(getattr(case, "conditions", None) or ()):
        expression = getattr(condition, "expression", None)
        if not self._expression_contains_unresolved(expression):
            continue
        locations.append(
            (
                "unresolved_location",
                "guard_condition",
                int(index),
                bool(getattr(condition, "negated", False)),
                self._unresolved_expression_location_classification(
                    expression,
                    "guard_condition",
                ),
                self._return_condition_object_key(condition),
                self._unresolved_expression_typed_lowering_evidence(
                    expression,
                    "guard_condition",
                    condition=condition,
                    case_value_expr=case_value_expr,
                ),
            )
        )
    return tuple(locations)

def _impl__unresolved_expression_typed_lowering_evidence(
    self,
    expr: Any,
    location_scope: str,
    *,
    condition: Any = None,
    case_value_expr: Any = None,
) -> Tuple[Any, ...]:
    expr_type = getattr(expr, "expr_type", None)
    expr_kind = getattr(expr_type, "name", None)
    try:
        bits = int(expression_smt_bit_width(expr) or 0)
    except (AttributeError, TypeError, ValueError, RecursionError):
        bits = 0
    if bits <= 0:
        try:
            bits = int(getattr(expr, "get_bit_width", lambda: 0)() or 0)
        except (AttributeError, TypeError, ValueError, RecursionError):
            bits = 0
    unsupported = bool(expression_contains_unsupported_smt_ops(expr))
    if expr_type == ExpressionType.UNKNOWN:
        status = "blocked_unknown_expression"
    elif unsupported:
        status = "blocked_unsupported_smt_op"
    else:
        status = "blocked_nested_unresolved_expression"
    evidence: List[Any] = [
        "typed_lowering_evidence",
        ("location_scope", str(location_scope)),
        ("expression_kind", str(expr_kind or "missing")),
        ("expression_bits", bits if bits > 0 else None),
        ("typed_expression_key", self._expression_runtime_object_key(expr)),
        ("contains_unsupported_smt_ops", unsupported),
        ("lowering_status", status),
    ]
    phi_evidence = self._phi_circular_typed_lowering_evidence(
        expr,
        location_scope,
        condition=condition,
        case_value_expr=case_value_expr,
    )
    if phi_evidence is not None:
        evidence.append(phi_evidence)
    return tuple(evidence)

def _impl__phi_circular_typed_lowering_evidence(
    self,
    expr: Any,
    location_scope: str,
    *,
    condition: Any = None,
    case_value_expr: Any = None,
) -> Optional[Tuple[Any, ...]]:
    phi_origins = self._collect_phi_circular_origin_details(expr)
    if not phi_origins:
        return None
    guard_condition_key = (
        self._return_condition_object_key(condition)
        if condition is not None
        else None
    )
    summary_parameter_refs = self._collect_summary_parameter_refs(
        expr,
        case_value_expr,
    )
    return (
        "phi_circular_evidence",
        ("location_scope", str(location_scope)),
        ("phi_origins", phi_origins),
        ("guard_condition_key", guard_condition_key),
        (
            "guard_condition_literals",
            self._phi_circular_condition_literals(condition)
            if condition is not None
            else (),
        ),
        ("summary_parameter_refs", summary_parameter_refs),
        ("relation_status", "pending_guard_summary_relation_proof"),
    )

def _impl__unresolved_expression_pair_lowering_diagnostic(
    self,
    case1: ReturnCase,
    case2: ReturnCase,
) -> Optional[Tuple[Any, ...]]:
    left_shape, left_unknowns = self._phi_circular_case_shape_and_unknowns(case1)
    right_shape, right_unknowns = self._phi_circular_case_shape_and_unknowns(case2)
    if left_shape is None and right_shape is None:
        return None
    if not left_unknowns and not right_unknowns:
        return None

    left_value = self._phi_circular_case_value_shape(left_shape)
    right_value = self._phi_circular_case_value_shape(right_shape)
    left_literals = self._phi_circular_case_condition_literals(case1)
    right_literals = self._phi_circular_case_condition_literals(case2)
    left_unknown_count = len(left_unknowns)
    right_unknown_count = len(right_unknowns)
    origin_shape_relation = self._phi_circular_origin_shape_relation(
        left_unknowns,
        right_unknowns,
    )
    contradictions = self._phi_circular_opposing_condition_literals(
        left_literals,
        right_literals,
    )
    if left_shape is not None and right_shape is not None and left_shape == right_shape:
        status = "full_shape_match"
    elif left_value is not None and right_value is not None and left_value != right_value:
        status = "value_shape_mismatch"
    elif contradictions:
        status = "guard_literal_conflict"
    elif left_shape is None or right_shape is None:
        status = "shape_unavailable"
    else:
        status = "condition_shape_mismatch"

    return (
        "pair_lowering_diagnostic",
        ("candidate_kind", "phi_circular_guard_summary_relation"),
        ("status", status),
        ("left_unknown_count", left_unknown_count),
        ("right_unknown_count", right_unknown_count),
        (
            "unknown_count_relation",
            self._phi_circular_unknown_count_relation(
                left_unknown_count,
                right_unknown_count,
            ),
        ),
        ("left_value_shape", left_value),
        ("right_value_shape", right_value),
        (
            "value_shape_relation",
            self._phi_circular_value_shape_relation(left_value, right_value),
        ),
        ("phi_origin_shape_relation", origin_shape_relation),
        ("left_guard_literals", left_literals),
        ("right_guard_literals", right_literals),
        ("opposing_guard_literals", contradictions),
        ("required_evidence", ("guard_condition_pair", "summary_parameter_binding")),
    )

def _impl__unresolved_expression_phi_circular_full_shape_diagnostic_evidence(
    self,
    object_target_key: Tuple[Any, ...],
) -> Optional[Tuple[Any, ...]]:
    diagnostic = self._find_pair_lowering_diagnostic(object_target_key)
    if diagnostic is None:
        return None
    fields = {
        item[0]: item[1]
        for item in diagnostic[1:]
        if isinstance(item, tuple) and len(item) == 2 and isinstance(item[0], str)
    }
    if fields.get("candidate_kind") != "phi_circular_guard_summary_relation":
        return None
    if fields.get("status") != "full_shape_match":
        return None
    if int(fields.get("left_unknown_count") or 0) <= 0:
        return None
    if int(fields.get("right_unknown_count") or 0) <= 0:
        return None
    if int(fields.get("left_unknown_count") or 0) != int(fields.get("right_unknown_count") or 0):
        return None
    if fields.get("left_value_shape") != fields.get("right_value_shape"):
        return None
    origin_relation = fields.get("phi_origin_shape_relation")
    if not (
        isinstance(origin_relation, tuple)
        and ("relation", "exact_match") in origin_relation
    ):
        return None
    if fields.get("left_guard_literals") != fields.get("right_guard_literals"):
        return None
    if fields.get("opposing_guard_literals"):
        return None
    stage_evidence = self._phi_circular_semantic_recurrence_stage_evidence(
        object_target_key=object_target_key,
        diagnostic=diagnostic,
        diagnostic_fields=fields,
    )
    if not stage_evidence:
        return None
    return (
        "unresolved_expression_diagnostic_evidence",
        ("object_derived", True),
        ("status", "object_evidence_collected"),
        ("diagnostic_rule", "phi_circular_full_shape_match"),
        (
            "pending_stages",
            (
                "phi_circular_guard_condition_lowering",
                "recursive_summary_guard_equivalence",
            ),
        ),
        (
            "required_semantic_proof",
            (
                "phi_incoming_values",
                "guard_transition_relation",
                "recursive_summary_parameter_binding",
                "loop_summary_recurrence_semantics",
            ),
        ),
        ("object_target_key", object_target_key),
        ("pair_lowering_diagnostic", diagnostic),
        ("stage_evidence", stage_evidence),
    )

def _impl__unresolved_expression_deferred_call_diagnostic_evidence(
    self,
    object_target_key: Tuple[Any, ...],
) -> Optional[Tuple[Any, ...]]:
    if not self._object_target_contains_deferred_call_unknown(object_target_key):
        return None
    call_evidence = self._deferred_call_object_evidence_from_target(object_target_key)
    if call_evidence is None:
        return None
    stage_evidence = self._deferred_call_unresolved_expression_stage_evidence(
        object_target_key=object_target_key,
        call_evidence=call_evidence,
    )
    if not stage_evidence:
        return None
    return (
        "unresolved_expression_diagnostic_evidence",
        ("object_derived", True),
        ("status", "object_evidence_collected"),
        ("diagnostic_rule", "deferred_call_object_proof_content"),
        (
            "pending_stages",
            (
                "deferred_call_return_resolution",
                "deferred_call_result_equivalence",
            ),
        ),
        (
            "required_semantic_proof",
            (
                "deferred_call_site",
                "callee_identity",
                "call_effect_summary",
                "argument_binding",
                "return_width_policy",
            ),
        ),
        ("object_target_key", object_target_key),
        ("deferred_call_evidence", call_evidence),
        ("stage_evidence", stage_evidence),
    )

def _impl__unresolved_expression_opaque_unknown_diagnostic_evidence(
    self,
    object_target_key: Tuple[Any, ...],
) -> Optional[Tuple[Any, ...]]:
    if not self._object_target_contains_void_opaque_unknown(object_target_key):
        return None
    opaque_evidence = self._opaque_unknown_return_object_evidence_from_target(
        object_target_key
    )
    if opaque_evidence is None:
        return None
    stage_evidence = self._opaque_unknown_unresolved_expression_stage_evidence(
        object_target_key=object_target_key,
        opaque_evidence=opaque_evidence,
    )
    if not stage_evidence:
        return None
    return (
        "unresolved_expression_diagnostic_evidence",
        ("object_derived", True),
        ("status", "object_evidence_collected"),
        ("diagnostic_rule", "opaque_unknown_return_object_proof_content"),
        (
            "pending_stages",
            (
                "opaque_unknown_return_origin_resolution",
                "opaque_unknown_return_value_equivalence",
            ),
        ),
        (
            "required_semantic_proof",
            (
                "opaque_unknown_ref",
                "return_case_origin",
                "guard_condition_pair",
                "return_width_policy",
            ),
        ),
        ("object_target_key", object_target_key),
        ("opaque_unknown_evidence", opaque_evidence),
        ("stage_evidence", stage_evidence),
    )

def _impl__unresolved_expression_generic_diagnostic_evidence(
    self,
    object_target_key: Tuple[Any, ...],
) -> Optional[Tuple[Any, ...]]:
    cause = self._unresolved_expression_target_cause(object_target_key)
    if cause not in {
        "mixed_float_call_read_recurrence",
        "multiple_or_nested_unresolved",
        "readonly_memory_read",
        "opaque_unknown",
    }:
        return None
    stage_evidence = self._generic_unresolved_expression_stage_evidence(
        object_target_key=object_target_key,
        cause=cause,
    )
    return (
        "unresolved_expression_diagnostic_evidence",
        ("object_derived", True),
        ("status", "object_evidence_collected"),
        ("diagnostic_rule", f"{cause}_pending_census"),
        ("unresolved_cause", cause),
        ("pending_stages", ("typed_expression_lowering", "type_normalization")),
        (
            "required_semantic_proof",
            (
                "typed_expression_key",
                "normalization_policy",
                "return_width_policy",
            ),
        ),
        ("object_target_key", object_target_key),
        ("stage_evidence", stage_evidence),
    )

def _impl__unresolved_expression_target_uses_generic_pending_census(
    cls,
    object_target_key: Any,
) -> bool:
    return cls._unresolved_expression_target_cause(object_target_key) in {
        "mixed_float_call_read_recurrence",
        "multiple_or_nested_unresolved",
        "readonly_memory_read",
    }

def _impl__generic_unresolved_expression_stage_evidence(
    self,
    *,
    object_target_key: Tuple[Any, ...],
    cause: str,
) -> Tuple[Any, ...]:
    return (
        (
            "unresolved_expression_stage_evidence",
            ("proof_stage", "typed_expression_lowering"),
            ("status", "object_evidence_collected"),
            ("object_target_key", object_target_key),
            ("unresolved_cause", cause),
            ("semantic_proof_status", "pending_semantic_proof"),
            ("completed_proof_allowed", False),
            (
                "required_semantic_proof",
                (
                    "typed_expression_key",
                    "unresolved_location",
                    "unresolved_cause",
                ),
            ),
        ),
        (
            "unresolved_expression_stage_evidence",
            ("proof_stage", "type_normalization"),
            ("status", "object_evidence_collected"),
            ("object_target_key", object_target_key),
            ("unresolved_cause", cause),
            ("semantic_proof_status", "pending_semantic_proof"),
            ("completed_proof_allowed", False),
            (
                "required_semantic_proof",
                (
                    "normalization_policy",
                    "return_width_policy",
                ),
            ),
        ),
    )

def _impl__opaque_unknown_unresolved_expression_stage_evidence(
    self,
    *,
    object_target_key: Tuple[Any, ...],
    opaque_evidence: Tuple[Any, ...],
) -> Tuple[Any, ...]:
    origin_query = self._semantic_recurrence_query_plan(
        query_id="opaque_unknown_return_origin_resolution",
        query_stage="opaque_unknown_return_origin_resolution",
        assertion_kind="opaque_unknown_return_origin_resolution",
        object_target_key=object_target_key,
        object_content=(("opaque_unknown_evidence", opaque_evidence),),
    )
    value_query = self._semantic_recurrence_query_plan(
        query_id="opaque_unknown_return_value_equivalence",
        query_stage="opaque_unknown_return_value_equivalence",
        assertion_kind="opaque_unknown_return_value_equivalence",
        object_target_key=object_target_key,
        object_content=(("opaque_unknown_evidence", opaque_evidence),),
    )
    return (
        (
            "unresolved_expression_stage_evidence",
            ("proof_stage", "opaque_unknown_return_origin_resolution"),
            ("status", "object_evidence_collected"),
            ("object_target_key", object_target_key),
            ("opaque_unknown_evidence", opaque_evidence),
            ("origin_resolution_status", "pending_semantic_proof"),
            ("proof_query_plan", (origin_query,)),
            (
                "required_semantic_proof",
                (
                    "opaque_unknown_ref",
                    "return_case_origin",
                ),
            ),
        ),
        (
            "unresolved_expression_stage_evidence",
            ("proof_stage", "opaque_unknown_return_value_equivalence"),
            ("status", "object_evidence_collected"),
            ("object_target_key", object_target_key),
            ("opaque_unknown_evidence", opaque_evidence),
            ("value_equivalence_status", "pending_semantic_proof"),
            ("proof_query_plan", (value_query,)),
            (
                "required_semantic_proof",
                (
                    "left_return_value",
                    "right_return_value",
                    "guard_condition_pair",
                    "return_width_policy",
                ),
            ),
        ),
    )

def _impl__deferred_call_unresolved_expression_stage_evidence(
    self,
    *,
    object_target_key: Tuple[Any, ...],
    call_evidence: Tuple[Any, ...],
) -> Tuple[Any, ...]:
    resolution_query = self._semantic_recurrence_query_plan(
        query_id="deferred_call_return_resolution",
        query_stage="deferred_call_return_resolution",
        assertion_kind="deferred_call_return_resolution",
        object_target_key=object_target_key,
        object_content=(("deferred_call_evidence", call_evidence),),
    )
    result_query = self._semantic_recurrence_query_plan(
        query_id="deferred_call_result_equivalence",
        query_stage="deferred_call_result_equivalence",
        assertion_kind="deferred_call_result_equivalence",
        object_target_key=object_target_key,
        object_content=(("deferred_call_evidence", call_evidence),),
    )
    return (
        (
            "unresolved_expression_stage_evidence",
            ("proof_stage", "deferred_call_return_resolution"),
            ("status", "object_evidence_collected"),
            ("object_target_key", object_target_key),
            ("deferred_call_evidence", call_evidence),
            ("call_resolution_status", "pending_semantic_proof"),
            ("proof_query_plan", (resolution_query,)),
            (
                "required_semantic_proof",
                (
                    "deferred_call_site",
                    "callee_identity",
                    "call_effect_summary",
                ),
            ),
        ),
        (
            "unresolved_expression_stage_evidence",
            ("proof_stage", "deferred_call_result_equivalence"),
            ("status", "object_evidence_collected"),
            ("object_target_key", object_target_key),
            ("deferred_call_evidence", call_evidence),
            ("result_equivalence_status", "pending_semantic_proof"),
            ("proof_query_plan", (result_query,)),
            (
                "required_semantic_proof",
                (
                    "left_return_value",
                    "right_return_value",
                    "argument_binding",
                    "return_width_policy",
                ),
            ),
        ),
    )

def _impl__deferred_call_object_evidence_from_target(
    self,
    object_target_key: Tuple[Any, ...],
) -> Optional[Tuple[Any, ...]]:
    target = self._normalize_nested_tuple(object_target_key)
    if not isinstance(target, tuple) or len(target) < 4:
        return None
    left_refs = self._deferred_call_runtime_refs_from_value(target[2])
    right_refs = self._deferred_call_runtime_refs_from_value(target[3])
    if not left_refs and not right_refs:
        return None
    left_semantic_refs = self._deferred_call_semantic_refs(left_refs)
    right_semantic_refs = self._deferred_call_semantic_refs(right_refs)
    return (
        "deferred_call_object_evidence",
        ("left_deferred_call_refs", left_refs),
        ("right_deferred_call_refs", right_refs),
        ("left_deferred_call_semantic_refs", left_semantic_refs),
        ("right_deferred_call_semantic_refs", right_semantic_refs),
        (
            "deferred_call_ref_relation",
            self._deferred_call_ref_relation(left_refs, right_refs),
        ),
        (
            "deferred_call_semantic_ref_relation",
            self._deferred_call_ref_relation(left_semantic_refs, right_semantic_refs),
        ),
        ("evidence_status", "object_evidence_collected"),
    )

def _impl__deferred_call_runtime_refs_from_value(cls, value: Any) -> Tuple[Any, ...]:
    refs: List[Any] = []
    seen = set()

    def visit(node: Any) -> None:
        normalized = cls._normalize_nested_tuple(node)
        if isinstance(normalized, tuple):
            if (
                len(normalized) == 2
                and normalized[0] in {"unknown_runtime_ref", "runtime_ref"}
                and isinstance(normalized[1], tuple)
                and normalized[1]
                and normalized[1][0] == "deferred_call"
            ):
                key = json.dumps(cls._semantic_recurrence_jsonable(normalized), sort_keys=True)
                if key not in seen:
                    seen.add(key)
                    refs.append(normalized)
                return
            for item in normalized:
                visit(item)
        elif isinstance(normalized, list):
            for item in normalized:
                visit(item)
        elif isinstance(normalized, dict):
            for key, item in sorted(normalized.items(), key=lambda item: str(item[0])):
                visit(key)
                visit(item)

    visit(value)
    return tuple(refs)

def _impl__deferred_call_semantic_refs(cls, refs: Tuple[Any, ...]) -> Tuple[Any, ...]:
    grouped: Dict[str, Dict[str, Any]] = {}
    for ref in refs:
        normalized = cls._normalize_nested_tuple(ref)
        if (
            not isinstance(normalized, tuple)
            or len(normalized) != 2
            or normalized[0] not in {"unknown_runtime_ref", "runtime_ref"}
            or not isinstance(normalized[1], tuple)
            or not normalized[1]
            or normalized[1][0] != "deferred_call"
        ):
            continue
        payload = normalized[1]
        key = json.dumps(cls._semantic_recurrence_jsonable(payload), sort_keys=True)
        entry = grouped.setdefault(
            key,
            {
                "payload": payload,
                "forms": set(),
            },
        )
        entry["forms"].add(normalized[0])
    semantic_refs = []
    for key in sorted(grouped):
        entry = grouped[key]
        semantic_refs.append(
            (
                "deferred_call_semantic_ref",
                ("deferred_call_payload", entry["payload"]),
                ("ref_forms", tuple(sorted(entry["forms"]))),
            )
        )
    return tuple(semantic_refs)

def _impl__deferred_call_ref_relation(
    left_refs: Tuple[Any, ...],
    right_refs: Tuple[Any, ...],
) -> Tuple[Any, ...]:
    if left_refs and right_refs:
        relation = "both_sides_deferred_call_unknown"
    elif left_refs:
        relation = "left_deferred_call_unknown_only"
    else:
        relation = "right_deferred_call_unknown_only"
    return (
        "deferred_call_ref_relation",
        ("relation", relation),
        ("left_count", len(left_refs)),
        ("right_count", len(right_refs)),
    )

def _impl__find_pair_lowering_diagnostic(cls, value: Any) -> Optional[Tuple[Any, ...]]:
    normalized = cls._normalize_nested_tuple(value)
    if isinstance(normalized, tuple):
        if normalized and normalized[0] == "pair_lowering_diagnostic":
            return normalized
        for item in normalized:
            found = cls._find_pair_lowering_diagnostic(item)
            if found is not None:
                return found
    if isinstance(normalized, list):
        for item in normalized:
            found = cls._find_pair_lowering_diagnostic(item)
            if found is not None:
                return found
    if isinstance(normalized, dict):
        for item in normalized.values():
            found = cls._find_pair_lowering_diagnostic(item)
            if found is not None:
                return found
    return None

def _impl__unresolved_expression_location_classification(
    self,
    expr: Any,
    location_scope: str,
) -> Tuple[Any, ...]:
    kinds: set[Any] = set()
    unknown_refs: set[Any] = set()
    unsupported_ops: set[Any] = set()
    self._collect_unresolved_expression_classification(
        expr,
        kinds=kinds,
        unknown_refs=unknown_refs,
        unsupported_ops=unsupported_ops,
    )
    location = self._unresolved_expression_location_taxonomy(location_scope)
    cause = self._unresolved_expression_cause_taxonomy(
        expr,
        unresolved_kinds=kinds,
        unknown_refs=unknown_refs,
        unsupported_ops=unsupported_ops,
    )
    return (
        "unresolved_classification",
        ("location_scope", str(location_scope)),
        ("unresolved_location", location),
        ("unresolved_cause", cause),
        ("unresolved_substage", self._unresolved_expression_substage(location, cause)),
        ("unresolved_kinds", tuple(sorted(kinds, key=repr))),
        ("unknown_refs", tuple(sorted(unknown_refs, key=repr))),
        ("unsupported_ops", tuple(sorted(unsupported_ops, key=repr))),
    )

def _impl__unresolved_expression_location_taxonomy(location_scope: str) -> str:
    if location_scope == "return_value":
        return "return_value_unresolved"
    if location_scope == "guard_condition":
        return "return_guard_unresolved"
    if location_scope == "path_guard":
        return "path_guard_unresolved"
    if location_scope == "call_argument":
        return "call_argument_unresolved"
    if location_scope == "memory_address":
        return "memory_address_unresolved"
    if location_scope == "effect_surface":
        return "effect_surface_unresolved"
    return f"{location_scope or 'unknown'}_unresolved"

def _impl__unresolved_expression_cause_taxonomy(
    self,
    expr: Any,
    *,
    unresolved_kinds: set[Any],
    unknown_refs: set[Any],
    unsupported_ops: set[Any],
) -> str:
    has_phi = any(self._value_contains_originated_phi_circular(ref) for ref in unknown_refs)
    has_deferred_call = (
        "deferred_call_unknown" in unresolved_kinds
        or any(self._value_contains_deferred_call_ref(ref) for ref in unknown_refs)
    )
    has_readonly = any(self._value_contains_readonly_ref(ref) for ref in unknown_refs)
    has_float = self._expression_uses_float_or_float_op(expr)
    has_memory_or_effect = self._unsupported_ops_include_memory_or_effect(unsupported_ops)
    unresolved_count = len(unknown_refs)

    if (
        has_float
        and (has_phi or has_deferred_call or has_readonly or has_memory_or_effect or unresolved_count > 1)
    ):
        return "mixed_float_call_read_recurrence"
    if unresolved_count > 1 or ("phi_unresolved" in unresolved_kinds and not has_phi):
        return "multiple_or_nested_unresolved"
    if has_phi:
        if has_float or has_deferred_call or has_readonly or has_memory_or_effect:
            return "multiple_or_nested_unresolved"
        return "phi_circular_integer"
    if has_deferred_call:
        return "deferred_call_return"
    if has_readonly:
        return "readonly_memory_read"
    if "unsupported_smt_op" in unresolved_kinds:
        return "opaque_unknown"
    return "opaque_unknown"

def _impl__unresolved_expression_substage(location: str, cause: str) -> str:
    if cause == "phi_circular_integer" and location in {
        "return_guard_unresolved",
        "path_guard_unresolved",
    }:
        return "integer_phi_circular_guard_pending"
    if cause == "phi_circular_integer" and location == "return_value_unresolved":
        return "integer_phi_circular_value_pending"
    if cause == "deferred_call_return" and location == "return_value_unresolved":
        return "deferred_call_return_value_pending"
    if cause == "readonly_memory_read":
        return "readonly_memory_read_subnode_pending"
    if cause == "mixed_float_call_read_recurrence":
        return "mixed_float_call_read_recurrence_deferred"
    if cause == "multiple_or_nested_unresolved":
        return "multiple_or_nested_unresolved_deferred"
    return "typed_lowering_pending"

def _impl__value_contains_deferred_call_ref(cls, value: Any) -> bool:
    normalized = cls._normalize_nested_tuple(value)
    if isinstance(normalized, tuple):
        if normalized and normalized[0] == "deferred_call":
            return True
        return any(cls._value_contains_deferred_call_ref(item) for item in normalized)
    if isinstance(normalized, list):
        return any(cls._value_contains_deferred_call_ref(item) for item in normalized)
    if isinstance(normalized, dict):
        return any(
            cls._value_contains_deferred_call_ref(key)
            or cls._value_contains_deferred_call_ref(item)
            for key, item in normalized.items()
        )
    return False

def _impl__collect_unresolved_expression_classification(
    self,
    expr: Any,
    *,
    kinds: set[Any],
    unknown_refs: set[Any],
    unsupported_ops: set[Any],
) -> None:
    if expr is None or getattr(expr, "expr_type", None) is None:
        return
    if expression_contains_unsupported_smt_ops(expr):
        unsupported_ops.update(self._unsupported_smt_op_keys(expr))
        if unsupported_ops:
            kinds.add("unsupported_smt_op")
    if expr.expr_type == ExpressionType.UNKNOWN:
        kind, ref_key = self._unknown_expression_classification_key(expr)
        kinds.add(kind)
        unknown_refs.add(ref_key)
        return
    if expr.expr_type == ExpressionType.PHI and expr.value:
        branch_had_unresolved = False
        for condition, value in expr.value:
            if condition is not None and self._expression_contains_unresolved(condition.expression):
                branch_had_unresolved = True
                self._collect_unresolved_expression_classification(
                    condition.expression,
                    kinds=kinds,
                    unknown_refs=unknown_refs,
                    unsupported_ops=unsupported_ops,
                )
            if self._expression_contains_unresolved(value):
                branch_had_unresolved = True
                self._collect_unresolved_expression_classification(
                    value,
                    kinds=kinds,
                    unknown_refs=unknown_refs,
                    unsupported_ops=unsupported_ops,
                )
        if branch_had_unresolved:
            kinds.add("phi_unresolved")
        return
    for operand in getattr(expr, "operands", []) or []:
        self._collect_unresolved_expression_classification(
            operand,
            kinds=kinds,
            unknown_refs=unknown_refs,
            unsupported_ops=unsupported_ops,
        )

def _impl__unresolved_expression_recovery_proof_obligations(
    self,
    object_target_key: Tuple[Any, ...],
) -> Optional[Tuple[UnknownRecoveryProofObligation, ...]]:
    target_cause = self._unresolved_expression_target_cause(object_target_key)
    if target_cause in {
        "mixed_float_call_read_recurrence",
        "multiple_or_nested_unresolved",
        "readonly_memory_read",
    }:
        return self._generic_unresolved_expression_proof_obligations(target_cause)
    if self._object_target_contains_originated_phi_circular(object_target_key):
        return (
            UnknownRecoveryProofObligation.create(
                UnknownRecoveryProofKind.SOLVER_RETRY_OR_NORMALIZATION,
                "phi_circular_guard_condition_lowering",
                required_evidence=(
                    "object_target_key",
                    "multiequal_pcode_op_ref",
                    "guard_condition_key",
                    "guard_condition_literals",
                    "pair_lowering_diagnostic",
                    "unknown_count_relation",
                    "typed_lowering_rule",
                ),
                description=(
                    "Lower a PHI-circular guard only when its MULTIEQUAL origin "
                    "and guard-condition provenance are preserved."
                ),
            ),
            UnknownRecoveryProofObligation.create(
                UnknownRecoveryProofKind.SOLVER_RETRY_OR_NORMALIZATION,
                "recursive_summary_guard_equivalence",
                required_evidence=(
                    "left_phi_origin",
                    "right_phi_origin",
                    "guard_condition_pair",
                    "pair_lowering_diagnostic",
                    "summary_parameter_binding",
                    "value_shape_relation",
                ),
                description=(
                    "Prove the recursive-summary guard relation before allowing "
                    "the unresolved PHI-circular guard to affect equivalence."
                ),
            ),
        )
    if self._object_target_contains_deferred_call_unknown(object_target_key):
        return (
            UnknownRecoveryProofObligation.create(
                UnknownRecoveryProofKind.SOLVER_RETRY_OR_NORMALIZATION,
                "deferred_call_return_resolution",
                required_evidence=(
                    "object_target_key",
                    "deferred_call_site",
                    "callee_identity",
                    "call_effect_summary",
                ),
                description=(
                    "Resolve the deferred call return expression before lowering "
                    "the unresolved value into SMT."
                ),
            ),
            UnknownRecoveryProofObligation.create(
                UnknownRecoveryProofKind.SOLVER_RETRY_OR_NORMALIZATION,
                "deferred_call_result_equivalence",
                required_evidence=(
                    "left_return_value",
                    "right_return_value",
                    "argument_binding",
                    "return_width_policy",
                ),
                description=(
                    "Prove the deferred-call result is equivalent to the peer "
                    "return value under the active guard and ABI width policy."
                ),
            ),
        )
    if self._object_target_contains_void_opaque_unknown(object_target_key):
        return (
            UnknownRecoveryProofObligation.create(
                UnknownRecoveryProofKind.SOLVER_RETRY_OR_NORMALIZATION,
                "opaque_unknown_return_origin_resolution",
                required_evidence=(
                    "object_target_key",
                    "opaque_unknown_ref",
                    "return_storage",
                    "return_case_origin",
                ),
                description=(
                    "Resolve the opaque return-value origin before lowering the "
                    "unknown value into SMT."
                ),
            ),
            UnknownRecoveryProofObligation.create(
                UnknownRecoveryProofKind.SOLVER_RETRY_OR_NORMALIZATION,
                "opaque_unknown_return_value_equivalence",
                required_evidence=(
                    "left_return_value",
                    "right_return_value",
                    "guard_condition_pair",
                    "return_width_policy",
                ),
                description=(
                    "Prove the opaque return value is equivalent to the peer "
                    "return value under the active guard and width policy."
                ),
            ),
        )
    return None

def _impl__generic_unresolved_expression_proof_obligations(
    self,
    cause: str,
) -> Tuple[UnknownRecoveryProofObligation, ...]:
    return (
        UnknownRecoveryProofObligation.create(
            UnknownRecoveryProofKind.SOLVER_RETRY_OR_NORMALIZATION,
            "typed_expression_lowering",
            required_evidence=(
                "object_target_key",
                "unresolved_location",
                "unresolved_cause",
                "typed_expression_key",
            ),
            description=(
                "Classify and lower the unresolved expression before retrying SMT."
            ),
        ),
        UnknownRecoveryProofObligation.create(
            UnknownRecoveryProofKind.SOLVER_RETRY_OR_NORMALIZATION,
            "type_normalization",
            required_evidence=(
                "object_target_key",
                "unresolved_cause",
                "return_width_policy",
                "normalization_policy",
            ),
            description=(
                f"Normalize the {cause} expression only after its semantic "
                "dependencies have been proven."
            ),
        ),
    )

def _impl__unresolved_expression_target_cause(cls, object_target_key: Any) -> Optional[str]:
    causes: List[str] = []

    def visit(value: Any) -> None:
        normalized = cls._normalize_nested_tuple(value)
        if isinstance(normalized, tuple):
            if (
                len(normalized) == 2
                and normalized[0] == "unresolved_cause"
                and isinstance(normalized[1], str)
            ):
                causes.append(normalized[1])
                return
            for item in normalized:
                visit(item)
        elif isinstance(normalized, list):
            for item in normalized:
                visit(item)
        elif isinstance(normalized, dict):
            for key, item in normalized.items():
                visit(key)
                visit(item)

    visit(object_target_key)
    unique_causes = tuple(sorted(set(causes)))
    if not unique_causes:
        return None
    if "mixed_float_call_read_recurrence" in unique_causes:
        return "mixed_float_call_read_recurrence"
    if len(unique_causes) > 1:
        return "multiple_or_nested_unresolved"
    return unique_causes[0]

def _impl__unresolved_expression_action_status(
    self,
    object_target_key: Optional[Tuple[Any, ...]],
    object_evidence: Any,
) -> Optional[UnknownRecoveryActionStatus]:
    if object_evidence is not None:
        return UnknownRecoveryActionStatus.PENDING_PROOF
    if object_target_key is None:
        return None
    if self._unresolved_expression_recovery_proof_obligations(object_target_key):
        return UnknownRecoveryActionStatus.PLANNED
    return None

def _impl__object_target_contains_deferred_call_unknown(cls, value: Any) -> bool:
    normalized = cls._normalize_nested_tuple(value)
    if isinstance(normalized, tuple):
        if (
            len(normalized) >= 4
            and normalized[0] == "deferred_call"
            and normalized[1] == "call_out_of_scope"
        ):
            return True
        if (
            len(normalized) >= 2
            and normalized[0] == "unresolved_kinds"
            and isinstance(normalized[1], tuple)
            and "deferred_call_unknown" in normalized[1]
        ):
            return True
        return any(cls._object_target_contains_deferred_call_unknown(item) for item in normalized)
    if isinstance(normalized, list):
        return any(cls._object_target_contains_deferred_call_unknown(item) for item in normalized)
    if isinstance(normalized, dict):
        return any(
            cls._object_target_contains_deferred_call_unknown(key)
            or cls._object_target_contains_deferred_call_unknown(item)
            for key, item in normalized.items()
        )
    return False

def _impl__try_build_unresolved_phi_circular_lowering(
    self,
    *,
    base_ctx: Dict[str, Any],
    case1: ReturnCase,
    case2: ReturnCase,
    pair_id: str,
) -> Optional[_UnresolvedDeferredCallLowering]:
    # A phi-circular equality assertion is a semantic proof obligation, not
    # a syntactic lowering. Keep this disabled until completed proof
    # evidence can be checked here.
    return None

def _impl__try_build_unresolved_deferred_call_lowering(
    self,
    *,
    base_ctx: Dict[str, Any],
    case1: ReturnCase,
    case2: ReturnCase,
    pair_id: str,
) -> Optional[_UnresolvedDeferredCallLowering]:
    analysis1 = base_ctx.get("analysis1")
    analysis2 = base_ctx.get("analysis2")
    if analysis1 is None or analysis2 is None:
        return None
    value1 = getattr(case1, "value_expr", None)
    value2 = getattr(case2, "value_expr", None)
    if self._expression_has_unsupported_smt_op_excluding_unknowns(value1):
        return None
    if self._expression_has_unsupported_smt_op_excluding_unknowns(value2):
        return None
    if self._case_conditions_have_unsupported_smt_op_excluding_unknowns(case1):
        return None
    if self._case_conditions_have_unsupported_smt_op_excluding_unknowns(case2):
        return None
    value_bits1 = int(expression_smt_bit_width(value1) or 0)
    value_bits2 = int(expression_smt_bit_width(value2) or 0)
    if value_bits1 <= 0 or value_bits2 <= 0 or value_bits1 != value_bits2:
        return None

    left_unknowns = self._collect_case_unknown_expression_nodes(case1)
    right_unknowns = self._collect_case_unknown_expression_nodes(case2)
    if not left_unknowns or not right_unknowns or len(left_unknowns) != len(right_unknowns):
        return None

    left_items = []
    right_items = []
    for expr in left_unknowns:
        item = self._deferred_call_unknown_lowering_item(
            analysis1,
            expr,
            side_label="function1",
        )
        if item is None:
            return None
        left_items.append(item)
    for expr in right_unknowns:
        item = self._deferred_call_unknown_lowering_item(
            analysis2,
            expr,
            side_label="function2",
        )
        if item is None:
            return None
        right_items.append(item)

    unmatched_right = list(right_items)
    assertions: List[str] = [
        f"; unresolved_expression runtime-unknown equality lowering for pair {pair_id}",
        "; object evidence: pairwise_runtime_unknown_lowering",
    ]
    evidence: List[Tuple[Any, ...]] = []
    lowered_left_unknown_keys: List[Any] = []
    lowered_right_unknown_keys: List[Any] = []
    for left_expr, left_info, left_key, left_kind, left_match_key in left_items:
        if left_kind != "deferred_call":
            return None
        proof_content = self._matched_deferred_call_argument_proof_content(
            left_key,
            analysis1,
            analysis1,
            analysis2,
        )
        if proof_content is None:
            return None
        expected_peer_key = self._normalize_nested_tuple(
            proof_content.get("peer_object_target_key")
        )
        candidates = [
            item
            for item in unmatched_right
            if (
                item[3] == left_kind
                and self._normalize_nested_tuple(item[2]) == expected_peer_key
            )
        ]
        if len(candidates) != 1:
            return None
        right_expr, right_info, right_key, right_kind, right_match_key = candidates[0]
        left_bits = int(expression_smt_bit_width(left_expr) or 0)
        right_bits = int(expression_smt_bit_width(right_expr) or 0)
        if left_bits <= 0 or right_bits <= 0 or left_bits != right_bits:
            return None
        unmatched_right.remove(candidates[0])
        assertions.append(
            f"(assert (= {left_expr.to_smt(float_mode='fp')} {right_expr.to_smt(float_mode='fp')}))"
        )
        lowered_left_unknown_keys.append(self._expression_runtime_object_key(left_expr))
        lowered_right_unknown_keys.append(self._expression_runtime_object_key(right_expr))
        evidence.append(
            (
                "matched_deferred_call_runtime_unknown",
                ("left_unknown", self._expression_runtime_object_key(left_expr)),
                ("right_unknown", self._expression_runtime_object_key(right_expr)),
                ("left_object_target", left_key),
                ("right_object_target", right_key),
                ("lowering_kind", left_kind),
                ("match_key", left_match_key),
                ("bit_width", left_bits),
                (
                    "left_recovery_status",
                    getattr(left_info, "call_argument_recovery_status", None),
                ),
                (
                    "right_recovery_status",
                    getattr(right_info, "call_argument_recovery_status", None),
                ),
            )
        )
    if unmatched_right:
        return None

    evidence_by_pair = base_ctx.setdefault(
        "pairwise_unresolved_deferred_call_lowering_evidence_by_pair",
        {},
    )
    evidence_by_pair[pair_id] = tuple(evidence)
    lowered_keys_by_pair = base_ctx.setdefault(
        "pairwise_unresolved_deferred_call_lowered_unknown_keys_by_pair",
        {},
    )
    lowered_keys_by_pair[pair_id] = {
        "left": tuple(lowered_left_unknown_keys),
        "right": tuple(lowered_right_unknown_keys),
    }
    return _UnresolvedDeferredCallLowering(
        assertions=tuple(assertions),
        evidence=tuple(evidence),
    )

def _impl__case_conditions_contain_unresolved(self, case: ReturnCase) -> bool:
    for condition in getattr(case, "conditions", None) or ():
        expression = getattr(condition, "expression", None)
        if self._expression_contains_unresolved(expression):
            return True
    return False

def _impl__deferred_call_unknown_lowering_item(
    self,
    analysis: FunctionReturnAnalysis,
    expr: Any,
    *,
    side_label: str,
) -> Optional[Tuple[Any, Any, Tuple[Any, ...], str, Tuple[Any, ...]]]:
    runtime_ref = getattr(expr, "runtime_ref", None)
    deferred_ref = getattr(runtime_ref, "deferred_call_ref", None)
    if deferred_ref is not None:
        info = self._deferred_call_info_for_ref(analysis, deferred_ref)
        if info is None:
            return None
        object_target_key = self._deferred_call_object_target_key(
            info,
            analysis=analysis,
            side_label=side_label,
        )
        if not self._call_effect_target_expression_key_is_present(
            self._cross_binary_call_effect_component_key(
                self._deferred_call_target_expression_key(object_target_key)
            )
        ):
            return None
        if not self._call_effect_argument_keys_are_present(
            self._cross_binary_call_effect_component_key(
                self._deferred_call_argument_keys(object_target_key)
            )
        ):
            return None
        return expr, info, object_target_key, "deferred_call", ()
    return None

def _impl__deferred_call_info_for_ref(
    self,
    analysis: FunctionReturnAnalysis,
    deferred_ref: Any,
) -> Optional[Any]:
    try:
        ref_key = deferred_ref.stable_key()
    except (AttributeError, TypeError, ValueError):
        return None
    deferred_calls = getattr(analysis, "deferred_calls", None) or {}
    direct = deferred_calls.get(ref_key) if hasattr(deferred_calls, "get") else None
    if direct is not None:
        return direct
    for info in getattr(deferred_calls, "values", lambda: ())():
        candidate_ref = getattr(info, "deferred_call_ref", None)
        try:
            if candidate_ref is not None and candidate_ref.stable_key() == ref_key:
                return info
        except (AttributeError, TypeError, ValueError):
            continue
    return None

def _impl__case_contains_unresolved_expression(
    self,
    case: ReturnCase,
    extra_conditions: Optional[List[Condition]] = None,
    *,
    own_render_fn=None,
    extra_render_fn=None,
    base_ctx: Optional[Dict[str, Any]] = None,
    query_label: str = "case",
) -> bool:
    return self._get_expression_safety_checker(base_ctx).case_contains_unresolved(
        case,
        own_render_fn=own_render_fn,
        extra_conditions=extra_conditions,
        extra_render_fn=extra_render_fn,
        query_label=query_label,
    )

def _impl__case_value_contains_unresolved(
    self,
    case: ReturnCase,
    extra_conditions: Optional[List[Condition]] = None,
    *,
    own_render_fn=None,
    extra_render_fn=None,
    base_ctx: Optional[Dict[str, Any]] = None,
    query_label: str = "value",
) -> bool:
    contains_unresolved = self._get_expression_safety_checker(base_ctx).value_contains_unresolved(
        case,
        own_render_fn=own_render_fn,
        extra_conditions=extra_conditions,
        extra_render_fn=extra_render_fn,
        query_label=query_label,
    )
    if not contains_unresolved:
        return False
    if self._case_value_unresolved_is_pairwise_lowered(
        case,
        base_ctx=base_ctx,
        query_label=query_label,
    ):
        return False
    return True

def _impl__case_value_unresolved_is_pairwise_lowered(
    self,
    case: ReturnCase,
    *,
    base_ctx: Optional[Dict[str, Any]],
    query_label: str,
) -> bool:
    if base_ctx is None:
        return False
    pair_id, side = self._pair_id_and_side_from_value_query_label(query_label)
    if pair_id is None or side is None:
        return False
    lowered_by_pair = base_ctx.get("pairwise_unresolved_deferred_call_lowered_unknown_keys_by_pair") or {}
    lowered = lowered_by_pair.get(pair_id) or {}
    lowered_keys = set(lowered.get(side) or ())
    if not lowered_keys:
        return False
    value_expr = getattr(case, "value_expr", None)
    if self._expression_has_unsupported_smt_op_excluding_unknowns(value_expr):
        return False
    unknown_keys = tuple(
        self._expression_runtime_object_key(expr)
        for expr in self._collect_unknown_expression_nodes(value_expr)
    )
    if not unknown_keys:
        return False
    return all(key in lowered_keys for key in unknown_keys)

def _impl__expression_contains_unresolved(self, expr) -> bool:
    if expr is None:
        return False

    if expr.expr_type == ExpressionType.UNKNOWN:
        return True
    if expression_contains_unsupported_smt_ops(expr):
        return True

    if expr.expr_type == ExpressionType.PHI and expr.value:
        for cond, value in expr.value:
            if cond is not None and self._expression_contains_unresolved(cond.expression):
                return True
            if self._expression_contains_unresolved(value):
                return True
        return False

    for operand in getattr(expr, "operands", []) or []:
        if self._expression_contains_unresolved(operand):
            return True

    return False

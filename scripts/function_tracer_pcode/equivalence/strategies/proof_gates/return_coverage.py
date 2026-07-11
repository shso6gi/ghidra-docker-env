"""Stateless method implementations extracted from ``scripts.function_tracer_pcode.equivalence.strategies.base``."""

from __future__ import annotations

from typing import Any
from ._shared import (
    Condition,
    ConditionSMTOracle,
    Mapping,
    ReturnCoverageCheckResult,
    UnknownReasonId,
    UnknownRecoveryActionStatus,
    UnknownRecoveryProofKind,
    build_proof_obligation_id,
    build_unknown_recovery_actions,
    coerce_value_to_bitvec_width,
    expression_smt_bit_width,
    hashlib,
    make_unknown_reason,
)

def invoke(_service_name: str, *args: Any, **kwargs: Any) -> Any:
    implementation_function = globals().get(f"_impl_{_service_name}")
    if implementation_function is None:
        raise AttributeError(_service_name)
    return implementation_function(*args, **kwargs)


def implementation(_service_name: str):
    return globals().get(f"_impl_{_service_name}")

def _impl__collect_return_coverage_unsafety_reasons(
    self,
    base_ctx: Dict[str, Any],
    cases1: Sequence[Any],
    cases2: Sequence[Any],
    param_replace_fn1,
    param_replace_fn2,
    analysis1: Optional[FunctionReturnAnalysis] = None,
    analysis2: Optional[FunctionReturnAnalysis] = None,
) -> List[str]:
    reasons: List[str] = []
    outcome_covered_labels = self._outcome_partition_covered_labels(
        base_ctx,
        analysis1,
        analysis2,
        param_replace_fn1,
        param_replace_fn2,
    )
    outcome_inconclusive_labels = self._outcome_partition_inconclusive_labels(
        base_ctx,
        analysis1,
        analysis2,
        param_replace_fn1,
        param_replace_fn2,
    )
    for label, cases, replace_fn, analysis in (
        ("function1", cases1, param_replace_fn1, analysis1),
        ("function2", cases2, param_replace_fn2, analysis2),
    ):
        if label in outcome_covered_labels:
            coverage_result = ReturnCoverageCheckResult(
                status="covered",
                coverage_proof_method="outcome_partition_equivalence",
                solver_status="unsat",
            )
        elif label in outcome_inconclusive_labels:
            coverage_result = ReturnCoverageCheckResult(
                status="inconclusive",
                reason_id=UnknownReasonId.OUTCOME_PARTITION_UNKNOWN,
                detail=f"Outcome partition unknown for {label}: UnknownOutcome covers missing control region",
                inconclusive_cause="unknown_outcome_partition",
                solver_status="unknown",
            )
        else:
            coverage_result = self._check_return_case_coverage_gap(
                base_ctx,
                cases,
                replace_fn,
                label,
            )
        if coverage_result.status == "gap":
            if coverage_result.detail:
                self._debug_print(coverage_result.detail)
            reasons.append(f"{label}:return_coverage_gap")
            reasons.extend(
                f"{label}:{reason_id}"
                for reason_id in self._summary_return_candidate_blocker_reason_ids(analysis)
            )
        elif coverage_result.status == "inconclusive":
            if coverage_result.detail:
                self._debug_print(coverage_result.detail)
            blocker_reason = coverage_result.reason_id or UnknownReasonId.RETURN_COVERAGE_INCONCLUSIVE
            reasons.append(f"{label}:{blocker_reason.value}")
            if (
                coverage_result.reason_id == UnknownReasonId.RETURN_COVERAGE_INCONCLUSIVE
                and self.enable_completed_recovery_proofs
                and analysis is not None
                and coverage_result.can_record_completion_proof
                and coverage_result.inconclusive_cause in self._RETURN_COVERAGE_DISCHARGEABLE_INCONCLUSIVE_CAUSES
                and self._return_coverage_proof_content_can_discharge_inconclusive(
                    self._return_coverage_inconclusive_proof_content(
                        base_ctx=base_ctx,
                        label=label,
                        cases=cases,
                        replace_fn=replace_fn,
                        inconclusive_cause=coverage_result.inconclusive_cause,
                    )
                )
            ):
                self._record_completed_return_coverage_proof(
                    label,
                    blocker_reason,
                    analysis,
                    analysis1,
                    analysis2,
                    proof_content=self._return_coverage_inconclusive_proof_content(
                        base_ctx=base_ctx,
                        label=label,
                        cases=cases,
                        replace_fn=replace_fn,
                        inconclusive_cause=coverage_result.inconclusive_cause,
                    ),
                )
        elif (
            coverage_result.status == "covered"
            and analysis1 is not None
            and analysis2 is not None
            and analysis is not None
        ):
            blocker_reason = self._analysis_requires_completed_return_coverage_proof(
                analysis,
                ignored_reason_ids=(coverage_result.reason_id,),
            )
            required_blocker_reason = blocker_reason
            proof_record_reason = blocker_reason
            if proof_record_reason is None and self.enable_completed_recovery_proofs:
                proof_record_reason = UnknownReasonId.RETURN_COVERAGE_GAP
            if proof_record_reason is not None and self.enable_completed_recovery_proofs:
                proof_content = self._return_coverage_covered_proof_content(
                    base_ctx=base_ctx,
                    label=label,
                    cases=cases,
                    replace_fn=replace_fn,
                    coverage_proof_method=coverage_result.coverage_proof_method,
                    solver_status=coverage_result.solver_status,
                )
                self._record_completed_return_coverage_proof(
                    label,
                    proof_record_reason,
                    analysis,
                    analysis1,
                    analysis2,
                    proof_content=proof_content,
                )
                if required_blocker_reason in {
                    UnknownReasonId.RETURN_COVERAGE_GAP,
                    UnknownReasonId.RETURN_COVERAGE_INCONCLUSIVE,
                }:
                    reason_record = self._make_blocking_unsafety_unknown_reason(
                        f"{label}:{required_blocker_reason.value}",
                        analysis1,
                        analysis2,
                        stage="S_RETURN_COVERAGE_CHECK",
                    )
                    if not self._return_coverage_proof_is_complete(
                        reason_record,
                        analysis1,
                        analysis2,
                    ):
                        reasons.append(f"{label}:{required_blocker_reason.value}")
            elif blocker_reason is not None:
                reasons.append(f"{label}:{blocker_reason.value}")
            if coverage_result.detail:
                self._debug_print(coverage_result.detail)
    return reasons

def _impl__record_completed_return_coverage_proof(
    self,
    label: str,
    reason_id: UnknownReasonId,
    analysis: FunctionReturnAnalysis,
    analysis1: FunctionReturnAnalysis,
    analysis2: FunctionReturnAnalysis,
    proof_content: Optional[Mapping[str, Any]] = None,
) -> None:
    if not self.enable_completed_recovery_proofs:
        return
    if self._analysis_has_active_return_coverage_blockers(
        analysis,
        ignored_reason_ids=(reason_id,),
    ):
        return
    requirements = self._RETURN_COVERAGE_COMPLETION_REQUIREMENTS.get(reason_id)
    if not requirements:
        return
    object_target_key = self._return_coverage_object_target_key(
        f"{label}:{reason_id.value}",
        analysis1,
        analysis2,
    )
    if object_target_key is None:
        return
    proof_kind = UnknownRecoveryProofKind.RETURN_COVERAGE_COMPLETION.value
    existing_ids = {
        self._normalize_nested_tuple(item.get("proof_obligation_id"))
        for item in getattr(analysis, "completed_recovery_proof_evidence", ()) or ()
        if isinstance(item, Mapping)
    }
    records: List[Dict[str, Any]] = [
        dict(item)
        for item in getattr(analysis, "completed_recovery_proof_evidence", ()) or ()
        if isinstance(item, Mapping)
    ]
    proof_content_map = dict(proof_content) if isinstance(proof_content, Mapping) else {}
    proof_content_map["proof_target_identity"] = object_target_key
    prototype = {
        "status": "complete",
        "reason_id": reason_id.value,
        "target_schema_version": self._RETURN_COVERAGE_TARGET_SCHEMA_VERSION,
        "proof_schema_version": self._RETURN_COVERAGE_PROOF_SCHEMA_VERSION,
        "object_target_key": object_target_key,
        "proof_content": proof_content_map,
    }
    if not self._return_coverage_proof_content_is_complete(
        prototype,
        reason_id=reason_id,
    ):
        return
    for proof_stage, evidence_kind in requirements:
        proof_id = build_proof_obligation_id(
            reason_id.value,
            proof_stage,
            proof_kind,
            evidence_kind,
            object_target_key,
        )
        if proof_id in existing_ids:
            continue
        candidate = {
            "object_derived": True,
            "status": "complete",
            "reason_id": reason_id.value,
            "recovery_proof_kind": proof_kind,
            "target_schema_version": self._RETURN_COVERAGE_TARGET_SCHEMA_VERSION,
            "proof_schema_version": self._RETURN_COVERAGE_PROOF_SCHEMA_VERSION,
            "proof_stage": proof_stage,
            "evidence_kind": evidence_kind,
            "object_target_key": object_target_key,
            "proof_obligation_id": proof_id,
            "proof_source": "return_case_coverage_check",
            "coverage_status": "covered",
            "required_evidence": (evidence_kind,),
            "proof_content": proof_content_map,
        }
        if self._return_coverage_proof_id_from_evidence(candidate) is None:
            continue
        records.append(candidate)
        existing_ids.add(proof_id)
    analysis.completed_recovery_proof_evidence = tuple(records)

def _impl__return_coverage_covered_proof_content(
    self,
    base_ctx: Dict[str, Any],
    label: str,
    cases: Sequence[Any],
    replace_fn,
    *,
    coverage_proof_method: Optional[str] = None,
    solver_status: Optional[str] = None,
) -> Dict[str, Any]:
    disjuncts = self._return_case_smt_disjunctions(cases, replace_fn)
    query = self._build_return_case_coverage_query(
        base_ctx,
        cases,
        replace_fn,
        label,
    )
    normalized_query = self._normalize_query(query) if query is not None else None
    if normalized_query is None and disjuncts:
        normalized_query = "(or " + " ".join(disjuncts) + ")"
    normalized_query_status = (
        "complete" if normalized_query is not None else "missing"
    )
    structural_evidence = self._return_coverage_structural_proof_content(
        cases,
        solver_status=solver_status,
        coverage_proof_method=coverage_proof_method,
    )
    coverage_method = coverage_proof_method or "return_case_coverage_check"
    return {
        "proof_schema_version": self._RETURN_COVERAGE_PROOF_SCHEMA_VERSION,
        "normalization_schema_version": self._RETURN_COVERAGE_NORMALIZATION_SCHEMA_VERSION,
        **structural_evidence,
        "case_guard_disjunction": {
            "status": "complete",
            "query_cases": tuple(disjuncts or ()),
            "case_count": len(tuple(disjuncts or ())),
            "status_scope": "function-local",
        },
        "normalized_guard_formula": {
            "status": normalized_query_status,
            "query": normalized_query if normalized_query is not None else query,
        },
        "coverage_guard_evidence": {
            "status": normalized_query_status,
            "guard_source": "return_partition_guard_set",
            "coverage_status": "covered",
            "coverage_proof_method": coverage_method,
            "case_count": len(tuple(disjuncts or ())),
            "normalized_guard_formula_sha256": (
                hashlib.sha256(normalized_query.encode("utf-8")).hexdigest()
                if isinstance(normalized_query, str) and normalized_query
                else None
            ),
        },
        "coverage_status": {
            "status": "complete",
            "result": "covered",
            "proof_source": "return_case_coverage_check",
        },
    }

def _impl__return_coverage_inconclusive_proof_content(
    self,
    base_ctx: Dict[str, Any],
    label: str,
    cases: Sequence[Any],
    replace_fn,
    inconclusive_cause: Optional[str] = None,
) -> Dict[str, Any]:
    disjuncts = self._return_case_smt_disjunctions(cases, replace_fn)
    query = self._build_return_case_coverage_query(
        base_ctx,
        cases,
        replace_fn,
        label,
    )
    normalized_query = self._normalize_query(query) if query is not None else None
    if normalized_query is None and disjuncts:
        normalized_query = "(or " + " ".join(disjuncts) + ")"
    normalized_query_status = (
        "complete" if normalized_query is not None else "missing"
    )
    structural_evidence = self._return_coverage_structural_proof_content(
        cases,
        solver_status="unknown",
    )
    return {
        "proof_schema_version": self._RETURN_COVERAGE_PROOF_SCHEMA_VERSION,
        "normalization_schema_version": self._RETURN_COVERAGE_NORMALIZATION_SCHEMA_VERSION,
        "inconclusive_cause": inconclusive_cause,
        **structural_evidence,
        "case_guard_disjunction": {
            "status": "complete",
            "query_cases": tuple(disjuncts or ()),
            "case_count": len(tuple(disjuncts or ())),
            "status_scope": "function-local",
        },
        "normalized_guard_formula": {
            "status": normalized_query_status,
            "query": normalized_query if normalized_query is not None else query,
        },
        "coverage_guard_evidence": {
            "status": normalized_query_status,
            "guard_source": "case_guard_disjunction",
            "case_count": len(tuple(disjuncts or ())),
            "normalized_guard_formula_sha256": (
                hashlib.sha256(normalized_query.encode("utf-8")).hexdigest()
                if isinstance(normalized_query, str) and normalized_query
                else None
            ),
        },
        "solver_model_or_timeout": {
            "status": "unknown",
            "detail": "coverage query returned UNKNOWN/timeout",
        },
    }

def _impl__return_coverage_structural_proof_content(
    self,
    cases: Sequence[Any],
    *,
    solver_status: Optional[str],
    coverage_proof_method: Optional[str] = None,
) -> Dict[str, Any]:
    case_entries: List[Tuple[Any, ...]] = []
    miss_entries: List[Tuple[Any, ...]] = []
    bit_widths: Set[int] = set()
    signedness: Set[str] = set()
    for case_index, case in enumerate(cases or ()):
        return_info = getattr(case, "return_info", None)
        structural_conditions = (
            getattr(return_info, "conditions", None)
            if return_info is not None
            else getattr(case, "conditions", None)
        ) or ()
        structural_value = (
            getattr(return_info, "value", None)
            if return_info is not None
            else getattr(case, "value_expr", None)
        )
        guard_keys = tuple(
            self._return_condition_object_key(condition)
            for condition in structural_conditions
        )
        value_key = self._expression_runtime_object_key(structural_value)
        miss_expr = self._case_miss_expression(
            list(structural_conditions)
        )
        miss_key = self._expression_runtime_object_key(miss_expr) if miss_expr is not None else None
        case_entries.append(
            (
                "return_case_guard_set",
                int(case_index),
                ("guard_structural_keys", guard_keys),
                ("return_value_structural_key", value_key),
            )
        )
        miss_entries.append(
            (
                "case_miss_formula",
                int(case_index),
                miss_key,
            )
        )
        for condition in structural_conditions:
            self._collect_condition_width_sign_metadata(condition, bit_widths, signedness)
    case_entries = list(self._canonicalize_key_sequence(case_entries))
    miss_entries = list(self._canonicalize_key_sequence(miss_entries))
    return {
        "structural_guard_keys": {
            "status": "complete",
            "case_count": len(case_entries),
            "keys": tuple(case_entries),
        },
        "structural_miss_formula_keys": {
            "status": "complete",
            "case_count": len(miss_entries),
            "keys": tuple(miss_entries),
        },
        "coverage_solver_evidence": {
            "status": str(solver_status) if solver_status is not None else "not_applicable",
            "proof_method": coverage_proof_method or "unknown",
        },
        "bit_width_signedness_metadata": {
            "status": "complete",
            "bit_widths": tuple(sorted(bit_widths)),
            "signedness": tuple(sorted(signedness)),
        },
    }

def _impl__return_coverage_normalization_policy(cls, *, rules: Sequence[Any] = ()) -> Dict[str, Any]:
    return {
        "normalization_policy_id": cls._RETURN_COVERAGE_NORMALIZATION_POLICY_ID,
        "normalization_schema_version": cls._RETURN_COVERAGE_NORMALIZATION_SCHEMA_VERSION,
        "rule_set_version": cls._RETURN_COVERAGE_NORMALIZATION_RULESET_VERSION,
        "canonical_encoding_version": cls._RETURN_COVERAGE_NORMALIZATION_CANONICAL_ENCODING_VERSION,
        "rules": tuple(sorted(tuple(rules or ()), key=repr)),
    }

def _impl__return_coverage_normalization_policy_digest(cls, policy: Mapping[str, Any]) -> Optional[str]:
    if not isinstance(policy, Mapping):
        return None
    required = {
        "normalization_policy_id",
        "normalization_schema_version",
        "rule_set_version",
        "canonical_encoding_version",
        "rules",
    }
    if not required.issubset(set(policy.keys())):
        return None
    if policy.get("normalization_policy_id") != cls._RETURN_COVERAGE_NORMALIZATION_POLICY_ID:
        return None
    if policy.get("normalization_schema_version") != cls._RETURN_COVERAGE_NORMALIZATION_SCHEMA_VERSION:
        return None
    if policy.get("rule_set_version") != cls._RETURN_COVERAGE_NORMALIZATION_RULESET_VERSION:
        return None
    if policy.get("canonical_encoding_version") != cls._RETURN_COVERAGE_NORMALIZATION_CANONICAL_ENCODING_VERSION:
        return None
    rules = policy.get("rules")
    if not isinstance(rules, (tuple, list)):
        return None
    normalized_rules = []
    for rule in rules:
        if not isinstance(rule, Mapping) or not isinstance(rule.get("rule_id"), str):
            return None
        normalized_rules.append({key: rule[key] for key in sorted(rule.keys())})
    normalized_rules.sort(key=lambda item: str(item.get("rule_id")))
    return cls._canonical_json_digest(
        {
            "canonical_encoding_version": policy.get("canonical_encoding_version"),
            "normalization_policy_id": policy.get("normalization_policy_id"),
            "normalization_schema_version": policy.get("normalization_schema_version"),
            "rule_set_version": policy.get("rule_set_version"),
            "rules": tuple(normalized_rules),
        }
    )

def _impl__analysis_has_active_return_coverage_blockers(
    self,
    analysis: FunctionReturnAnalysis,
    *,
    ignored_reason_ids: Sequence[Optional[UnknownReasonId]],
) -> bool:
    return (
        self._analysis_requires_completed_return_coverage_proof(
            analysis,
            ignored_reason_ids=ignored_reason_ids,
        )
        is not None
    )

def _impl__analysis_requires_completed_return_coverage_proof(
    self,
    analysis: FunctionReturnAnalysis,
    *,
    ignored_reason_ids: Sequence[Optional[UnknownReasonId]],
) -> Optional[UnknownReasonId]:
    ignored_reason_kinds = {
        self._blocking_reason_kind(reason.value)
        for reason in ignored_reason_ids
        if reason is not None
    }
    for reason in (
        getattr(analysis, "get_decisive_sat_unsafety_reasons", lambda: ())()
    ):
        reason_text = str(reason)
        reason_kind = self._blocking_reason_kind(reason_text)
        if reason_kind in {
            "return_case_coverage_gap",
            "return_case_coverage_inconclusive",
        }:
            continue
        if reason_kind in ignored_reason_kinds:
            continue
        if reason_kind == "return_coverage_gap":
            return UnknownReasonId.RETURN_COVERAGE_GAP
        if reason_kind == "return_coverage_inconclusive":
            return UnknownReasonId.RETURN_COVERAGE_INCONCLUSIVE
        return self._unknown_reason_id_for_blocking_unsafety(reason_text)
    return None

def _impl__make_return_coverage_unknown_reason(
    self,
    typed_reason_id: UnknownReasonId,
    blocking_reason: str,
    analysis1: FunctionReturnAnalysis,
    analysis2: FunctionReturnAnalysis,
    *,
    stage: str,
) -> UnknownReasonRecord:
    object_target_key = self._return_coverage_object_target_key(
        blocking_reason,
        analysis1,
        analysis2,
    )
    kwargs: Dict[str, Any] = {}
    if object_target_key is not None:
        kwargs.update(
            {
                "object_target_key": object_target_key,
                "recovery_action": "return_coverage_proof_required",
                "action_status": UnknownRecoveryActionStatus.PENDING_PROOF,
            }
        )
    return make_unknown_reason(
        typed_reason_id,
        stage=stage,
        evidence_refs=(blocking_reason,),
        detail=blocking_reason,
        **kwargs,
    )

def _impl__unresolved_return_coverage_unknown_reasons(
    self,
    blocking_reasons: Sequence[str],
    analysis1: FunctionReturnAnalysis,
    analysis2: FunctionReturnAnalysis,
    *,
    stage: str,
) -> List[UnknownReasonRecord]:
    unresolved: List[UnknownReasonRecord] = []
    for blocking_reason in blocking_reasons:
        reason_record = self._make_blocking_unsafety_unknown_reason(
            blocking_reason,
            analysis1,
            analysis2,
            stage=stage,
        )
        self._record_completed_call_effect_summary_proof_if_safe(
            reason_record,
            analysis1,
            analysis2,
        )
        if self._recovery_proof_is_complete(
            reason_record,
            analysis1,
            analysis2,
        ):
            continue
        unresolved.append(reason_record)
    return unresolved

def _impl__return_coverage_proof_is_complete(
    self,
    reason_record: UnknownReasonRecord,
    analysis1: FunctionReturnAnalysis,
    analysis2: FunctionReturnAnalysis,
) -> bool:
    if reason_record.reason_id not in (
        UnknownReasonId.RETURN_COVERAGE_GAP.value,
        UnknownReasonId.RETURN_COVERAGE_INCONCLUSIVE.value,
    ):
        return False
    completed = set(self._completed_recovery_proof_ids(analysis1, analysis2))
    required_ids = tuple(
        self._normalize_nested_tuple(action.proof_obligation_id)
        for action in build_unknown_recovery_actions([reason_record])
    )
    if not required_ids or any(proof_id is None for proof_id in required_ids):
        return False
    return all(proof_id in completed for proof_id in required_ids)

def _impl__return_coverage_proof_content_can_discharge_inconclusive(
    cls,
    proof_content: Any,
) -> bool:
    if not isinstance(proof_content, Mapping):
        return False
    solver_evidence = proof_content.get("solver_model_or_timeout")
    if solver_evidence is None:
        return False
    if not isinstance(solver_evidence, Mapping):
        return False
    status = cls._evidence_text(solver_evidence, "status")
    return status in {"complete", "completed", "proven", "unsat", "discharged"}

def _impl__return_coverage_guard_evidence_is_complete(
    cls,
    proof_content: Mapping[str, Any],
    normalized_query: str,
) -> bool:
    guard_evidence = proof_content.get("coverage_guard_evidence")
    if not isinstance(guard_evidence, Mapping):
        return False
    if cls._evidence_text(guard_evidence, "status") not in {"complete", "completed", "proven"}:
        return False
    guard_source = cls._evidence_text(guard_evidence, "guard_source")
    if guard_source not in {
        "case_guard_disjunction",
        "normalized_guard_formula",
        "return_partition_guard_set",
    }:
        return False
    if guard_source != "case_guard_disjunction" and cls._evidence_text(
        guard_evidence,
        "coverage_status",
    ) != "covered":
        return False
    case_count = guard_evidence.get("case_count")
    if not isinstance(case_count, int) or case_count < 0:
        return False
    expected_hash = hashlib.sha256(normalized_query.encode("utf-8")).hexdigest()
    return guard_evidence.get("normalized_guard_formula_sha256") == expected_hash

def _impl__return_coverage_proof_content_is_complete(
    cls,
    evidence: Mapping[str, Any],
    reason_id: Optional[UnknownReasonId] = None,
) -> bool:
    if cls._evidence_get(evidence, "target_schema_version") != cls._RETURN_COVERAGE_TARGET_SCHEMA_VERSION:
        return False
    evidence_schema = cls._evidence_get(evidence, "proof_schema_version")
    if evidence_schema not in {
        cls._RETURN_COVERAGE_PROOF_SCHEMA_VERSION,
        cls._RETURN_COVERAGE_NORMALIZATION_AWARE_PROOF_SCHEMA_VERSION,
    }:
        return False
    if reason_id is not None:
        evidence_reason_id = cls._evidence_text(evidence, "reason_id")
        if evidence_reason_id != reason_id.value:
            return False
    proof_content = cls._evidence_get(evidence, "proof_content")
    if not isinstance(proof_content, Mapping):
        return False
    if reason_id is not None:
        applicable_reason_ids = cls._normalize_nested_tuple(
            cls._evidence_get(evidence, "applicable_reason_ids")
        )
        if applicable_reason_ids is None:
            applicable_reason_ids = cls._normalize_nested_tuple(
                proof_content.get("applicable_reason_ids")
            )
        if applicable_reason_ids is not None and reason_id.value not in set(applicable_reason_ids):
            return False
    evidence_target = cls._normalize_nested_tuple(cls._evidence_get(evidence, "object_target_key"))
    proof_target = cls._normalize_nested_tuple(proof_content.get("proof_target_identity"))
    if proof_target != evidence_target:
        return False
    content_schema = proof_content.get("proof_schema_version")
    if content_schema != evidence_schema:
        return False
    if proof_content.get("normalization_schema_version") != cls._RETURN_COVERAGE_NORMALIZATION_SCHEMA_VERSION:
        return False
    normalization_required = cls._return_coverage_normalization_required(
        evidence,
        proof_content,
        evidence_target,
    )
    if normalization_required and evidence_schema != cls._RETURN_COVERAGE_NORMALIZATION_AWARE_PROOF_SCHEMA_VERSION:
        return False
    if evidence_schema == cls._RETURN_COVERAGE_NORMALIZATION_AWARE_PROOF_SCHEMA_VERSION:
        if not cls._return_coverage_normalization_proof_content_is_complete(
            proof_content,
            evidence_target,
            required=normalization_required,
        ):
            return False
    if not cls._return_coverage_structural_proof_content_is_complete(proof_content):
        return False
    if not cls._return_coverage_structural_proof_content_matches_target(
        proof_content,
        evidence_target,
    ):
        return False
    case_guard_disjunction = proof_content.get("case_guard_disjunction")
    if not isinstance(case_guard_disjunction, Mapping):
        return False
    status = cls._evidence_text(case_guard_disjunction, "status")
    if status not in {"complete", "completed", "proven"}:
        return False
    normalized_guard_formula = proof_content.get("normalized_guard_formula")
    if not isinstance(normalized_guard_formula, Mapping):
        return False
    normalized_status = cls._evidence_text(normalized_guard_formula, "status")
    if normalized_status not in {"complete", "completed", "proven"}:
        return False
    normalized_query = normalized_guard_formula.get("query")
    if not isinstance(normalized_query, str) or not normalized_query:
        return False
    if not cls._return_coverage_guard_evidence_is_complete(proof_content, normalized_query):
        return False
    if reason_id == UnknownReasonId.RETURN_COVERAGE_INCONCLUSIVE:
        if not cls._return_coverage_proof_content_can_discharge_inconclusive(proof_content):
            return False
    else:
        solver_evidence = proof_content.get("solver_model_or_timeout")
        if isinstance(solver_evidence, Mapping):
            solver_status = cls._evidence_text(solver_evidence, "status")
            if solver_status in {"unknown", "timeout", "error", "inconclusive"}:
                return False
    return True

def _impl__return_coverage_normalization_required(
    cls,
    evidence: Mapping[str, Any],
    proof_content: Mapping[str, Any],
    object_target_key: Any,
) -> bool:
    if cls._evidence_bool(evidence, "normalization_required") or bool(
        proof_content.get("normalization_required")
    ):
        return True
    if cls._nested_contains_tag(object_target_key, "normalization_policy_digest"):
        return True
    for key in (
        "normalized_guard_payload",
        "normalized_value_payload",
        "normalized_address_payload",
        "raw_normalized_correspondence",
    ):
        if key in proof_content:
            return True
    return False

def _impl__return_coverage_normalization_proof_content_is_complete(
    cls,
    proof_content: Mapping[str, Any],
    object_target_key: Any,
    *,
    required: bool,
) -> bool:
    policy = proof_content.get("normalization_policy")
    policy_digest = proof_content.get("normalization_policy_digest")
    if not isinstance(policy, Mapping) or not isinstance(policy_digest, str) or not policy_digest:
        return not required
    if cls._return_coverage_normalization_policy_digest(policy) != policy_digest:
        return False
    target_digest = cls._normalization_policy_digest_from_target(object_target_key)
    if target_digest is not None and target_digest != policy_digest:
        return False
    correspondence = proof_content.get("raw_normalized_correspondence")
    if not isinstance(correspondence, Mapping):
        return not required
    if cls._evidence_text(correspondence, "status") not in {"complete", "completed", "proven"}:
        return False
    if correspondence.get("normalization_policy_digest") != policy_digest:
        return False
    raw_identity = cls._normalize_nested_tuple(correspondence.get("raw_guard_identity"))
    normalized_identity = cls._normalize_nested_tuple(correspondence.get("normalized_guard_identity"))
    before_key = cls._normalize_nested_tuple(correspondence.get("before_structural_key"))
    after_key = cls._normalize_nested_tuple(correspondence.get("after_structural_key"))
    if raw_identity is None or normalized_identity is None or before_key is None or after_key is None:
        return False
    if not correspondence.get("rule_id"):
        return False
    equivalence_proof = correspondence.get("equivalence_proof")
    if not isinstance(equivalence_proof, Mapping):
        return False
    if cls._evidence_text(equivalence_proof, "status") not in {"complete", "completed", "proven", "unsat"}:
        return False
    normalized_guard_formula = proof_content.get("normalized_guard_formula")
    if not isinstance(normalized_guard_formula, Mapping):
        return False
    query = normalized_guard_formula.get("query")
    if not isinstance(query, str) or not query:
        return False
    expected_query_hash = hashlib.sha256(query.encode("utf-8")).hexdigest()
    payloads: List[Tuple[str, Mapping[str, Any]]] = []
    for kind, key in (
        ("guard", "normalized_guard_payload"),
        ("value", "normalized_value_payload"),
        ("address", "normalized_address_payload"),
    ):
        payload = proof_content.get(key)
        if payload is None:
            continue
        if not isinstance(payload, Mapping):
            return False
        payloads.append((kind, payload))
    if not payloads:
        return not required
    for kind, payload in payloads:
        if not cls._return_coverage_normalized_payload_is_complete(
            kind,
            payload,
            policy_digest=policy_digest,
            expected_query_hash=expected_query_hash,
            correspondence=correspondence,
            default_raw_identity=raw_identity,
            default_normalized_identity=normalized_identity,
        ):
            return False
    return True

def _impl__return_coverage_normalized_payload_is_complete(
    cls,
    kind: str,
    payload: Mapping[str, Any],
    *,
    policy_digest: str,
    expected_query_hash: str,
    correspondence: Mapping[str, Any],
    default_raw_identity: Any,
    default_normalized_identity: Any,
) -> bool:
    if payload.get("normalization_policy_digest") != policy_digest:
        return False
    payload_raw = cls._normalize_nested_tuple(payload.get("raw_identity"))
    payload_normalized = cls._normalize_nested_tuple(payload.get("normalized_identity"))
    if payload_raw is None or payload_normalized is None:
        return False
    expected_raw = cls._normalize_nested_tuple(correspondence.get(f"raw_{kind}_identity"))
    expected_normalized = cls._normalize_nested_tuple(
        correspondence.get(f"normalized_{kind}_identity")
    )
    if kind == "guard":
        expected_raw = expected_raw if expected_raw is not None else default_raw_identity
        expected_normalized = (
            expected_normalized
            if expected_normalized is not None
            else default_normalized_identity
        )
    elif expected_raw is None or expected_normalized is None:
        return False
    if expected_raw is not None and payload_raw != expected_raw:
        return False
    if expected_normalized is not None and payload_normalized != expected_normalized:
        return False
    final_hash = payload.get("final_query_sha256")
    if not isinstance(final_hash, str) or not final_hash:
        return False
    return final_hash == expected_query_hash

def _impl__return_coverage_structural_proof_content_is_complete(
    cls,
    proof_content: Mapping[str, Any],
) -> bool:
    guard_keys = proof_content.get("structural_guard_keys")
    miss_keys = proof_content.get("structural_miss_formula_keys")
    solver_evidence = proof_content.get("coverage_solver_evidence")
    bit_width_metadata = proof_content.get("bit_width_signedness_metadata")
    if not isinstance(guard_keys, Mapping) or cls._evidence_text(guard_keys, "status") != "complete":
        return False
    if not isinstance(miss_keys, Mapping) or cls._evidence_text(miss_keys, "status") != "complete":
        return False
    if not isinstance(solver_evidence, Mapping):
        return False
    solver_status = cls._evidence_text(solver_evidence, "status")
    proof_method = cls._evidence_text(solver_evidence, "proof_method")
    if solver_status != "unsat" and not (
        solver_status == "not_applicable"
        and proof_method in {"unconditional_return_case", "object_centric_total_coverage"}
    ):
        return False
    if not isinstance(bit_width_metadata, Mapping):
        return False
    if cls._evidence_text(bit_width_metadata, "status") != "complete":
        return False
    guard_key_values = cls._normalize_nested_tuple(guard_keys.get("keys"))
    miss_key_values = cls._normalize_nested_tuple(miss_keys.get("keys"))
    if not isinstance(guard_key_values, tuple) or not guard_key_values:
        return False
    if not isinstance(miss_key_values, tuple) or not miss_key_values:
        return False
    if cls._evidence_has_any_recursive(
        {
            "structural_guard_keys": guard_key_values,
            "structural_miss_formula_keys": miss_key_values,
        },
        cls._COMPLETED_PROOF_BLOCKER_FIELDS,
    ):
        return False
    return True

def _impl__return_coverage_structural_proof_content_matches_target(
    cls,
    proof_content: Mapping[str, Any],
    object_target_key: Any,
) -> bool:
    if not cls._return_coverage_object_target_key_is_valid(object_target_key):
        return False
    target_partition_cases = cls._return_coverage_target_partition_cases(object_target_key)
    if target_partition_cases is None:
        return False
    expected_guard_entries: List[Tuple[Any, ...]] = []
    expected_miss_entries: List[Tuple[Any, ...]] = []
    for case in target_partition_cases:
        fields = {
            field[0]: field[1]
            for field in case[1:]
            if isinstance(field, tuple) and len(field) == 2 and isinstance(field[0], str)
        }
        if "guards" not in fields or "return_value" not in fields or "case_miss_formula" not in fields:
            return False
        expected_guard_entries.append(
            (
                "return_case_guard_set",
                ("guard_structural_keys", cls._normalize_nested_tuple(fields["guards"])),
                ("return_value_structural_key", cls._normalize_nested_tuple(fields["return_value"])),
            )
        )
        expected_miss_entries.append(
            (
                "case_miss_formula",
                cls._normalize_nested_tuple(fields["case_miss_formula"]),
            )
        )

    guard_keys = proof_content.get("structural_guard_keys")
    miss_keys = proof_content.get("structural_miss_formula_keys")
    if not isinstance(guard_keys, Mapping) or not isinstance(miss_keys, Mapping):
        return False
    actual_guard_entries = []
    for entry in cls._normalize_nested_tuple(guard_keys.get("keys")) or ():
        if not isinstance(entry, tuple) or len(entry) < 4 or entry[0] != "return_case_guard_set":
            return False
        fields = {
            field[0]: field[1]
            for field in entry[2:]
            if isinstance(field, tuple) and len(field) == 2 and isinstance(field[0], str)
        }
        if "guard_structural_keys" not in fields or "return_value_structural_key" not in fields:
            return False
        actual_guard_entries.append(
            (
                "return_case_guard_set",
                ("guard_structural_keys", cls._normalize_nested_tuple(fields["guard_structural_keys"])),
                ("return_value_structural_key", cls._normalize_nested_tuple(fields["return_value_structural_key"])),
            )
        )
    actual_miss_entries = []
    for entry in cls._normalize_nested_tuple(miss_keys.get("keys")) or ():
        if not isinstance(entry, tuple) or len(entry) < 3 or entry[0] != "case_miss_formula":
            return False
        actual_miss_entries.append(
            (
                "case_miss_formula",
                cls._normalize_nested_tuple(entry[2]),
            )
        )
    return (
        cls._canonicalize_key_sequence(expected_guard_entries)
        == cls._canonicalize_key_sequence(actual_guard_entries)
        and cls._canonicalize_key_sequence(expected_miss_entries)
        == cls._canonicalize_key_sequence(actual_miss_entries)
    )

def _impl__return_coverage_target_partition_cases(object_target_key: Any) -> Optional[Tuple[Any, ...]]:
    if not isinstance(object_target_key, tuple) or len(object_target_key) < 7:
        return None
    partition = object_target_key[6]
    if not isinstance(partition, tuple) or len(partition) < 3:
        return None
    if partition[0] != "return_partition_identity":
        return None
    cases = partition[2]
    if not isinstance(cases, tuple):
        return None
    for case in cases:
        if not isinstance(case, tuple) or not case or case[0] != "return_case_identity":
            return None
    return cases

def _impl__return_coverage_proof_id_from_evidence(cls, evidence: Any) -> Optional[Tuple[Any, ...]]:
    if not cls._evidence_bool(evidence, "object_derived"):
        return None
    if cls._evidence_text(evidence, "status") not in {"complete", "completed", "proven"}:
        return None
    reason_id = cls._evidence_text(evidence, "reason_id")
    if reason_id not in {
        UnknownReasonId.RETURN_COVERAGE_GAP.value,
        UnknownReasonId.RETURN_COVERAGE_INCONCLUSIVE.value,
    }:
        return None
    canonical_reason_id = None
    try:
        canonical_reason_id = UnknownReasonId(reason_id)
    except ValueError:
        canonical_reason_id = None
    proof_kind = cls._evidence_text(evidence, "recovery_proof_kind")
    if proof_kind != UnknownRecoveryProofKind.RETURN_COVERAGE_COMPLETION.value:
        return None
    proof_stage = cls._evidence_text(evidence, "proof_stage")
    requirements = (
        cls._RETURN_COVERAGE_COMPLETION_REQUIREMENTS.get(canonical_reason_id)
        if canonical_reason_id is not None
        else None
    )
    if not requirements:
        return None
    allowed_stages = {proof_stage_ for proof_stage_, _ in requirements}
    if proof_stage not in allowed_stages:
        return None
    evidence_kind = cls._evidence_text(evidence, "evidence_kind")
    if not evidence_kind:
        return None
    if cls._evidence_has_any(evidence, cls._COMPLETED_PROOF_BLOCKER_FIELDS):
        return None
    object_target_key = cls._normalize_nested_tuple(cls._evidence_get(evidence, "object_target_key"))
    if not isinstance(object_target_key, tuple):
        return None
    if not cls._return_coverage_object_target_key_is_valid(object_target_key):
        return None
    proof_id = build_proof_obligation_id(
        reason_id,
        proof_stage,
        proof_kind,
        evidence_kind,
        object_target_key,
    )
    provided_id = cls._normalize_nested_tuple(cls._evidence_get(evidence, "proof_obligation_id"))
    if provided_id is None or provided_id != proof_id:
        return None
    if not cls._return_coverage_proof_content_is_complete(evidence, canonical_reason_id):
        return None
    return proof_id

def _impl__return_coverage_object_target_key_is_valid(cls, object_target_key: Tuple[Any, ...]) -> bool:
    if not isinstance(object_target_key, tuple) or len(object_target_key) < 8:
        return False
    if object_target_key[0] != "return_coverage":
        return False
    schema = object_target_key[1]
    if not (
        isinstance(schema, tuple)
        and len(schema) == 2
        and schema[0] == "target_schema_version"
        and schema[1] == cls._RETURN_COVERAGE_TARGET_SCHEMA_VERSION
    ):
        return False
    if object_target_key[2] not in {"function1", "function2"}:
        return False
    if not isinstance(object_target_key[3], tuple) or object_target_key[3][0] != "function_identity":
        return False
    if object_target_key[4] not in {"return_coverage_gap", "return_coverage_inconclusive"}:
        return False
    if not isinstance(object_target_key[6], tuple) or object_target_key[6][0] != "return_partition_identity":
        return False
    if not isinstance(object_target_key[7], tuple) or object_target_key[7][0] != "guard_disjunction_identity":
        return False
    return not cls._return_coverage_identity_contains_forbidden_atoms(object_target_key)

def _impl__return_coverage_identity_contains_forbidden_atoms(cls, value: Any) -> bool:
    if isinstance(value, Mapping):
        return True
    if isinstance(value, (list, set, frozenset)):
        return True
    if isinstance(value, tuple):
        if value and value[0] in {"object_id", "program_uid", "opaque"}:
            return True
        if len(value) == 2 and value[0] == "int" and isinstance(value[1], int) and value[1] < 0:
            return False
        return any(cls._return_coverage_identity_contains_forbidden_atoms(item) for item in value)
    if value is None or isinstance(value, str) or isinstance(value, bool):
        return False
    if isinstance(value, int) and not isinstance(value, bool):
        return False
    return True

def _impl__return_coverage_object_target_key(
    self,
    blocking_reason: str,
    analysis1: FunctionReturnAnalysis,
    analysis2: FunctionReturnAnalysis,
) -> Optional[Tuple[Any, ...]]:
    label, _reason_text = self._split_blocking_reason(blocking_reason)
    reason_kind = self._blocking_reason_kind(blocking_reason)
    if reason_kind not in {"return_coverage_gap", "return_coverage_inconclusive"}:
        return None
    analysis = analysis1 if label == "function1" else analysis2 if label == "function2" else None
    if analysis is None:
        return None
    target = (
        "return_coverage",
        ("target_schema_version", self._RETURN_COVERAGE_TARGET_SCHEMA_VERSION),
        label,
        self._deterministic_function_identity(analysis),
        reason_kind,
        self._return_storage_object_key(analysis),
        self._return_coverage_partition_identity_key(analysis),
        self._return_coverage_guard_disjunction_identity_key(analysis),
    )
    return self._identity_freeze(
        self._artifact_stable_key_for_analysis(
            self._identity_freeze(target),
            analysis,
        )
    )

def _impl__outcome_partition_unknown_object_target_key(
    self,
    blocking_reason: str,
    analysis1: FunctionReturnAnalysis,
    analysis2: FunctionReturnAnalysis,
) -> Optional[Tuple[Any, ...]]:
    label, _reason_text = self._split_blocking_reason(blocking_reason)
    reason_kind = self._blocking_reason_kind(blocking_reason)
    if reason_kind != "outcome_partition_unknown":
        return None
    analysis = analysis1 if label == "function1" else analysis2 if label == "function2" else None
    if analysis is None:
        return None
    target = (
        "outcome_partition_unknown",
        ("target_schema_version", 1),
        label,
        self._deterministic_function_identity(analysis),
        self._return_storage_object_key(analysis),
        self._outcome_partition_identity_key(analysis),
        self._unknown_outcome_identity_key(analysis),
    )
    return self._identity_freeze(
        self._artifact_stable_key_for_analysis(
            self._identity_freeze(target),
            analysis,
        )
    )

def _impl__outcome_partition_unknown_object_evidence(
    self,
    blocking_reason: str,
    analysis1: FunctionReturnAnalysis,
    analysis2: FunctionReturnAnalysis,
) -> Optional[Dict[str, Any]]:
    label, _reason_text = self._split_blocking_reason(blocking_reason)
    analysis = analysis1 if label == "function1" else analysis2 if label == "function2" else None
    if analysis is None:
        return None
    return {
        "object_derived": True,
        "evidence_version": 1,
        "evidence_kind": "outcome_partition",
        "blocker_reason": blocking_reason,
        "side": label,
        "analysis_key": self._analysis_entry_key(analysis),
        "return_storage": self._return_storage_object_key(analysis),
        "outcome_partition": self._outcome_partition_identity_key(analysis),
        "unknown_outcomes": self._unknown_outcome_identity_key(analysis),
    }

def _impl__return_case_partition_member_object_key(
    self,
    case: Any,
    return_info: Any,
) -> Tuple[Any, ...]:
    case_index = getattr(case, "index", None)
    try:
        normalized_case_index = int(case_index)
    except (TypeError, ValueError):
        normalized_case_index = None
    source_indices = []
    for source_index in getattr(case, "source_indices", ()) or ():
        try:
            source_indices.append(int(source_index))
        except (TypeError, ValueError):
            continue
    return (
        "return_case_partition_member",
        normalized_case_index,
        tuple(source_indices),
        self._return_case_object_key(
            normalized_case_index if normalized_case_index is not None else -1,
            return_info,
        )
        if return_info is not None
        else None,
        (
            "comparison_surface",
            getattr(getattr(case, "comparison_surface", None), "kind", None),
            getattr(getattr(case, "comparison_surface", None), "explicit_bit_width", None),
            getattr(getattr(case, "comparison_surface", None), "use_sign_extension", None),
        ),
        ("value", self._expression_runtime_object_key(getattr(case, "value_expr", None))),
    )

def _impl__return_partition_object_key(self, analysis: FunctionReturnAnalysis) -> Tuple[Any, ...]:
    return (
        "return_partition",
        tuple(
            self._return_case_object_key(index, return_info)
            for index, return_info in enumerate(getattr(analysis, "returns", ()) or ())
        ),
    )

def _impl__return_coverage_partition_identity_key(self, analysis: FunctionReturnAnalysis) -> Tuple[Any, ...]:
    cases = tuple(
        self._return_coverage_case_identity_key(return_info)
        for return_info in (getattr(analysis, "returns", ()) or ())
    )
    return (
        "return_partition_identity",
        ("normalization_schema_version", self._RETURN_COVERAGE_NORMALIZATION_SCHEMA_VERSION),
        self._canonicalize_key_sequence(cases),
    )

def _impl__return_coverage_case_identity_key(self, return_info: Any) -> Tuple[Any, ...]:
    pcode_op_ref = getattr(return_info, "pcode_op_ref", None)
    value = getattr(return_info, "value", None)
    conditions = tuple(getattr(return_info, "conditions", None) or ())
    miss_expr = self._case_miss_expression(list(conditions))
    return (
        "return_case_identity",
        ("site", self._identity_freeze(getattr(return_info, "address", None))),
        ("pcode_sequence", self._identity_freeze(self._stable_key_or_none(pcode_op_ref))),
        ("pcode_identity", self._identity_freeze(getattr(return_info, "pcode_identity", None))),
        ("pcode_order", self._identity_freeze(getattr(return_info, "pcode_order", None))),
        ("pcode_time", self._identity_freeze(getattr(return_info, "pcode_time", None))),
        ("return_value", self._expression_runtime_object_key(value)),
        (
            "case_miss_formula",
            self._expression_runtime_object_key(miss_expr) if miss_expr is not None else None,
        ),
        (
            "guards",
            self._canonicalize_key_sequence(
                tuple(
                    self._return_condition_object_key(condition)
                    for condition in conditions
                )
            ),
        ),
        ("bit_width", self._expression_smt_bit_width_for_object_key(value)),
    )

def _impl__return_coverage_guard_disjunction_identity_key(self, analysis: FunctionReturnAnalysis) -> Tuple[Any, ...]:
    guard_sets = tuple(
        (
            "return_case_guard_identity",
            self._canonicalize_key_sequence(
                tuple(
                    self._return_condition_object_key(condition)
                    for condition in (getattr(return_info, "conditions", None) or ())
                )
            ),
        )
        for return_info in (getattr(analysis, "returns", ()) or ())
    )
    return (
        "guard_disjunction_identity",
        ("normalization_schema_version", self._RETURN_COVERAGE_NORMALIZATION_SCHEMA_VERSION),
        self._canonicalize_key_sequence(guard_sets),
    )

def _impl__outcome_partition_identity_key(self, analysis: FunctionReturnAnalysis) -> Tuple[Any, ...]:
    return_outcomes = tuple(getattr(analysis, "return_outcomes", ()) or ())
    divergence_outcomes = tuple(getattr(analysis, "divergence_outcomes", ()) or ())
    unknown_outcomes = tuple(getattr(analysis, "unknown_outcomes", ()) or ())
    return_keys = tuple(
        (
            "return",
            index,
            self._canonicalize_key_sequence(
                tuple(self._return_condition_object_key(condition) for condition in (getattr(outcome, "guard", ()) or ()))
            ),
            self._expression_runtime_object_key(getattr(outcome, "value", None)),
            self._identity_freeze(getattr(outcome, "provenance", None)),
        )
        for index, outcome in enumerate(return_outcomes)
    )
    divergence_keys = tuple(
        (
            "divergence",
            index,
            self._canonicalize_key_sequence(
                tuple(self._return_condition_object_key(condition) for condition in (getattr(outcome, "guard", ()) or ()))
            ),
            self._identity_freeze(getattr(outcome, "proof", None)),
        )
        for index, outcome in enumerate(divergence_outcomes)
    )
    unknown_keys = tuple(
        self._unknown_outcome_member_identity_key(index, outcome)
        for index, outcome in enumerate(unknown_outcomes)
    )
    return (
        "outcome_partition_identity",
        ("normalization_schema_version", self._RETURN_COVERAGE_NORMALIZATION_SCHEMA_VERSION),
        self._canonicalize_key_sequence(return_keys),
        self._canonicalize_key_sequence(divergence_keys),
        self._canonicalize_key_sequence(unknown_keys),
    )

def _impl__unknown_outcome_identity_key(self, analysis: FunctionReturnAnalysis) -> Tuple[Any, ...]:
    return (
        "unknown_outcomes",
        self._canonicalize_key_sequence(
            tuple(
                self._unknown_outcome_member_identity_key(index, outcome)
                for index, outcome in enumerate(getattr(analysis, "unknown_outcomes", ()) or ())
            )
        ),
    )

def _impl__unknown_outcome_member_identity_key(self, index: int, outcome: Any) -> Tuple[Any, ...]:
    return (
        "unknown_outcome",
        int(index),
        ("reason", str(getattr(outcome, "reason", "") or "")),
        (
            "guard",
            self._canonicalize_key_sequence(
                tuple(self._return_condition_object_key(condition) for condition in (getattr(outcome, "guard", ()) or ()))
            ),
        ),
        ("evidence", self._identity_freeze(getattr(outcome, "evidence", None))),
    )

def _impl__outcome_partition_covered_labels(
    self,
    base_ctx: Mapping[str, Any],
    analysis1: Optional[FunctionReturnAnalysis],
    analysis2: Optional[FunctionReturnAnalysis],
    param_replace_fn1,
    param_replace_fn2,
) -> Set[str]:
    if analysis1 is None or analysis2 is None:
        return set()
    if not self._analysis_has_proved_outcome_partition(
        base_ctx,
        analysis1,
        param_replace_fn1,
        "function1",
    ):
        self._debug_print("Outcome partition coverage declined: function1 partition is not proved total")
        return set()
    if not self._analysis_has_proved_outcome_partition(
        base_ctx,
        analysis2,
        param_replace_fn2,
        "function2",
    ):
        self._debug_print("Outcome partition coverage declined: function2 partition is not proved total")
        return set()
    if not self._outcome_partitions_are_equivalent(
        base_ctx,
        analysis1,
        analysis2,
        param_replace_fn1,
        param_replace_fn2,
    ):
        self._debug_print("Outcome partition coverage declined: partitions are not equivalent")
        return set()
    return {"function1", "function2"}

def _impl__outcome_partition_inconclusive_labels(
    self,
    base_ctx: Mapping[str, Any],
    analysis1: Optional[FunctionReturnAnalysis],
    analysis2: Optional[FunctionReturnAnalysis],
    param_replace_fn1,
    param_replace_fn2,
) -> Set[str]:
    labels: Set[str] = set()
    for label, analysis, replace_fn in (
        ("function1", analysis1, param_replace_fn1),
        ("function2", analysis2, param_replace_fn2),
    ):
        if analysis is None:
            continue
        if not getattr(analysis, "unknown_outcomes", ()) or ():
            continue
        if self._analysis_has_total_outcome_partition(
            base_ctx,
            analysis,
            replace_fn,
            label,
        ):
            labels.add(label)
    return labels

def _impl__analysis_has_total_outcome_partition(
    self,
    base_ctx: Mapping[str, Any],
    analysis: FunctionReturnAnalysis,
    replace_fn,
    label: str,
) -> bool:
    return_outcomes = tuple(getattr(analysis, "return_outcomes", ()) or ())
    divergence_outcomes = tuple(getattr(analysis, "divergence_outcomes", ()) or ())
    unknown_outcomes = tuple(getattr(analysis, "unknown_outcomes", ()) or ())
    outcome_guards = [
        tuple(getattr(outcome, "guard", ()) or ())
        for outcome in (*return_outcomes, *divergence_outcomes, *unknown_outcomes)
    ]
    if not outcome_guards:
        return False
    return self._outcome_guard_union_is_total(
        base_ctx,
        outcome_guards,
        replace_fn,
        label,
    )

def _impl__analysis_has_proved_outcome_partition(
    self,
    base_ctx: Mapping[str, Any],
    analysis: FunctionReturnAnalysis,
    replace_fn,
    label: str,
) -> bool:
    if getattr(analysis, "unknown_outcomes", ()) or ():
        return False
    return_outcomes = tuple(getattr(analysis, "return_outcomes", ()) or ())
    divergence_outcomes = tuple(getattr(analysis, "divergence_outcomes", ()) or ())
    if not divergence_outcomes:
        return False
    return self._outcome_guard_union_is_total(
        base_ctx,
        [tuple(getattr(outcome, "guard", ()) or ()) for outcome in (*return_outcomes, *divergence_outcomes)],
        replace_fn,
        label,
    )

def _impl__outcome_partitions_are_equivalent(
    self,
    base_ctx: Mapping[str, Any],
    analysis1: FunctionReturnAnalysis,
    analysis2: FunctionReturnAnalysis,
    param_replace_fn1,
    param_replace_fn2,
) -> bool:
    divergence1 = tuple(getattr(analysis1, "divergence_outcomes", ()) or ())
    divergence2 = tuple(getattr(analysis2, "divergence_outcomes", ()) or ())
    returns1 = tuple(getattr(analysis1, "return_outcomes", ()) or ())
    returns2 = tuple(getattr(analysis2, "return_outcomes", ()) or ())
    if not divergence1 or not divergence2:
        self._debug_print("Outcome partition equivalence declined: missing divergence outcomes")
        return False
    if not self._outcome_guard_unions_equivalent(
        base_ctx,
        [tuple(getattr(outcome, "guard", ()) or ()) for outcome in divergence1],
        [tuple(getattr(outcome, "guard", ()) or ()) for outcome in divergence2],
        param_replace_fn1,
        param_replace_fn2,
    ):
        self._debug_print("Outcome partition equivalence declined: divergence guard unions differ")
        return False
    if not self._outcome_cross_kind_disjoint(
        base_ctx,
        returns1,
        divergence2,
        param_replace_fn1,
        param_replace_fn2,
    ):
        self._debug_print("Outcome partition equivalence declined: function1 returns overlap function2 divergence")
        return False
    if not self._outcome_cross_kind_disjoint(
        base_ctx,
        returns2,
        divergence1,
        param_replace_fn2,
        param_replace_fn1,
    ):
        self._debug_print("Outcome partition equivalence declined: function2 returns overlap function1 divergence")
        return False
    if not self._return_outcome_values_are_equivalent(
        base_ctx,
        returns1,
        returns2,
        param_replace_fn1,
        param_replace_fn2,
    ):
        self._debug_print("Outcome partition equivalence declined: return outcome values differ")
        return False
    return True

def _impl__return_outcome_values_are_equivalent(
    self,
    base_ctx: Mapping[str, Any],
    returns1: Sequence[Any],
    returns2: Sequence[Any],
    param_replace_fn1,
    param_replace_fn2,
) -> bool:
    for left in returns1 or ():
        left_guard = tuple(getattr(left, "guard", ()) or ())
        left_value = getattr(left, "value", None)
        if left_value is None:
            return False
        for right in returns2 or ():
            right_guard = tuple(getattr(right, "guard", ()) or ())
            right_value = getattr(right, "value", None)
            if right_value is None:
                return False
            if self._outcome_condition_groups_are_unsat(
                base_ctx,
                ((left_guard, param_replace_fn1), (right_guard, param_replace_fn2)),
                title="Outcome return guard overlap",
            ):
                continue
            if not self._outcome_return_values_equal_under_guards(
                base_ctx,
                left_guard,
                right_guard,
                left_value,
                right_value,
                param_replace_fn1,
                param_replace_fn2,
            ):
                return False
    return True

def _impl__outcome_cross_kind_disjoint(
    self,
    base_ctx: Mapping[str, Any],
    return_outcomes: Sequence[Any],
    divergence_outcomes: Sequence[Any],
    return_replace_fn,
    divergence_replace_fn,
) -> bool:
    for ret in return_outcomes or ():
        ret_guard = tuple(getattr(ret, "guard", ()) or ())
        for divergence in divergence_outcomes or ():
            div_guard = tuple(getattr(divergence, "guard", ()) or ())
            if not self._outcome_condition_groups_are_unsat(
                base_ctx,
                ((ret_guard, return_replace_fn), (div_guard, divergence_replace_fn)),
                title="Outcome return/divergence disjointness",
            ):
                return False
    return True

def _impl__outcome_guard_unions_equivalent(
    self,
    base_ctx: Mapping[str, Any],
    left_guards: Sequence[Sequence[Condition]],
    right_guards: Sequence[Sequence[Condition]],
    left_replace_fn,
    right_replace_fn,
) -> bool:
    left_union = self._outcome_guard_union_smt(left_guards, left_replace_fn)
    right_union = self._outcome_guard_union_smt(right_guards, right_replace_fn)
    if left_union is None or right_union is None:
        return False

    left_implies_right = self._outcome_smt_assertions_are_unsat(
        base_ctx,
        [left_union, f"(not {right_union})"],
        title="Outcome divergence guard implication left-to-right",
    )
    right_implies_left = self._outcome_smt_assertions_are_unsat(
        base_ctx,
        [right_union, f"(not {left_union})"],
        title="Outcome divergence guard implication right-to-left",
    )
    return left_implies_right and right_implies_left

def _impl__outcome_guard_union_is_total(
    self,
    base_ctx: Mapping[str, Any],
    guard_sets: Sequence[Sequence[Condition]],
    replace_fn,
    label: str,
) -> bool:
    union = self._outcome_guard_union_smt(guard_sets, replace_fn)
    if union is None:
        return False
    return self._outcome_smt_assertions_are_unsat(
        base_ctx,
        [f"(not {union})"],
        title=f"Outcome partition total coverage: {label}",
    )

def _impl__outcome_condition_groups_are_unsat(
    self,
    base_ctx: Mapping[str, Any],
    condition_groups: Sequence[Tuple[Sequence[Condition], Any]],
    *,
    title: str,
) -> bool:
    assertions: List[str] = []
    for conditions, replace_fn in condition_groups:
        rendered = self._outcome_conditions_smt(conditions, replace_fn)
        if rendered is None:
            return False
        assertions.extend(rendered)
    return self._outcome_smt_assertions_are_unsat(base_ctx, assertions, title=title)

def _impl__outcome_return_values_equal_under_guards(
    self,
    base_ctx: Mapping[str, Any],
    left_guard: Sequence[Condition],
    right_guard: Sequence[Condition],
    left_value: Expression,
    right_value: Expression,
    left_replace_fn,
    right_replace_fn,
) -> bool:
    left_conditions = self._outcome_conditions_smt(left_guard, left_replace_fn)
    right_conditions = self._outcome_conditions_smt(right_guard, right_replace_fn)
    if left_conditions is None or right_conditions is None:
        return False
    left_smt = self._outcome_expression_smt(left_value, left_replace_fn)
    right_smt = self._outcome_expression_smt(right_value, right_replace_fn)
    if left_smt is None or right_smt is None:
        return False
    left_bits = int(expression_smt_bit_width(left_value) or 0)
    right_bits = int(expression_smt_bit_width(right_value) or 0)
    if left_bits <= 0 or right_bits <= 0:
        return False
    target_bits = max(left_bits, right_bits)
    left_smt = coerce_value_to_bitvec_width(left_value, left_smt, target_bits)
    right_smt = coerce_value_to_bitvec_width(right_value, right_smt, target_bits)
    return self._outcome_smt_assertions_are_unsat(
        base_ctx,
        [*left_conditions, *right_conditions, f"(not (= {left_smt} {right_smt}))"],
        title="Outcome return value equality",
    )

def _impl__outcome_guard_union_smt(
    self,
    guard_sets: Sequence[Sequence[Condition]],
    replace_fn,
) -> Optional[str]:
    disjuncts: List[str] = []
    for guards in guard_sets or ():
        rendered = self._outcome_conditions_smt(guards, replace_fn)
        if rendered is None:
            return None
        if not rendered:
            return "true"
        if len(rendered) == 1:
            disjuncts.append(rendered[0])
        else:
            disjuncts.append(f"(and {' '.join(rendered)})")
    if not disjuncts:
        return None
    if len(disjuncts) == 1:
        return disjuncts[0]
    return f"(or {' '.join(disjuncts)})"

def _impl__outcome_conditions_smt(
    self,
    conditions: Sequence[Condition],
    replace_fn,
) -> Optional[List[str]]:
    rendered: List[str] = []
    for condition in conditions or ():
        smt = self._outcome_condition_smt(condition, replace_fn)
        if smt is None:
            return None
        rendered.append(smt)
    return rendered

def _impl__outcome_condition_smt(self, condition: Condition, replace_fn) -> Optional[str]:
    try:
        if replace_fn is None:
            return condition.to_smt(float_mode="fp")
        return replace_fn(condition)
    except TypeError:
        try:
            return replace_fn(condition.to_smt(float_mode="fp"))
        except Exception:
            return None
    except Exception:
        return None

def _impl__outcome_expression_smt(self, expression: Expression, replace_fn) -> Optional[str]:
    try:
        if replace_fn is None:
            return expression.to_smt(float_mode="fp")
        return replace_fn(expression)
    except TypeError:
        try:
            return replace_fn(expression.to_smt(float_mode="fp"))
        except Exception:
            return None
    except Exception:
        return None

def _impl__outcome_smt_assertions_are_unsat(
    self,
    base_ctx: Mapping[str, Any],
    assertions: Sequence[str],
    *,
    title: str,
) -> bool:
    header_lines = list(base_ctx.get("header_lines", []) or []) if isinstance(base_ctx, Mapping) else []
    if not header_lines:
        return False
    if not assertions:
        return False
    normalized_assertions = self._normalize_zero_constant_widths_for_declared_symbols(
        assertions,
        header_lines,
    )
    query = "\n".join(
        [
            f"; {title}",
            *header_lines,
            *(f"(assert {assertion})" for assertion in normalized_assertions),
            "(check-sat)",
            "(get-model)",
        ]
    )
    result = self.solver_runner.run_sequential(query)
    return result.is_equivalent is True

def _impl__check_return_case_coverage_gap(
    self,
    base_ctx: Dict[str, Any],
    cases: Sequence[Any],
    param_replace_fn,
    label: str,
) -> ReturnCoverageCheckResult:
    if not cases:
        return ReturnCoverageCheckResult(
            status="gap",
            detail=f"{label} has no return cases after extraction",
        )
    if any(not getattr(case, "conditions", None) for case in cases):
        return ReturnCoverageCheckResult(
            status="covered",
            coverage_proof_method="unconditional_return_case",
        )
    object_centric_status = self._return_cases_have_object_centric_total_coverage(
        cases
    )
    if object_centric_status is True:
        return ReturnCoverageCheckResult(
            status="covered",
            coverage_proof_method="object_centric_total_coverage",
        )
    if object_centric_status is False and not self._base_context_has_return_coverage_domain_assumptions(base_ctx):
        return ReturnCoverageCheckResult(
            status="gap",
            detail=f"{label} object-centric return-case coverage check found uncovered region",
        )
    if object_centric_status is None:
        case_conditions = [
            cond
            for case in (cases or ())
            for cond in (getattr(case, "conditions", None) or ())
        ]
        if not ConditionSMTOracle.has_object_identity_support(case_conditions):
            return ReturnCoverageCheckResult(
                status="inconclusive",
                reason_id=UnknownReasonId.RETURN_COVERAGE_INCONCLUSIVE,
                detail=f"{label} return-case object-centric coverage check was inconclusive",
                inconclusive_cause="object_identity_unsupported",
            )
    if not base_ctx.get("header_lines"):
        return ReturnCoverageCheckResult(
            status="inconclusive",
            reason_id=UnknownReasonId.RETURN_COVERAGE_INCONCLUSIVE,
            detail=f"{label} return-case coverage query skipped: base context has no declarations",
            inconclusive_cause="missing_header_context",
        )
    if any(self._case_conditions_contain_unresolved_expression(case) for case in cases):
        return ReturnCoverageCheckResult(
            status="inconclusive",
            reason_id=UnknownReasonId.RETURN_COVERAGE_INCONCLUSIVE,
            detail=f"{label} return-case coverage query skipped: unresolved condition expression",
            inconclusive_cause="unresolved_expression",
        )

    query = self._build_return_case_coverage_query(
        base_ctx,
        cases,
        param_replace_fn,
        label,
    )
    if query is None:
        return ReturnCoverageCheckResult(
            status="inconclusive",
            reason_id=UnknownReasonId.RETURN_COVERAGE_INCONCLUSIVE,
            detail=f"{label} return-case coverage query could not be built",
            inconclusive_cause="unsupported_expression",
        )

    result = self.solver_runner.run_sequential(query)
    if result.is_equivalent is False:
        model = result.get_counterexample()
        detail = f"{label} has uncovered return-condition region"
        if model:
            detail += f" under model {model}"
        if getattr(self, "debug", False):
            detail += self._return_coverage_case_debug_suffix(cases)
        return ReturnCoverageCheckResult(status="gap", detail=detail)
    if result.is_equivalent is None:
        return ReturnCoverageCheckResult(
            status="inconclusive",
            reason_id=UnknownReasonId.RETURN_COVERAGE_INCONCLUSIVE,
            detail=f"{label} return-case coverage query was inconclusive",
            can_record_completion_proof=True,
            inconclusive_cause="smt_disambiguation_inconclusive",
        )
    return ReturnCoverageCheckResult(
        status="covered",
        coverage_proof_method="smt_coverage_query",
        solver_status="unsat",
    )

def _impl__return_coverage_case_debug_suffix(self, cases: Sequence[Any]) -> str:
    lines: List[str] = []
    for case in cases or ():
        case_index = getattr(case, "index", "?")
        rendered_conditions = []
        for condition in getattr(case, "conditions", []) or []:
            to_string = getattr(condition, "to_string", None)
            if callable(to_string):
                try:
                    rendered_conditions.append(to_string())
                    continue
                except Exception:
                    pass
            rendered_conditions.append(repr(condition))
        lines.append(f"case[{case_index}] conditions={rendered_conditions}")
    if not lines:
        return ""
    return "\n  coverage cases:\n  " + "\n  ".join(lines)

def _impl__base_context_has_return_coverage_domain_assumptions(
    base_ctx: Mapping[str, Any],
) -> bool:
    assumptions = base_ctx.get("return_coverage_domain_assumptions")
    if not isinstance(assumptions, Mapping):
        return False
    return bool(assumptions.get("fp_non_nan"))

def _impl__return_cases_have_object_centric_total_coverage(
    self,
    cases: Sequence[Any],
) -> Optional[bool]:
    if not cases:
        return False
    if any(not getattr(case, "conditions", None) for case in cases):
        return True
    case_conditions = [
        condition
        for case in cases
        for condition in (getattr(case, "conditions", None) or ())
    ]
    if not ConditionSMTOracle.has_object_identity_support(case_conditions):
        return None
    smt_result = self._return_cases_have_smt_total_coverage(cases)
    if smt_result is not None:
        return smt_result
    return None

def _impl__return_cases_have_smt_total_coverage(
    self,
    cases: Sequence[Any],
) -> Optional[bool]:
    """Prove coverage from Condition objects without rendered-query plumbing.

    A coverage gap exists iff every return case can be missed at once.
    For a case with conditions c1..cn, the case is missed by
    (not c1) or ... or (not cn).  If the conjunction of all case-miss
    formulas is UNSAT, the return partition is total.
    """

    miss_conditions: List[Condition] = []
    for case in cases or ():
        conditions = list(getattr(case, "conditions", None) or [])
        if not conditions:
            return True
        miss_expr = self._case_miss_expression(conditions)
        if miss_expr is None:
            return None
        miss_conditions.append(Condition(miss_expr, False))
    if not miss_conditions:
        return False
    return ConditionSMTOracle.conjunction_is_unsat(miss_conditions)

def _impl__build_return_case_coverage_query(
    self,
    base_ctx: Dict[str, Any],
    cases: Sequence[Any],
    param_replace_fn,
    label: str,
) -> Optional[str]:
    disjuncts: List[str] = []
    for case in cases:
        conditions = list(getattr(case, "get_conditions_smt")(param_replace_fn))
        if not conditions:
            return None
        if len(conditions) == 1:
            disjuncts.append(conditions[0])
        else:
            disjuncts.append(f"(and {' '.join(conditions)})")

    if not disjuncts:
        return None

    lines = [
        f"; Return coverage gap query: {label}",
        *base_ctx.get("header_lines", []),
        f"(assert (not (or {' '.join(disjuncts)})))",
        "(check-sat)",
        "(get-model)",
    ]
    return "\n".join(lines)

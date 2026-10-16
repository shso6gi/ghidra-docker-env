"""Method-B covering-case closure: relation keys, completed-proof evidence and count identity compatibility."""

from __future__ import annotations

from typing import Any, Dict, List, Optional, Sequence, Tuple
from scripts.function_tracer_pcode.core import CountedLoopSummaryRef, FunctionReturnAnalysis, ReadonlyReductionRef
from scripts.function_tracer_pcode.proof.formula.input_correspondence.binding import comparison_evidence_subject
from scripts.function_tracer_pcode.proof.strategies.pairwise_services._shared import (
    CrossSideIdentification,
    certify_owner_free_identity,
    ReturnCase,
    UnknownRecoveryProofKind,
    _ExactReadonlyReductionProof,
    _MethodBCoveringCaseProof,
    build_unknown_recovery_actions,
    comparison_evidence,
    owner_free_evidence_values,
    store_comparison_evidence,
)


def _impl__method_b_covering_case_proof(
    self,
    case1: ReturnCase,
    case2: ReturnCase,
) -> Optional[_MethodBCoveringCaseProof]:
    right_ref = self._method_b_readonly_summary_ref(getattr(case2, "value_expr", None))
    if right_ref is not None:
        proven = self._prove_exact_load_sum_covers_readonly_loop_summary(case1, case2, right_ref)
        if proven is not None:
            proof, adapter = proven
            return _MethodBCoveringCaseProof("left", "right", case1, case2, adapter, proof)
    left_ref = self._method_b_readonly_summary_ref(getattr(case1, "value_expr", None))
    if left_ref is not None:
        proven = self._prove_exact_load_sum_covers_readonly_loop_summary(case2, case1, left_ref)
        if proven is not None:
            proof, adapter = proven
            return _MethodBCoveringCaseProof("right", "left", case2, case1, adapter, proof)
    return None


def _impl__record_completed_method_b_covering_case_proof_if_safe(
    self,
    reason_record,
    analysis: FunctionReturnAnalysis,
    case1: ReturnCase,
    case2: ReturnCase,
    *,
    v2_blocker_signal=None,
) -> None:
    if not self.enable_completed_recovery_proofs:
        return
    # 左右を owner を含まない key で比べて作る証拠。比べる値の読み（runtime ref の中を含む）が全幅で、
    # relation が位置どおり・全幅の等式のときだけ作り、その検査の証明書と一緒に記録する（plan v4
    # PR-P。採用の規則は証明書を照合する）。
    certification = certify_owner_free_identity(
        (case1,), (case2,),
        subject=comparison_evidence_subject(self._normalize_nested_tuple(reason_record.object_target_key)),
    )
    if not certification.passed:
        return
    from scripts.function_tracer_pcode.authority.domains.loop_recurrence import LOOP_REASON_SPECS

    if reason_record.reason_id not in LOOP_REASON_SPECS:
        return
    object_target_key = self._normalize_nested_tuple(reason_record.object_target_key)
    if not isinstance(object_target_key, tuple) or len(object_target_key) != 5:
        return
    covering = self._method_b_covering_case_proof(case1, case2)
    if covering is None:
        return
    proof = covering.exact_proof
    relation = self._normalize_nested_tuple(object_target_key[4])
    if not self._method_b_covering_relation_matches_proof(
        relation,
        exact_side=covering.exact_side,
        summary_side=covering.summary_side,
        proof=proof,
    ):
        return
    v2_term_completion_signal = None
    if v2_blocker_signal is not None:
        try:
            from scripts.function_tracer_pcode.authority.domains.loop_recurrence import (
                LoopExactTermRelationCompletionSignal,
            )
            from scripts.function_tracer_pcode.authority.lifecycle.production_signals import (
                emit_loop_recurrence_signal,
            )

            v2_term_completion_signal = (
                LoopExactTermRelationCompletionSignal.from_pairwise_cases(
                    v2_blocker_signal,
                    case1,
                    case2,
                )
            )
            emit_loop_recurrence_signal(
                v2_term_completion_signal,
                producer_site_manifest_id="pairwise-loop-term-completed",
            )
        except Exception as exc:
            from scripts.function_tracer_pcode.authority.lifecycle.production_signals import (
                record_production_pilot_shadow_error,
            )

            record_production_pilot_shadow_error(exc)
    actions = tuple(build_unknown_recovery_actions([reason_record]))
    records: List[Dict[str, Any]] = [
        dict(item)
        for item in getattr(analysis, "completed_recovery_proof_evidence", ()) or ()
        if isinstance(item, dict)
    ]
    # 既にある証拠は、この pair の値について作ったもの（と relation の premise の下の証拠）だけを数える。
    with owner_free_evidence_values((case1,), (case2,)):
        existing_ids = {
            self._normalize_nested_tuple(item.get("proof_obligation_id"))
            for item in comparison_evidence(records)
        }
    changed = self._append_completed_method_b_covering_case_evidence(
        records,
        existing_ids,
        actions,
        reason_id=reason_record.reason_id,
        object_target_key=object_target_key,
        covering=covering,
    )
    count_values = tuple(int(value) for value in (proof.count_values or (proof.count_value,)) if int(value) > 0)
    if self._cases_admit_reduction_count_values(
        covering.exact_case,
        covering.summary_case,
        covering.accumulator_proof,
        count_values,
    ):
        if v2_term_completion_signal is not None:
            try:
                from scripts.function_tracer_pcode.authority.domains.loop_recurrence import (
                    LoopExactGuardPartitionCompletionSignal,
                )
                from scripts.function_tracer_pcode.authority.lifecycle.production_signals import (
                    emit_loop_recurrence_signal,
                )

                emit_loop_recurrence_signal(
                    LoopExactGuardPartitionCompletionSignal.from_pairwise_cases(
                        v2_term_completion_signal,
                        case1,
                        case2,
                    ),
                    producer_site_manifest_id="pairwise-loop-guard-completed",
                )
            except Exception as exc:
                from scripts.function_tracer_pcode.authority.lifecycle.production_signals import (
                    record_production_pilot_shadow_error,
                )

                record_production_pilot_shadow_error(exc)
        changed = self._append_completed_method_b_guard_partition_evidence(
            records,
            existing_ids,
            actions,
            reason_id=reason_record.reason_id,
            object_target_key=object_target_key,
            covering=covering,
        ) or changed
    if changed:
        store_comparison_evidence(
            analysis, records, identification=CrossSideIdentification.OWNER_FREE,
            certificate=certification.certificate,
            checked_values=((case1,), (case2,)),
        )


def _impl__append_completed_method_b_covering_case_evidence(
    self,
    records: List[Dict[str, Any]],
    existing_ids: set,
    actions: Sequence[Any],
    *,
    reason_id: str,
    object_target_key: Tuple[Any, ...],
    covering: _MethodBCoveringCaseProof,
) -> bool:
    action = self._method_b_recovery_action(
        actions,
        proof_kind=UnknownRecoveryProofKind.PROOF_BACKED_COVERING_CASE.value,
        proof_stage="method_b_covering_case",
    )
    if action is None:
        return False
    proof_id = self._normalize_nested_tuple(action.proof_obligation_id)
    if proof_id is None or proof_id in existing_ids:
        return False
    proof = covering.exact_proof
    count_values = tuple(int(value) for value in (proof.count_values or (proof.count_value,)) if int(value) > 0)
    records.append(
        {
            "object_derived": True,
            "status": "complete",
            "reason_id": reason_id,
            "proof_kind": action.proof_kind,
            "recovery_proof_kind": action.proof_kind,
            "proof_stage": action.proof_stage,
            "evidence_kind": action.evidence_kind,
            "required_evidence": tuple(action.required_evidence),
            "object_target_key": object_target_key,
            "proof_obligation_id": proof_id,
            "proof_source": "method_b_one_sided_summary_exact_terms",
            "proof_content": {
                "object_derived": True,
                "object_target_key": object_target_key,
                "seed_compensation": "proven",
                "term_sequence": "matched",
                "pure_side_effect_profile": "proven",
                "exact_side": covering.exact_side,
                "summary_side": covering.summary_side,
                "count_value": int(proof.count_value),
                "count_values": count_values,
                "exact_terms": tuple(term.stable_key() for term in proof.exact_terms),
                "expected_terms": tuple(term.stable_key() for term in proof.expected_terms),
                "constant_bias": int(proof.constant_bias),
                "result_size": int(proof.result_size),
                "covering_evidence": proof.evidence,
            },
        }
    )
    existing_ids.add(proof_id)
    return True


def _impl__append_completed_method_b_guard_partition_evidence(
    self,
    records: List[Dict[str, Any]],
    existing_ids: set,
    actions: Sequence[Any],
    *,
    reason_id: str,
    object_target_key: Tuple[Any, ...],
    covering: _MethodBCoveringCaseProof,
) -> bool:
    action = self._method_b_recovery_action(
        actions,
        proof_kind=UnknownRecoveryProofKind.GUARD_PARTITION_COMPLETION.value,
        proof_stage="method_b_guard_partition",
    )
    if action is None:
        return False
    proof_id = self._normalize_nested_tuple(action.proof_obligation_id)
    if proof_id is None or proof_id in existing_ids:
        return False
    proof = covering.exact_proof
    count_values = tuple(int(value) for value in (proof.count_values or (proof.count_value,)) if int(value) > 0)
    guard_evidence = (
        "reduction_count_implication"
        if len(count_values) == 1
        else "reduction_count_membership_implication"
    )
    records.append(
        {
            "object_derived": True,
            "status": "complete",
            "reason_id": reason_id,
            "proof_kind": action.proof_kind,
            "recovery_proof_kind": action.proof_kind,
            "proof_stage": action.proof_stage,
            "evidence_kind": action.evidence_kind,
            "required_evidence": tuple(action.required_evidence),
            "object_target_key": object_target_key,
            "proof_obligation_id": proof_id,
            "proof_source": "method_b_reduction_count_guard_partition",
            "proof_content": {
                "object_derived": True,
                "object_target_key": object_target_key,
                "guard_partition": "proven",
                "partition_coverage_proof": "covered",
                "exact_side": covering.exact_side,
                "summary_side": covering.summary_side,
                "count_value": int(proof.count_value),
                "count_values": count_values,
                "guard_evidence": guard_evidence,
            },
        }
    )
    existing_ids.add(proof_id)
    return True


def _impl__method_b_recovery_action(
    actions: Sequence[Any],
    *,
    proof_kind: str,
    proof_stage: str,
):
    return next(
        (
            candidate
            for candidate in actions
            if candidate.proof_stage == proof_stage and candidate.proof_kind == proof_kind
        ),
        None,
    )


def _impl__method_b_covering_relation_matches_proof(
    relation: Any,
    *,
    exact_side: str,
    summary_side: str,
    proof: _ExactReadonlyReductionProof,
) -> bool:
    if not isinstance(relation, tuple) or relation[0] != "method_b_closure_relation":
        return False
    fields = {
        item[0]: item[1]
        for item in relation[1:]
        if isinstance(item, tuple) and len(item) == 2
    }
    if fields.get("kind") != "one_sided_summary":
        return False
    if fields.get("exact_side") != exact_side or fields.get("summary_side") != summary_side:
        return False
    exact_terms = fields.get("exact_terms")
    if not isinstance(exact_terms, tuple) or not exact_terms:
        return False
    if tuple(exact_terms) != tuple(term.stable_key() for term in proof.exact_terms):
        return False
    try:
        exact_constant_bias = int(fields.get("exact_constant_bias"))
    except (TypeError, ValueError):
        return False
    return exact_constant_bias == int(proof.constant_bias)


def _impl__register_storage_identity_components(
    self,
    storage_identity: Optional[tuple],
) -> Optional[Tuple[int, int, int, int, int]]:
    normalized = tuple(storage_identity or ())
    if (
        len(normalized) == 2
        and normalized[0] == "parameter_storage"
        and isinstance(normalized[1], tuple)
    ):
        normalized = tuple(normalized[1])
    if len(normalized) != 6 or normalized[0] != "register_storage":
        return None
    try:
        return (
            int(normalized[1]),
            int(normalized[2]),
            int(normalized[3]),
            int(normalized[4]),
            int(normalized[5]),
        )
    except (TypeError, ValueError):
        return None


def _impl__method_b_closure_object_target_key(
    self,
    *,
    base_ctx: Dict[str, Any],
    case1: ReturnCase,
    case2: ReturnCase,
    pair_id: str,
) -> Tuple[Any, ...]:
    """Object-derived target key for Method-B covering/guard proof backlog."""

    return (
        "method_b_closure",
        ("pair", pair_id),
        self._method_b_closure_side_object_key(
            "left",
            base_ctx.get("analysis1"),
            case1,
        ),
        self._method_b_closure_side_object_key(
            "right",
            base_ctx.get("analysis2"),
            case2,
        ),
        self._method_b_closure_relation_object_key(case1, case2),
    )


def _impl__method_b_closure_relation_object_key(
    self,
    case1: ReturnCase,
    case2: ReturnCase,
) -> Tuple[Any, ...]:
    left_readonly_ref = self._method_b_readonly_summary_ref(getattr(case1, "value_expr", None))
    right_readonly_ref = self._method_b_readonly_summary_ref(getattr(case2, "value_expr", None))
    left_summary_ref = self._method_b_summary_runtime_ref(getattr(case1, "value_expr", None))
    right_summary_ref = self._method_b_summary_runtime_ref(getattr(case2, "value_expr", None))
    if left_readonly_ref is not None and right_summary_ref is None:
        return self._method_b_one_sided_summary_relation(
            summary_side="left",
            summary_ref=left_readonly_ref,
            exact_side="right",
            exact_case=case2,
        )
    if right_readonly_ref is not None and left_summary_ref is None:
        return self._method_b_one_sided_summary_relation(
            summary_side="right",
            summary_ref=right_readonly_ref,
            exact_side="left",
            exact_case=case1,
        )
    if left_summary_ref is not None and right_summary_ref is not None:
        return (
            "method_b_closure_relation",
            ("kind", "dual_summary"),
            ("left_summary", self._method_b_summary_profile_key(left_summary_ref)),
            ("right_summary", self._method_b_summary_profile_key(right_summary_ref)),
        )
    return ("method_b_closure_relation", ("kind", "missing_method_b_summary"))


def _impl__method_b_one_sided_summary_relation(
    self,
    *,
    summary_side: str,
    summary_ref: ReadonlyReductionRef,
    exact_side: str,
    exact_case: ReturnCase,
) -> Tuple[Any, ...]:
    extracted = self._extract_readonly_reduction_terms_and_bias_from_expression(
        getattr(exact_case, "value_expr", None),
        getattr(exact_case, "parameters", ()) or (),
        getattr(summary_ref, "pointer_base_ref", None),
        program_is_big_endian=getattr(exact_case, "program_is_big_endian", None),
    )
    exact_terms_key: Any = ("exact_terms_unavailable",)
    exact_bias: Any = None
    if extracted is not None:
        exact_terms, exact_bias = extracted
        exact_terms_key = tuple(term.stable_key() for term in exact_terms)
    return (
        "method_b_closure_relation",
        ("kind", "one_sided_summary"),
        ("summary_side", summary_side),
        ("exact_side", exact_side),
        ("summary", self._method_b_summary_profile_key(summary_ref)),
        ("exact_terms", exact_terms_key),
        ("exact_constant_bias", exact_bias),
    )


def _impl__method_b_summary_profile_key(self, summary_ref) -> Tuple[Any, ...]:
    if isinstance(summary_ref, CountedLoopSummaryRef):
        runtime_ref_key = self._counted_loop_summary_runtime_profile_key(summary_ref)
        loop_summary_key = self._counted_loop_summary_loop_profile_key(getattr(summary_ref, "loop_summary", None))
        term_contract = self._counted_loop_summary_contract_key(summary_ref)
        count_identities = self._counted_loop_summary_count_identities(summary_ref)
    else:
        runtime_ref_key = self._semantic_key_or_stable_key_or_none(summary_ref)
        loop_summary_key = self._semantic_key_or_stable_key_or_none(getattr(summary_ref, "loop_summary", None))
        term_contract = self._readonly_reduction_term_sequence_contract_key(
            summary_ref,
            result_size=getattr(summary_ref, "result_size", None),
        )
        term_contract = self._method_b_normalized_term_contract_key(summary_ref, term_contract)
        count_identities = tuple(sorted(self._readonly_count_identity_keys(summary_ref), key=repr))
    return (
        "method_b_summary_profile",
        ("runtime_ref", runtime_ref_key),
        ("loop_summary", loop_summary_key),
        ("term_contract", term_contract),
        ("count_identities", tuple(sorted(count_identities, key=repr))),
    )


def _impl__method_b_value_key_or_none(self, value: Any):
    key = self._semantic_key_or_stable_key_or_none(value)
    if key is not None:
        return self._method_b_key_with_explicit_optional_none(key)
    structural_key = getattr(value, "structural_key", None)
    if callable(structural_key):
        try:
            return self._method_b_key_with_explicit_optional_none(structural_key(budget=256))
        except (AttributeError, TypeError, ValueError, RecursionError):
            return None
    return None


def _impl__method_b_key_with_explicit_optional_none(self, value: Any):
    if value is None:
        return ("optional_none",)
    if isinstance(value, tuple):
        return tuple(self._method_b_key_with_explicit_optional_none(item) for item in value)
    if isinstance(value, list):
        return tuple(self._method_b_key_with_explicit_optional_none(item) for item in value)
    return value


def _impl__method_b_normalized_term_contract_key(
    self,
    readonly_ref: ReadonlyReductionRef,
    term_contract: Optional[tuple],
) -> Optional[tuple]:
    if not isinstance(term_contract, tuple) or not term_contract:
        return term_contract
    if term_contract[0] != "loop_summary_method_b" or len(term_contract) < 9:
        return term_contract
    pointer_base = self._semantic_key_or_stable_key_or_none(getattr(readonly_ref, "pointer_base_ref", None))
    count_identities = tuple(sorted(self._readonly_count_identity_keys(readonly_ref), key=repr))
    count_identity = count_identities[0] if count_identities else None
    if pointer_base is None or count_identity is None:
        return term_contract
    term_sequence = term_contract[5]
    if not isinstance(term_sequence, tuple) or len(term_sequence) < 7:
        return term_contract
    try:
        result_size = max(1, int(getattr(readonly_ref, "result_size", 0) or term_sequence[6]))
    except (TypeError, ValueError):
        return term_contract
    return (
        "readonly_reduction_term_sequence_contract",
        str(getattr(readonly_ref, "reduction_kind", None) or "memory_sum"),
        pointer_base,
        count_identity,
        term_contract[3],
        result_size,
        term_sequence[3],
        term_contract[4],
        getattr(readonly_ref, "constant_bias", 0),
        term_sequence[5],
        bool(getattr(readonly_ref, "signed_counter", False)),
        term_contract[6],
        term_contract[7],
        term_contract[8],
    )


def _impl__method_b_closure_side_object_key(
    self,
    side_label: str,
    analysis: Optional[FunctionReturnAnalysis],
    case: ReturnCase,
) -> Tuple[Any, ...]:
    value_expr = getattr(case, "value_expr", None)
    return (
        "method_b_closure_side",
        side_label,
        self._analysis_entry_key(analysis) if analysis is not None else None,
        self._readonly_return_case_partition_member_object_key(case),
        (
            "loop_value",
            self._method_b_loop_value_object_key(value_expr),
        ),
        (
            "guards",
            tuple(
                self._return_condition_object_key(condition)
                for condition in (getattr(case, "conditions", None) or ())
            ),
        ),
    )


def _impl__semantic_key_or_stable_key_or_none(value: Any):
    for name in ("pairwise_semantic_key", "semantic_key", "stable_key"):
        key_fn = getattr(value, name, None)
        if callable(key_fn):
            try:
                key = key_fn()
            except (AttributeError, TypeError, ValueError, RecursionError):
                key = None
            if key is not None:
                return key
    return None


def _impl__diagnostic_key_or_semantic_key_or_stable_key_or_none(value: Any):
    for name in ("diagnostic_key", "pairwise_semantic_key", "semantic_key", "stable_key"):
        key_fn = getattr(value, name, None)
        if callable(key_fn):
            try:
                key = key_fn()
            except (AttributeError, TypeError, ValueError, RecursionError):
                key = None
            if key is not None:
                return key
    return None


def _impl__count_identity_components_compatible(
    self,
    left_storage: Optional[tuple],
    left_index: Optional[tuple],
    right_storage: Optional[tuple],
    right_index: Optional[tuple],
) -> bool:
    if left_storage is not None and right_storage is not None:
        if left_storage == right_storage:
            return True
        return False
    return left_index is not None and right_index is not None and left_index == right_index


def _impl__count_storage_low_projection_compatible(
    self,
    left_storage: tuple,
    right_storage: tuple,
) -> bool:
    left_register = self._register_storage_identity_components(left_storage)
    right_register = self._register_storage_identity_components(right_storage)
    if left_register is None or right_register is None:
        return False
    if left_register[:3] != right_register[:3]:
        return False
    left_low, left_size = int(left_register[3]), int(left_register[4])
    right_low, right_size = int(right_register[3]), int(right_register[4])
    if left_low != right_low:
        return False
    return left_size <= right_size or right_size <= left_size


def _impl__accumulator_proof_supports_count_bit_width(
    self,
    case: ReturnCase,
    accumulator_proof,
    candidate_bits: int,
) -> bool:
    candidate_bits = max(1, int(candidate_bits))
    proof_bits = self._reduction_count_bit_width(accumulator_proof)
    if candidate_bits == proof_bits:
        return True
    if candidate_bits > proof_bits:
        return False
    for expr in self._accumulator_proof_count_surface_expressions(accumulator_proof):
        if self._expression_contains_reduction_count_surface_at_width(
            expr,
            case,
            accumulator_proof,
            candidate_bits,
        ):
            return True
    return False


def _impl__accumulator_proof_count_surface_expressions(self, accumulator_proof):
    limit_expr = getattr(accumulator_proof, "limit_expr", None)
    if limit_expr is not None:
        yield limit_expr
    for condition in tuple(getattr(accumulator_proof, "guard_constraints", ()) or ()):
        expr = getattr(condition, "expression", condition)
        if expr is not None:
            yield expr

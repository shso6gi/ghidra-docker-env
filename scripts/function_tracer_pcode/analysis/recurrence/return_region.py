"""Stateless method implementations extracted from ``scripts.function_tracer_pcode.analysis.recurrence.summarizer``."""

from __future__ import annotations

from typing import Any, Dict, Iterable, List, Optional, Sequence, Set, Tuple
from scripts.function_tracer_pcode.core.evidence_authority import record_function_unary_evidence
from scripts.function_tracer_pcode.core import (
    Condition,
    Expression,
    ExpressionType,
    PcodeOpRef,
    ReturnInfo,
    StorageInfo,
)
from scripts.function_tracer_pcode.core.runtime_refs import UnknownValueRef
from scripts.function_tracer_pcode.core.errors import AnalysisLimitation
from scripts.function_tracer_pcode.smt.interface import SolverStatus
from scripts.function_tracer_pcode.smt.solvers.z3 import Z3Solver
from scripts.function_tracer_pcode.smt.parallel import run_backend_query
from scripts.function_tracer_pcode.analysis.recurrence._shared import (
    ConditionSMTOracle,
    _reduce_expression_under_conditions,
    _runtime_conditions_signature,
    _runtime_expression_signature,
)

def _impl_has_summary_candidate(self, function, high_function, analysis) -> bool:
    if function is None or high_function is None or analysis is None:
        return False
    if not getattr(analysis, "returns", None):
        return False

    function_name = getattr(function, "getName", lambda: "")()
    if len(getattr(analysis, "parameters", []) or []) == 1 and any(
        self._expression_contains_recursive_unknown(ret.value, function_name)
        for ret in (analysis.returns or [])
    ):
        return True

    if self._has_readonly_pointer_reduction_candidate(high_function, analysis):
        return True

    if self._has_counted_scalar_loop_candidate(high_function):
        return True

    if self._has_state_transition_loop_candidate(high_function):
        return True

    if self._has_proved_return_region_state_transition_candidate(analysis):
        return True

    if self._has_branch_accumulator_candidate(analysis):
        return True

    return False

def _impl__prove_return_value_equals_summary_closed_form(
    self,
    value: Expression,
    summary_closed: Expression,
    conditions: Sequence[Condition],
    *,
    result_size: int,
) -> bool:
    reduced_value = _reduce_expression_under_conditions(value, conditions)
    if reduced_value is not None:
        value = reduced_value
    reduced_summary = _reduce_expression_under_conditions(summary_closed, conditions)
    if reduced_summary is not None:
        summary_closed = reduced_summary
    actual = self._coerce_summary_expression_to_size(
        value,
        result_size,
        signed=self._expression_prefers_signed_extension(value),
    )
    expected = self._coerce_summary_expression_to_size(
        summary_closed,
        result_size,
        signed=False,
    )
    disequality = Condition(Expression.binary_op("INT_NOTEQUAL", actual, expected), False)
    proof_conditions = list(conditions or []) + [disequality]
    try:
        if ConditionSMTOracle.conjunction_is_unsat(proof_conditions) is True:
            return True
    except AnalysisLimitation:
        # Issue #106 PR-106-0: 解析の限界は「回復可能な失敗」ではない。ここで
        # 握り潰すと pair の打ち切りが遅れるので、そのまま上へ返す。
        raise
    except Exception:
        pass
    try:
        usable, script = ConditionSMTOracle._build_script(proof_conditions)
    except Exception:
        return False
    if not usable or not script:
        return False
    try:
        result = run_backend_query(Z3Solver(timeout=2, debug=False), script)
    except Exception:
        return False
    return result.status == SolverStatus.UNSAT

def _impl__return_value_contains_phi_circular(self, expr: Optional[Expression]) -> bool:
    for node in self._iter_expression_nodes(expr):
        if getattr(node, "expr_type", None) != ExpressionType.UNKNOWN:
            continue
        if "phi_circular" in str(getattr(node, "name", "") or ""):
            return True
        runtime_ref = getattr(node, "runtime_ref", None)
        if isinstance(runtime_ref, UnknownValueRef) and getattr(runtime_ref, "reason", None) == "phi_circular":
            return True
    return False

def _impl__record_return_region_summary_proof(
    self,
    *,
    analysis,
    summary_value: Expression,
    summary_conditions: Sequence[Condition],
    exact_returns: Sequence[ReturnInfo],
    source: str,
    allow_summary_region_coverage: bool = False,
) -> Optional[Tuple[Any, ...]]:
    if not self.enable_completed_recovery_proofs:
        return None
    witnesses = self._prove_return_region_summary_witnesses(
        analysis=analysis,
        summary_value=summary_value,
        summary_conditions=summary_conditions,
        exact_returns=exact_returns,
        allow_summary_region_coverage=allow_summary_region_coverage,
    )
    if witnesses is None:
        return None
    witness_key, coverage_key, coverage_status = witnesses
    source_key = self._summary_value_source_key(summary_value)
    if source_key is None:
        source_key = ("summary_value", _runtime_expression_signature(summary_value))
    object_target_key = (
        "return_region_summary_target",
        _runtime_expression_signature(summary_value),
        _runtime_conditions_signature(tuple(summary_conditions or ())),
        witness_key,
        coverage_key,
        source_key,
    )
    proof_id = ("proof_obligation_id", "return_region_summary", object_target_key)
    proof_ref = ("return_region_summary_proof_ref", proof_id, object_target_key)
    existing = tuple(getattr(analysis, "completed_recovery_proof_evidence", ()) or ())
    if any(item.get("proof_obligation_id") == proof_id for item in existing if isinstance(item, dict)):
        return proof_ref
    evidence = {
        "proof_obligation_id": proof_id,
        "reason_id": "return_region_summary",
        "status": "complete",
        "proof_stage": "return_region_summary",
        "evidence_kind": "smt_value_equivalence",
        "object_target_key": object_target_key,
        "proof_source": str(source or "return_region_summary"),
        "proof_content": {
            "proof_status": "proved",
            "object_target_key": object_target_key,
            "summary_value_key": object_target_key[1],
            "summary_conditions_key": object_target_key[2],
            "exact_witnesses_key": witness_key,
            "coverage_key": coverage_key,
            "source_key": source_key,
            "checks": (
                ("summary_value_equivalence", "proved"),
                ("summary_region_coverage", coverage_status),
                ("summary_side_effects", "pure"),
            ),
        },
    }
    record_function_unary_evidence(analysis, evidence)
    return proof_ref

def _impl__summary_excluded_counter_values(
    self,
    conditions: Sequence[Condition],
    parameters: Optional[Sequence[dict]] = None,
) -> Tuple[Tuple[Tuple[Any, ...], int], ...]:
    excluded: List[Tuple[Tuple[Any, ...], int]] = []
    for condition in conditions or ():
        if not bool(getattr(condition, "negated", False)):
            continue
        expr = getattr(condition, "expression", None)
        if getattr(expr, "expr_type", None) != ExpressionType.BINARY_OP:
            continue
        if getattr(expr, "operator", None) != "INT_EQUAL":
            continue
        operands = list(getattr(expr, "operands", ()) or ())
        if len(operands) != 2:
            continue
        left, right = operands
        left_const = self._constant_value(left)
        right_const = self._constant_value(right)
        if getattr(left, "expr_type", None) == ExpressionType.PARAMETER and right_const is not None:
            key = self._counter_parameter_identity_key(left, parameters)
            if key is not None:
                excluded.append((key, int(right_const)))
        elif getattr(right, "expr_type", None) == ExpressionType.PARAMETER and left_const is not None:
            key = self._counter_parameter_identity_key(right, parameters)
            if key is not None:
                excluded.append((key, int(left_const)))
    return tuple(dict.fromkeys(excluded))

def _impl__return_covers_nonpositive_parameter_region(
    self,
    ret: ReturnInfo,
    positive_param_key: Tuple[Any, ...],
) -> bool:
    return self._conditions_cover_nonpositive_parameter_region(
        getattr(ret, "conditions", None) or (),
        positive_param_key,
    )

def _impl__collect_summary_parameter_specs(
    self,
    *exprs: Optional[Expression],
) -> Optional[List[dict]]:
    return self._collect_expression_symbol_specs(*exprs)

def _impl__summary_storage_info_from_parameter(self, param: dict) -> Optional[StorageInfo]:
    storage_info = param.get("storage_info", param.get("storage")) if isinstance(param, dict) else None
    if isinstance(storage_info, StorageInfo):
        return storage_info
    if isinstance(storage_info, dict):
        try:
            return StorageInfo(**storage_info)
        except Exception:
            return None
    return None

def _impl__assign_summary_auxiliary_symbols(
    self,
    symbol_specs: Iterable[dict],
) -> List[dict]:
    ordered = sorted(
        (dict(spec) for spec in symbol_specs or [] if spec.get("identity") is not None),
        key=lambda item: (
            self._summary_symbol_identity_sort_key(item.get("identity")),
            int(item.get("size", 0) or 0),
        ),
    )
    for ordinal, spec in enumerate(ordered):
        spec["aux_name"] = f"aux_sym_{ordinal}"
        spec["aux_index"] = ordinal
    return ordered

def _impl__exit_region_return_refs_using_value(
    self,
    exit_block,
    init_varnode,
    *,
    phi_output_varnode=None,
    forbidden_blocks: Sequence[object],
    budget: int = 64,
) -> Optional[Tuple[Tuple[PcodeOpRef, ...], Tuple[Tuple[Any, ...], ...]]]:
    forbidden_keys = {
        self._block_key(block)
        for block in forbidden_blocks or ()
        if self._block_key(block) != self._block_key(exit_block)
    }
    refs: Dict[Tuple[Any, ...], PcodeOpRef] = {}
    scanned_op_keys: Set[Tuple[Any, ...]] = set()
    proven_blocks: Set[Any] = set()
    visiting: Set[Any] = set()

    def prove_block(block, depth: int) -> bool:
        if block is None or depth > budget:
            return False
        block_key = self._block_key(block)
        if block_key in forbidden_keys:
            return False
        if block_key in proven_blocks:
            return True
        if block_key in visiting:
            return False
        visiting.add(block_key)
        has_return = False
        block_ops = self._strict_zero_iteration_exit_region_block_ops(block)
        if block_ops is None:
            visiting.discard(block_key)
            return False
        for op in block_ops:
            mnemonic = str(getattr(op, "getMnemonic", lambda: "")() or "").strip().upper()
            if not self._zero_iteration_exit_region_mnemonic_is_safe(mnemonic):
                visiting.discard(block_key)
                return False
            scanned_op_keys.add(self._zero_iteration_exit_region_op_key(op, block))
            if mnemonic != "RETURN":
                continue
            has_return = True
            if not self._return_op_returns_varnode(
                op,
                init_varnode,
                phi_output_varnode=phi_output_varnode,
            ):
                try:
                    return_operand = op.getInput(1) if self._safe_pcode_input_count(op) >= 2 else None
                except Exception:
                    return_operand = None
                self._debug(
                    "Declined zero-iteration anchor proof: return operand mismatch "
                    f"(return={self._varnode_cache_key(return_operand)}, "
                    f"return_followed={self._varnode_cache_key(self._follow_passthrough_varnode(return_operand))}, "
                    f"init={self._varnode_cache_key(init_varnode)}, "
                    f"init_followed={self._varnode_cache_key(self._follow_passthrough_varnode(init_varnode))}, "
                    f"phi_output={self._varnode_cache_key(phi_output_varnode)})"
                )
                visiting.discard(block_key)
                return False
            ref = self._make_pcode_op_ref(op)
            if ref is not None:
                refs.setdefault(ref.stable_key(), ref)
        if has_return:
            visiting.discard(block_key)
            proven_blocks.add(block_key)
            return True
        successors = self._collect_block_successors(block)
        if not successors:
            visiting.discard(block_key)
            return False
        for successor in successors:
            if not prove_block(successor, depth + 1):
                visiting.discard(block_key)
                return False
        visiting.discard(block_key)
        proven_blocks.add(block_key)
        return True

    if not prove_block(exit_block, 0):
        return None
    return (
        tuple(sorted(refs.values(), key=lambda ref: repr(ref.stable_key()))),
        tuple(sorted(scanned_op_keys, key=repr)),
    )

def _impl__strict_zero_iteration_exit_region_block_ops(block) -> Optional[Tuple[object, ...]]:
    get_iterator = getattr(block, "getIterator", None)
    if not callable(get_iterator):
        return None
    try:
        iterator = get_iterator()
    except Exception:
        return None
    if iterator is None:
        return None
    has_next = getattr(iterator, "hasNext", None)
    next_item = getattr(iterator, "next", None)
    if callable(has_next) and callable(next_item):
        ops: List[object] = []
        while True:
            try:
                has_item = has_next()
                if not isinstance(has_item, bool):
                    return None
                if not has_item:
                    break
                ops.append(next_item())
            except Exception:
                return None
        return tuple(ops)
    try:
        return tuple(iterator)
    except Exception:
        return None

def _impl__zero_iteration_exit_region_mnemonic_is_safe(mnemonic: object) -> bool:
    name = str(mnemonic or "").strip().upper()
    if not name:
        return False
    if name in {
        "CALL",
        "CALLIND",
        "CALLOTHER",
        "LOAD",
        "STORE",
        "BRANCH",
        "CBRANCH",
        "BRANCHIND",
        "INDIRECT",
    }:
        return False
    if "FLOAT" in name or name in {"INT2FLOAT", "FLOAT2INT"}:
        return False
    if name in {
        "RETURN",
        "COPY",
        "CAST",
        "SUBPIECE",
        "PIECE",
        "MULTIEQUAL",
        "BOOL_AND",
        "BOOL_OR",
        "BOOL_XOR",
        "BOOL_NEGATE",
        "PTRADD",
        "PTRSUB",
        "SEGMENTOP",
        "CPOOLREF",
    }:
        return True
    return name.startswith("INT_")

def _impl__return_op_returns_varnode(self, return_op, init_varnode, *, phi_output_varnode=None) -> bool:
    if self._safe_pcode_input_count(return_op) < 2:
        return False
    return_value = self._follow_passthrough_varnode(return_op.getInput(1))
    init_value = self._follow_passthrough_varnode(init_varnode)
    if self._same_varnode_value(return_value, init_value):
        return True
    if phi_output_varnode is None:
        return False
    phi_output = self._follow_passthrough_varnode(phi_output_varnode)
    return self._same_varnode_value(return_value, phi_output)

def _impl__return_is_exact_anchor_seed(self, ret: ReturnInfo) -> bool:
    if str(getattr(ret, "return_kind", "exact") or "exact") != "exact":
        return False
    if self._expression_is_unresolved(getattr(ret, "value", None)):
        return False
    if getattr(ret, "summary_candidate_id", None) is not None:
        return False
    if getattr(ret, "summary_candidate_source_key", None) is not None:
        return False
    if getattr(ret, "summary_transition_evidence_key", None) is not None:
        return False
    for node in self._iter_expression_nodes(getattr(ret, "value", None)):
        runtime_ref = getattr(node, "runtime_ref", None)
        for owner in (
            runtime_ref,
            getattr(runtime_ref, "loop_summary", None),
            getattr(runtime_ref, "accumulator_proof", None),
            getattr(runtime_ref, "proof", None),
        ):
            stable_key = self._stable_key_or_none(owner)
            if stable_key is not None and self._stable_key_looks_like_loop_summary(stable_key):
                return False
    return True

def _impl__return_is_stable_resolved_phi_anchor_seed(self, ret: ReturnInfo) -> bool:
    if str(getattr(ret, "return_kind", "exact") or "exact") != "phi_expansion":
        return False
    if self._expression_is_unresolved(getattr(ret, "value", None)):
        return False
    if getattr(ret, "summary_candidate_id", None) is not None:
        return False
    if getattr(ret, "summary_candidate_source_key", None) is not None:
        return False
    if getattr(ret, "summary_transition_evidence_key", None) is not None:
        return False
    if not (
        getattr(ret, "pcode_op_ref", None) is not None
        or getattr(ret, "pcode_identity", None)
        or tuple(getattr(ret, "return_value_pcode_op_refs", ()) or ())
    ):
        return False
    return True

def _impl__synthesize_bounded_prefix_exact_returns(
    self,
    analysis,
    high_function,
    pointer_param: dict,
    count_param: dict,
    *,
    counter_signed: bool,
    broad_positive_conditions: Sequence[Condition],
    existing_returns: Sequence[ReturnInfo],
    result_size: int,
) -> List[ReturnInfo]:
    synthesized = list(existing_returns or ())
    proofs = self._collect_readonly_prefix_accumulator_proofs(
        analysis,
        high_function,
        pointer_param,
        count_param,
        counter_signed=counter_signed,
        positive_conditions=broad_positive_conditions,
        result_size=result_size,
    )
    if not proofs:
        self._debug("Skipped bounded prefix exact synthesis: no prefix accumulator proofs")
        return synthesized
    self._debug(f"Bounded prefix exact synthesis: considering {len(proofs)} prefix proof(s)")
    count_name = str(count_param.get("name") or "")
    existing_exact_counts = {
        int(exact_count)
        for ret in synthesized
        for exact_count in [self._exact_counter_value_from_conditions(ret.conditions or [], count_name)]
        if exact_count is not None and int(exact_count) > 0
    }
    for proof in proofs:
        anchor_returns = []
        bounded_region_anchors: List[Tuple[ReturnInfo, List[Condition]]] = []
        max_upper_bound = None
        for ret in getattr(analysis, "returns", None) or ():
            exact_count = self._exact_counter_value_from_conditions(ret.conditions or [], count_name)
            exact_count_was_inferred_from_terms = False
            if exact_count is None:
                extracted = self._extract_readonly_return_terms_and_bias(
                    analysis,
                    pointer_param,
                    ret,
                    proof,
                )
                if extracted is not None:
                    extracted_terms, _constant_bias = extracted
                    exact_count = self._infer_exact_count_from_readonly_terms(
                        ret.conditions or [],
                        extracted_terms,
                        count_param,
                        proof,
                    )
                    if exact_count is None:
                        candidate_count = len(tuple(extracted_terms or ()))
                        expected_terms = proof.full_terms_for_count_value(int(candidate_count))
                        if (
                            candidate_count > 0
                            and expected_terms is not None
                            and tuple(term.stable_key() for term in extracted_terms) == tuple(
                                term.stable_key() for term in expected_terms
                            )
                            and self._conditions_imply_counter_value(
                                ret.conditions or [],
                                count_param,
                                int(candidate_count),
                            )
                        ):
                            exact_count = int(candidate_count)
                            exact_count_was_inferred_from_terms = True
                    else:
                        exact_count_was_inferred_from_terms = True
            upper_bound = self._infer_upper_bound_from_conditions(ret.conditions or [], count_name)
            if exact_count is not None and int(exact_count) > 0:
                if not exact_count_was_inferred_from_terms and not self._readonly_positive_return_proves_count_value(
                    analysis,
                    pointer_param,
                    count_param,
                    ret,
                    proof,
                    count_value=int(exact_count),
                ):
                    continue
                if upper_bound is None or int(upper_bound) < int(exact_count):
                    continue
                anchor_returns.append(ret)
                if int(upper_bound) > int(exact_count):
                    bounded_conditions = self._bounded_prefix_region_conditions_from_exact_anchor(
                        ret.conditions or [],
                        count_param,
                        exact_count=int(exact_count),
                        upper_bound=int(upper_bound),
                    )
                    if bounded_conditions is not None:
                        bounded_region_anchors.append((ret, bounded_conditions))
                max_upper_bound = int(upper_bound) if max_upper_bound is None else max(max_upper_bound, int(upper_bound))
                continue
            if upper_bound is None or int(upper_bound) <= 0 or int(upper_bound) > 16:
                continue
            if not self._readonly_return_region_value_is_proven(
                ret,
                tuple(getattr(proof, "guard_constraints", ()) or broad_positive_conditions or ()),
                proof,
            ):
                continue
            if any(proof.full_terms_for_count_value(count_value) is None for count_value in range(1, int(upper_bound) + 1)):
                continue
            anchor_returns.append(ret)
            bounded_region_anchors.append((ret, list(ret.conditions or [])))
            max_upper_bound = int(upper_bound) if max_upper_bound is None else max(max_upper_bound, int(upper_bound))
        if not anchor_returns or max_upper_bound is None or max_upper_bound <= 0 or max_upper_bound > 16:
            self._debug("Skipped bounded prefix exact synthesis: no bounded/exact anchor returns")
            continue
        anchor = anchor_returns[0]
        synthesis_base_conditions = (
            list(bounded_region_anchors[0][1])
            if bounded_region_anchors
            else list(anchor.conditions or broad_positive_conditions or [])
        )
        added_for_anchor: Dict[int, ReturnInfo] = {}
        for count_value in range(1, max_upper_bound + 1):
            if count_value in existing_exact_counts and not bounded_region_anchors:
                continue
            terms = proof.full_terms_for_count_value(count_value)
            if terms is None:
                continue
            value = self._build_readonly_reduction_expression_from_terms(
                pointer_param,
                terms,
                constant_bias=int(getattr(proof, "constant_bias", 0) or 0),
                result_size=result_size,
            )
            if value is None:
                continue
            conditions = list(synthesis_base_conditions)
            conditions.append(self._counter_equality_condition(count_param, count_value))
            exact_return = ReturnInfo(
                address=anchor.address,
                value=value,
                conditions=conditions,
                branch_index=10_300 + count_value,
                pcode_identity=anchor.pcode_identity,
                pcode_order=anchor.pcode_order,
                pcode_time=anchor.pcode_time,
                pcode_op_ref=getattr(anchor, "pcode_op_ref", None),
                return_value_pcode_op_refs=tuple(
                    getattr(anchor, "return_value_pcode_op_refs", ()) or ()
                ),
            )
            if bounded_region_anchors:
                insert_at = self._bounded_prefix_exact_insert_index(
                    synthesized,
                    bounded_region_anchors,
                )
                synthesized.insert(insert_at + len(added_for_anchor), exact_return)
            else:
                synthesized.append(exact_return)
            self._debug(
                "Synthesized bounded prefix exact return "
                f"for count={count_value} from proof start_index={proof.start_index} "
                f"terms={[term.byte_offset for term in terms]}"
            )
            added_for_anchor[int(count_value)] = exact_return
            existing_exact_counts.add(count_value)
        for bounded_anchor, bounded_conditions in bounded_region_anchors:
            exact_cover = [
                exact_return
                for count_value, exact_return in sorted(added_for_anchor.items())
                if self._conditions_allow_counter_value(
                    bounded_conditions,
                    count_param,
                    int(count_value),
                )
            ]
            if exact_cover and (
                self._readonly_region_is_covered_by_returns(
                    bounded_conditions,
                    exact_cover,
                )
                or self._readonly_bounded_counter_region_is_covered_by_exact_returns(
                    bounded_conditions,
                    exact_cover,
                    count_param,
                )
            ):
                synthesized = [
                    ret for ret in synthesized
                    if ret is not bounded_anchor
                    and not self._conditions_equivalent_object_centric(
                        ret.conditions or [],
                        bounded_conditions,
                    )
                ]
    return synthesized

def _impl__return_info_matches_reachable_value_pcode_op_ref(
    self,
    ret: ReturnInfo,
    ref: PcodeOpRef,
) -> bool:
    """Match a value op only when ReturnInfo carries that exact value site.

    Def-use proof from a value op to RETURN is represented by separately
    recording the reachable RETURN refs.  This method is intentionally
    strict so a nearby sequence number cannot stand in for reachability.
    """

    if ref is None:
        return False
    return self._return_info_matches_pcode_op_ref(ret, ref)

def _impl__return_info_matches_pcode_op_ref(
    self,
    ret: ReturnInfo,
    ref: PcodeOpRef,
) -> bool:
    if ref is None:
        return False
    ret_ref = getattr(ret, "pcode_op_ref", None)
    if isinstance(ret_ref, PcodeOpRef):
        return ret_ref.stable_key() == ref.stable_key()
    ref_key = ref.stable_key()
    for value_ref in getattr(ret, "return_value_pcode_op_refs", ()) or ():
        if isinstance(value_ref, PcodeOpRef) and value_ref.stable_key() == ref_key:
            return True
    _ret_address, ret_time, ret_order = self._return_info_pcode_site(ret)
    if ret_time is not None and ref.seq_time is not None:
        if int(ret_time) == int(ref.seq_time):
            return self._return_info_address_matches_pcode_ref(ret, ref)
        if self._return_info_matches_adjacent_value_copy(ret, ref, int(ret_time), ret_order):
            return True
        else:
            return False
    if ret_order is not None and ref.seq_order is not None:
        if int(ret_order) != int(ref.seq_order):
            return False
        return self._return_info_address_matches_pcode_ref(ret, ref)
    return False

def _impl__return_info_matches_adjacent_value_copy(
    self,
    ret: ReturnInfo,
    ref: PcodeOpRef,
    ret_time: int,
    ret_order: Optional[int],
) -> bool:
    if getattr(ref, "mnemonic", None) != "COPY" or ref.seq_time is None:
        return False
    if int(ret_time) != int(ref.seq_time) + 1:
        return False
    if ret_order is not None and ref.seq_order is not None and int(ret_order) != int(ref.seq_order) + 1:
        return False
    return self._return_info_address_matches_pcode_ref(ret, ref)

def _impl__pcode_op_ref_from_return_info(
    self,
    ret: ReturnInfo,
) -> Optional[PcodeOpRef]:
    ret_ref = getattr(ret, "pcode_op_ref", None)
    if isinstance(ret_ref, PcodeOpRef):
        return ret_ref
    address_offset, ret_time, ret_order = self._return_info_pcode_site(ret)
    if ret_time is None and ret_order is None:
        return None
    return PcodeOpRef(
        address_offset=address_offset,
        seq_time=None if ret_time is None else int(ret_time),
        seq_order=None if ret_order is None else int(ret_order),
        mnemonic=None,
    )

def _impl__return_info_pcode_site(
    self,
    ret: ReturnInfo,
) -> Tuple[Optional[int], Optional[int], Optional[int]]:
    address_offset = self._return_info_address_offset(ret)
    ret_time = self._coerce_pcode_site_int(getattr(ret, "pcode_time", None))
    ret_order = self._coerce_pcode_site_int(getattr(ret, "pcode_order", None))
    identity = getattr(ret, "pcode_identity", None)
    if isinstance(identity, str):
        identity_address, identity_time, identity_order = self._parse_pcode_site_text(identity)
        if address_offset is None:
            address_offset = identity_address
        if ret_time is None:
            ret_time = identity_time
        if ret_order is None:
            ret_order = identity_order
    return address_offset, ret_time, ret_order

def _impl__varnode_additive_return_contribution_count(
    self,
    start_varnode,
    *,
    budget: int = 128,
) -> int:
    allowed = {
        "INT_ADD",
        "COPY",
        "CAST",
        "INT_ZEXT",
        "INT_SEXT",
        "SUBPIECE",
        "MULTIEQUAL",
    }
    stack = [(start_varnode, 1)]
    seen_coefficients: Dict[Tuple[Any, ...], int] = {}
    return_count = 0
    steps = 0
    while stack and steps < budget:
        current, coefficient = stack.pop()
        steps += 1
        if coefficient <= 0:
            continue
        key = self._varnode_cache_key(current)
        previous = seen_coefficients.get(key)
        if previous is not None and previous >= coefficient:
            continue
        seen_coefficients[key] = coefficient
        for op in self._iter_varnode_descendant_ops(current):
            mnemonic = getattr(op, "getMnemonic", lambda: None)()
            input_multiplicity = self._varnode_input_multiplicity(op, current)
            if input_multiplicity <= 0:
                continue
            if mnemonic == "RETURN":
                return_count += coefficient * input_multiplicity
                if return_count > 1:
                    return 2
                continue
            if mnemonic not in allowed:
                continue
            if mnemonic == "MULTIEQUAL":
                accepted_phi_input = self._multiequal_input_is_accumulator_update(
                    op,
                    current,
                )
                if not accepted_phi_input:
                    self._debug(
                        "Declined vectorized readonly prefix-sum accumulator PHI contribution: "
                        f"phi={self._varnode_cache_key(getattr(op, 'getOutput', lambda: None)())} "
                        f"input={self._varnode_cache_key(current)} "
                        f"reason={self._multiequal_accumulator_update_rejection_reason(op)}"
                    )
                    continue
            output = getattr(op, "getOutput", lambda: None)()
            if output is not None:
                next_coefficient = coefficient
                if mnemonic == "INT_ADD":
                    next_coefficient *= input_multiplicity
                if next_coefficient > 1:
                    return 2
                stack.append((output, next_coefficient))
    return min(return_count, 2)

def _impl__varnode_has_additive_return_contribution(
    self,
    start_varnode,
    *,
    budget: int = 128,
) -> bool:
    allowed = {
        "INT_ADD",
        "COPY",
        "CAST",
        "INT_ZEXT",
        "INT_SEXT",
        "SUBPIECE",
        "MULTIEQUAL",
    }
    stack = [(start_varnode, 1)]
    seen_coefficients: Dict[Tuple[Any, ...], int] = {}
    steps = 0
    while stack and steps < budget:
        current, coefficient = stack.pop()
        steps += 1
        if coefficient != 1:
            return False
        key = self._varnode_cache_key(current)
        previous = seen_coefficients.get(key)
        if previous is not None and previous >= coefficient:
            continue
        seen_coefficients[key] = coefficient
        for op in self._iter_varnode_descendant_ops(current):
            mnemonic = getattr(op, "getMnemonic", lambda: None)()
            input_multiplicity = self._varnode_input_multiplicity(op, current)
            if input_multiplicity <= 0:
                continue
            if mnemonic == "RETURN":
                return True
            if mnemonic not in allowed:
                continue
            if mnemonic == "MULTIEQUAL":
                accepted_phi_input = self._multiequal_input_is_accumulator_update(
                    op,
                    current,
                )
                if not accepted_phi_input:
                    continue
            output = getattr(op, "getOutput", lambda: None)()
            if output is None:
                continue
            next_coefficient = coefficient
            if mnemonic == "INT_ADD":
                next_coefficient *= input_multiplicity
            if next_coefficient != 1:
                return False
            stack.append((output, next_coefficient))
    return False

def _impl__varnode_reaches_return(
    self,
    start_varnode,
    *,
    budget: int = 128,
) -> bool:
    stack = [start_varnode]
    seen = set()
    while stack and len(seen) < budget:
        current = stack.pop()
        if current is None:
            continue
        current_id = id(current)
        if current_id in seen:
            continue
        seen.add(current_id)
        descendants = getattr(current, "getDescendants", lambda: None)()
        if descendants is None:
            continue
        try:
            iterator = iter(descendants)
        except TypeError:
            iterator = None
        if iterator is not None:
            for op in iterator:
                mnemonic = getattr(op, "getMnemonic", lambda: None)()
                if mnemonic == "RETURN":
                    return True
                output = getattr(op, "getOutput", lambda: None)()
                if output is not None:
                    stack.append(output)
            continue
        while descendants.hasNext():
            op = descendants.next()
            mnemonic = getattr(op, "getMnemonic", lambda: None)()
            if mnemonic == "RETURN":
                return True
            output = getattr(op, "getOutput", lambda: None)()
            if output is not None:
                stack.append(output)
    return False

def _impl__reachable_return_op_refs_from_varnodes(
    self,
    start_varnodes: Sequence[object],
    *,
    budget: int = 128,
) -> Tuple[PcodeOpRef, ...]:
    stack = [varnode for varnode in start_varnodes if varnode is not None]
    seen_varnodes = set()
    refs: Dict[Tuple[Any, ...], PcodeOpRef] = {}
    while stack and len(seen_varnodes) < budget:
        current = stack.pop()
        current_id = id(current)
        if current_id in seen_varnodes:
            continue
        seen_varnodes.add(current_id)
        for equivalent in self._high_varnode_instances(current):
            equivalent_id = id(equivalent)
            if equivalent_id not in seen_varnodes:
                seen_varnodes.add(equivalent_id)
            for op in self._iter_varnode_descendant_ops(equivalent):
                mnemonic = getattr(op, "getMnemonic", lambda: None)()
                if mnemonic == "RETURN":
                    ref = self._make_pcode_op_ref(op)
                    if (
                        ref is not None
                        and (
                            ref.address_offset is not None
                            or ref.seq_time is not None
                            or ref.seq_order is not None
                        )
                    ):
                        refs.setdefault(ref.stable_key(), ref)
                    continue
                output = getattr(op, "getOutput", lambda: None)()
                if output is not None:
                    stack.append(output)
    return tuple(sorted(refs.values(), key=lambda ref: repr(ref.stable_key())))

def _impl__reachable_return_value_op_refs_from_varnodes(
    self,
    start_varnodes: Sequence[object],
    *,
    budget: int = 128,
) -> Tuple[PcodeOpRef, ...]:
    value_refs, _return_refs = self._reachable_return_value_and_return_refs_from_varnodes(
        start_varnodes,
        budget=budget,
    )
    return value_refs

def _impl__fp_average_return_value_and_return_refs_from_varnodes(
    self,
    start_varnodes: Sequence[object],
    count_param: dict,
    *,
    budget: int = 128,
) -> Tuple[Tuple[PcodeOpRef, ...], Tuple[PcodeOpRef, ...]]:
    stack: List[Tuple[object, Tuple[PcodeOpRef, ...], bool]] = [
        (varnode, (), False) for varnode in (start_varnodes or ()) if varnode is not None
    ]
    seen_states = set()
    value_refs: Dict[Tuple[Any, ...], PcodeOpRef] = {}
    return_refs: Dict[Tuple[Any, ...], PcodeOpRef] = {}
    passthrough_mnemonics = {
        "COPY",
        "CAST",
        "INT_ZEXT",
        "INT_SEXT",
        "SUBPIECE",
    }
    while stack and len(seen_states) < budget:
        current, path_refs, saw_average_projection = stack.pop()
        for equivalent in self._high_varnode_instances(current):
            state_key = (
                id(equivalent),
                tuple(ref.stable_key() for ref in path_refs),
                bool(saw_average_projection),
            )
            if state_key in seen_states:
                continue
            seen_states.add(state_key)
            for op in self._iter_varnode_descendant_ops(equivalent):
                mnemonic = getattr(op, "getMnemonic", lambda: None)()
                if mnemonic == "RETURN":
                    if not saw_average_projection:
                        continue
                    ref = self._make_pcode_op_ref(op)
                    if (
                        ref is not None
                        and (
                            ref.address_offset is not None
                            or ref.seq_time is not None
                            or ref.seq_order is not None
                        )
                    ):
                        return_refs.setdefault(ref.stable_key(), ref)
                        for value_ref in path_refs:
                            value_refs.setdefault(value_ref.stable_key(), value_ref)
                    continue

                output = getattr(op, "getOutput", lambda: None)()
                if output is None:
                    continue
                next_projection = saw_average_projection
                if mnemonic in passthrough_mnemonics:
                    pass
                elif mnemonic == "FLOAT_ADD" and self._float_add_has_zero_other_operand(op, equivalent):
                    pass
                elif mnemonic == "FLOAT_DIV":
                    if not self._float_div_is_average_projection(op, equivalent, count_param):
                        continue
                    next_projection = True
                else:
                    continue

                ref = self._make_pcode_op_ref(op)
                next_path_refs = path_refs
                if (
                    ref is not None
                    and (
                        ref.address_offset is not None
                        or ref.seq_time is not None
                        or ref.seq_order is not None
                    )
                ):
                    next_path_refs = tuple(path_refs) + (ref,)
                stack.append((output, next_path_refs, next_projection))
    return (
        tuple(sorted(value_refs.values(), key=lambda ref: repr(ref.stable_key()))),
        tuple(sorted(return_refs.values(), key=lambda ref: repr(ref.stable_key()))),
    )

def _impl__direct_return_value_and_return_refs_from_varnodes(
    self,
    start_varnodes: Sequence[object],
    *,
    budget: int = 128,
) -> Tuple[Tuple[PcodeOpRef, ...], Tuple[PcodeOpRef, ...]]:
    """Return refs proven to use the tracked value as the whole return.

    Reachability through an arithmetic op only proves contribution.  A
    scalar accumulator summary may replace a return region only when the
    accumulator value itself reaches RETURN, possibly through value-
    preserving width/passthrough ops.  Vectorized summaries have a separate
    lane-contribution proof and intentionally keep using the broader
    reachability collector after that proof succeeds.
    """

    passthrough_mnemonics = {
        "COPY",
        "CAST",
        "INT_ZEXT",
        "INT_SEXT",
        "SUBPIECE",
    }
    stack: List[Tuple[object, Tuple[PcodeOpRef, ...]]] = [
        (varnode, ()) for varnode in (start_varnodes or ()) if varnode is not None
    ]
    seen_states = set()
    value_refs: Dict[Tuple[Any, ...], PcodeOpRef] = {}
    return_refs: Dict[Tuple[Any, ...], PcodeOpRef] = {}
    while stack and len(seen_states) < budget:
        current, path_refs = stack.pop()
        for equivalent in self._high_varnode_instances(current):
            state_key = (
                id(equivalent),
                tuple(ref.stable_key() for ref in path_refs),
            )
            if state_key in seen_states:
                continue
            seen_states.add(state_key)
            for op in self._iter_varnode_descendant_ops(equivalent):
                mnemonic = getattr(op, "getMnemonic", lambda: None)()
                if mnemonic == "RETURN":
                    ref = self._make_pcode_op_ref(op)
                    if (
                        ref is not None
                        and (
                            ref.address_offset is not None
                            or ref.seq_time is not None
                            or ref.seq_order is not None
                        )
                    ):
                        return_refs.setdefault(ref.stable_key(), ref)
                        for value_ref in path_refs:
                            value_refs.setdefault(value_ref.stable_key(), value_ref)
                    continue
                if mnemonic not in passthrough_mnemonics:
                    if mnemonic != "FLOAT_ADD" or not self._float_add_has_zero_other_operand(op, equivalent):
                        continue
                output = getattr(op, "getOutput", lambda: None)()
                if output is None:
                    continue
                ref = self._make_pcode_op_ref(op)
                next_path_refs = path_refs
                if (
                    ref is not None
                    and (
                        ref.address_offset is not None
                        or ref.seq_time is not None
                        or ref.seq_order is not None
                    )
                ):
                    next_path_refs = tuple(path_refs) + (ref,)
                stack.append((output, next_path_refs))
    return (
        tuple(sorted(value_refs.values(), key=lambda ref: repr(ref.stable_key()))),
        tuple(sorted(return_refs.values(), key=lambda ref: repr(ref.stable_key()))),
    )

def _impl__reachable_return_value_and_return_refs_from_varnodes(
    self,
    start_varnodes: Sequence[object],
    *,
    budget: int = 128,
) -> Tuple[Tuple[PcodeOpRef, ...], Tuple[PcodeOpRef, ...]]:
    stack = [varnode for varnode in start_varnodes if varnode is not None]
    seen_varnodes = set()
    value_refs: Dict[Tuple[Any, ...], PcodeOpRef] = {}
    return_refs: Dict[Tuple[Any, ...], PcodeOpRef] = {}
    while stack and len(seen_varnodes) < budget:
        current = stack.pop()
        current_id = id(current)
        if current_id in seen_varnodes:
            continue
        seen_varnodes.add(current_id)
        for equivalent in self._high_varnode_instances(current):
            equivalent_id = id(equivalent)
            if equivalent_id not in seen_varnodes:
                seen_varnodes.add(equivalent_id)
            for op in self._iter_varnode_descendant_ops(equivalent):
                output = getattr(op, "getOutput", lambda: None)()
                if output is not None:
                    stack.append(output)
                if getattr(op, "getMnemonic", lambda: None)() == "RETURN":
                    ref = self._make_pcode_op_ref(op)
                    if (
                        ref is not None
                        and (
                            ref.address_offset is not None
                            or ref.seq_time is not None
                            or ref.seq_order is not None
                        )
                    ):
                        return_refs.setdefault(ref.stable_key(), ref)
                elif output is not None:
                    reachable_returns = self._reachable_return_op_refs_from_varnodes((output,))
                    if not reachable_returns:
                        ref = None
                    else:
                        for return_ref in reachable_returns:
                            return_refs.setdefault(return_ref.stable_key(), return_ref)
                        ref = self._make_pcode_op_ref(op)
                else:
                    ref = None
                if (
                    ref is not None
                    and (
                        ref.address_offset is not None
                        or ref.seq_time is not None
                        or ref.seq_order is not None
                    )
                ):
                    value_refs.setdefault(ref.stable_key(), ref)
    return (
        tuple(sorted(value_refs.values(), key=lambda ref: repr(ref.stable_key()))),
        tuple(sorted(return_refs.values(), key=lambda ref: repr(ref.stable_key()))),
    )

def _impl__return_is_constant(self, ret: ReturnInfo) -> bool:
    return ret.value is not None and ret.value.expr_type == ExpressionType.CONSTANT

def _impl__summary_working_size(self, narrow_size: int) -> int:
    narrow_bits = max(8, narrow_size * 8)
    wide_bits = max(64, narrow_bits * 2)
    return max(narrow_size, (wide_bits + 7) // 8)

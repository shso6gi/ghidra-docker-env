"""Stateless method implementations extracted from ``scripts.function_tracer_pcode.analysis.analyzer``."""

from __future__ import annotations

from typing import Any, Dict, List, Set, Tuple
from ._shared import (
    Condition,
    ConditionSimplifier,
    DivergenceOutcome,
    Expression,
    ExpressionType,
    FunctionReturnAnalysis,
    Iterable,
    Optional,
    PcodeOpRef,
    ReturnInfo,
    ReturnOutcome,
    StorageInfo,
    UnknownOutcome,
    _TrackedReturnValue,
    _expression_contains_observed_loads,
    _expressions_equivalent,
    attach_quarantined_recurrence_proposal,
    cast,
    cmp_to_key,
    expression_contains_post_state_reads,
    expression_contains_unsupported_smt_ops,
    expression_key_safe,
    replace,
)
from ._api import StructuralRecurrenceSummarizer, accept_summary_return_candidates
from ...model import (
    FunctionOutcomeSeed,
    ReturnValueFlowCertificate,
    ReturnValueFlowStep,
    ReturnPathEvidence,
    SymbolicRegionCandidate,
    TerminalCandidate,
    TerminationContractRef,
    TerminationPathEffectEvidence,
    VarnodeFlowRef,
)
from ...model.structural import expression_key_safe as _outcome_expression_key_safe
from ...model.structural import expression_provenance_key

def invoke(_service_name: str, *args: Any, **kwargs: Any) -> Any:
    implementation_function = globals().get(f"_impl_{_service_name}")
    if implementation_function is None:
        raise AttributeError(_service_name)
    return implementation_function(*args, **kwargs)


def implementation(_service_name: str):
    return globals().get(f"_impl_{_service_name}")

def _impl__return_site_key(self, ret_info: ReturnInfo) -> str:
    return ret_info.site_key()

def _impl__return_site_metadata_from_info(info: ReturnInfo) -> Dict[str, Optional[object]]:
    return {
        "pcode_identity": info.pcode_identity,
        "pcode_order": info.pcode_order,
        "pcode_time": info.pcode_time,
        "pcode_op_ref": info.pcode_op_ref,
        "return_value_pcode_op_refs": tuple(
            getattr(info, "return_value_pcode_op_refs", ()) or ()
        ),
    }

def _impl__return_value_pcode_op_refs_from_varnode(
    self,
    varnode,
) -> Tuple[PcodeOpRef, ...]:
    refs: List[PcodeOpRef] = []
    seen: Set[Tuple[Any, ...]] = set()
    for pcode_op in self._return_value_producer_chain(varnode):
        ref = PcodeOpRef.from_pcode_op(
            pcode_op,
            binary_id=self._binary_id,
            program_uid=self._program_identity(),
            function_entry=self._current_function_entry_address(),
        )
        if ref is None:
            continue
        key = ref.stable_key()
        if key in seen:
            continue
        seen.add(key)
        refs.append(ref)
    return tuple(refs)

def _impl__return_value_producer_chain(varnode, *, max_depth: int = 4) -> Tuple[Any, ...]:
    """Collect the direct return producer plus transparent single-input producers."""
    if varnode is None:
        return ()
    refs: List[Any] = []
    current = varnode
    seen_varnodes: Set[int] = set()
    transparent_single_input_ops = {
        "COPY",
        "CAST",
        "INT_SEXT",
        "INT_ZEXT",
        "SUBPIECE",
    }
    for _depth in range(max(1, int(max_depth))):
        marker = id(current)
        if marker in seen_varnodes:
            break
        seen_varnodes.add(marker)
        get_def = getattr(current, "getDef", None)
        pcode_op = get_def() if callable(get_def) else None
        if pcode_op is None:
            break
        refs.append(pcode_op)
        try:
            mnemonic = str(pcode_op.getMnemonic() or "")
        except Exception:
            break
        if mnemonic not in transparent_single_input_ops:
            break
        try:
            input_count = int(pcode_op.getNumInputs())
        except Exception:
            break
        if input_count != 1:
            break
        try:
            current = pcode_op.getInput(0)
        except Exception:
            break
    return tuple(refs)

def _impl__site_metadata_with_return_value_pcode_op_refs(
    self,
    site_metadata: Optional[Dict[str, Optional[object]]],
    *,
    return_varnode=None,
    producer_op=None,
    tracer=None,
) -> Dict[str, Optional[object]]:
    metadata: Dict[str, Optional[object]] = dict(site_metadata or {})
    refs: List[PcodeOpRef] = [
        ref
        for ref in (metadata.get("return_value_pcode_op_refs") or ())
        if isinstance(ref, PcodeOpRef)
    ]
    if producer_op is not None:
        producer_ref = PcodeOpRef.from_pcode_op(
            producer_op,
            binary_id=self._binary_id,
            program_uid=self._program_identity(),
            function_entry=self._current_function_entry_address(),
        )
        if producer_ref is not None:
            refs.append(producer_ref)
    refs.extend(self._return_value_pcode_op_refs_from_varnode(return_varnode))
    deduped: List[PcodeOpRef] = []
    seen: Set[Tuple[Any, ...]] = set()
    for ref in refs:
        key = ref.stable_key()
        if key in seen:
            continue
        seen.add(key)
        deduped.append(ref)
    metadata["return_value_pcode_op_refs"] = tuple(deduped)
    certificate = _build_return_value_flow_certificate(
        self,
        metadata,
        return_varnode=return_varnode,
        tracer=tracer,
    )
    if certificate is not None:
        metadata["return_value_flow_certificate"] = certificate
    return metadata


def _build_return_value_flow_certificate(
    self,
    metadata: Dict[str, Optional[object]],
    *,
    return_varnode,
    tracer=None,
) -> Optional[ReturnValueFlowCertificate]:
    """Capture exact Varnode edges from RETURN input to an extension payload."""

    return_op = metadata.get("_return_op_object")
    return_op_ref = metadata.get("pcode_op_ref")
    if return_op is None or not isinstance(return_op_ref, PcodeOpRef) or return_varnode is None:
        return None
    try:
        if str(return_op.getMnemonic() or "").upper() != "RETURN":
            return None
        if int(return_op.getNumInputs()) <= 1 or return_op.getInput(1) is not return_varnode:
            return None
    except Exception:
        return None
    return_input_ref = VarnodeFlowRef.from_varnode(return_varnode)
    if return_input_ref is None:
        return None

    steps: List[ReturnValueFlowStep] = []
    extension_indices: List[int] = []
    extension_payload_varnode = None
    current = return_varnode
    for pcode_op in self._return_value_producer_chain(return_varnode):
        try:
            output = pcode_op.getOutput()
            if output is not current:
                return None
            input_count = int(pcode_op.getNumInputs())
            inputs = tuple(pcode_op.getInput(index) for index in range(input_count))
            if input_count != 1:
                return None
        except Exception:
            return None
        op_ref = PcodeOpRef.from_pcode_op(
            pcode_op,
            binary_id=self._binary_id,
            program_uid=self._program_identity(),
            function_entry=self._current_function_entry_address(),
        )
        output_ref = VarnodeFlowRef.from_varnode(output)
        input_refs = tuple(VarnodeFlowRef.from_varnode(item) for item in inputs)
        if op_ref is None or output_ref is None or any(item is None for item in input_refs):
            return None
        mnemonic = str(op_ref.mnemonic or "").upper()
        if mnemonic in {"INT_ZEXT", "INT_SEXT"}:
            extension_indices.append(len(steps))
            extension_payload_varnode = inputs[0]
        steps.append(ReturnValueFlowStep(
            op_ref=op_ref,
            output_ref=output_ref,
            input_refs=cast(Tuple[VarnodeFlowRef, ...], input_refs),
            traversed_input_index=0,
        ))
        current = inputs[0]

    if len(extension_indices) > 1:
        return None
    payload_identity: Tuple[Any, ...] = ()
    if extension_payload_varnode is not None and tracer is not None:
        try:
            payload_expr = tracer.trace_varnode(extension_payload_varnode, use_cache=False)
            if payload_expr is not None:
                payload_identity = tuple(expression_provenance_key(payload_expr))
        except Exception:
            payload_identity = ()
    return ReturnValueFlowCertificate(
        return_op_ref=return_op_ref,
        return_input_index=1,
        return_input_ref=return_input_ref,
        steps=tuple(steps),
        extension_step_index=(extension_indices[0] if extension_indices else None),
        payload_expression_identity=payload_identity,
    )

def _impl__make_return_info(
    self,
    *,
    address: str,
    value: Expression,
    conditions: List[Condition],
    branch_index: Optional[int] = None,
    site_metadata: Optional[Dict[str, Optional[object]]] = None,
) -> ReturnInfo:
    site_metadata = site_metadata or {}
    return_path_evidence = cast(
        Optional[ReturnPathEvidence], site_metadata.get("return_path_evidence")
    )
    if return_path_evidence is not None:
        target_guard_keys = (tuple(sorted(
            (condition.structural_key() for condition in (conditions or ())), key=repr
        )),)
        if tuple(return_path_evidence.path_guard_keys) != target_guard_keys:
            original_key = return_path_evidence.stable_key()
            return_path_evidence = replace(
                return_path_evidence,
                path_guard_keys=target_guard_keys,
                guard_rewrite_proof_keys=(
                    (
                        "return_extraction_guard_materialization_v1",
                        original_key,
                        target_guard_keys,
                    ),
                ),
            )
    return ReturnInfo(
        address=address,
        value=value,
        conditions=list(conditions or []),
        branch_index=branch_index,
        pcode_identity=cast(Optional[str], site_metadata.get("pcode_identity")),
        pcode_order=self._coerce_optional_int(site_metadata.get("pcode_order")),
        pcode_time=self._coerce_optional_int(site_metadata.get("pcode_time")),
        pcode_op_ref=cast(Optional[PcodeOpRef], site_metadata.get("pcode_op_ref")),
        return_value_pcode_op_refs=tuple(
            ref
            for ref in (site_metadata.get("return_value_pcode_op_refs") or ())
            if isinstance(ref, PcodeOpRef)
        ),
        return_value_flow_certificate=cast(
            Optional[ReturnValueFlowCertificate],
            site_metadata.get("return_value_flow_certificate"),
        ),
        return_path_evidence=return_path_evidence,
    )

def _impl__dump_return_infos(self, analysis: FunctionReturnAnalysis):
    """
    ReturnInfo一覧をダンプ（デバッグ用）

    各ReturnInfoについて以下を出力：
    - branch_index（分岐識別子）
    - address（アドレス）
    - value（式の文字列表現とSMT表現）
    - conditions（簡約後の条件リスト）
    """
    if not self.debug:
        return

    self._debug_print("=" * 60)
    self._debug_print(f"ReturnInfo dump for {analysis.function_name}")
    self._debug_print(f"Total return candidates: {len(analysis.returns)}")
    if analysis.analysis_notes:
        self._debug_print(f"Analysis notes: {analysis.analysis_notes}")
    self._debug_print("=" * 60)

    for i, ret_info in enumerate(analysis.returns):
        self._debug_print(f"[{i}] branch_index={ret_info.branch_index}")
        self._debug_print(f"    address: {ret_info.address}", 1)
        if ret_info.pcode_identity is not None:
            self._debug_print(f"    pcode_identity: {ret_info.pcode_identity}", 1)
        if ret_info.pcode_time is not None or ret_info.pcode_order is not None:
            self._debug_print(
                f"    seq(time={ret_info.pcode_time}, order={ret_info.pcode_order})",
                1,
            )
        if getattr(ret_info, "return_kind", "exact") != "exact":
            self._debug_print(f"    return_kind: {ret_info.return_kind}", 1)
        if getattr(ret_info, "summary_candidate_source_key", None) is not None:
            self._debug_print(
                f"    summary_candidate_source_key: {ret_info.summary_candidate_source_key}",
                1,
            )

        # 値の文字列表現
        try:
            value_str = self._debug_expr_summary(ret_info.value)
            self._debug_print(f"    value: {value_str}", 1)
        except Exception as e:
            self._debug_print(f"    value: (error converting to string: {e})", 1)

        # SMT表現（エラー時はスキップ）- 引数なし
        try:
            smt_str = ret_info.value.to_smt()
            # 長すぎる場合は切り詰め
            if len(smt_str) > 300:
                smt_str = smt_str[:300] + "..."
            self._debug_print(f"    smt: {smt_str}", 1)
        except Exception as e:
            self._debug_print(f"    smt: (error: {e})", 1)

        # 条件リスト（簡約版）
        if ret_info.conditions:
            try:
                cond_strs = [ConditionSimplifier.get_simplified_condition_string(c)
                            for c in ret_info.conditions]
                self._debug_print(f"    conditions({len(ret_info.conditions)}): {cond_strs}", 1)
            except Exception as e:
                self._debug_print(f"    conditions: (error: {e})", 1)
        else:
            self._debug_print(f"    conditions: (unconditional/always)", 1)

    self._debug_print("=" * 60)

    # 条件カバレッジの簡易チェック
    self._check_condition_coverage(analysis)

def _impl__try_pre_return_counted_loop_summary(
    self,
    *,
    function,
    high_function,
    tracer: PcodeTracer,
    parameters: Sequence[Dict],
    return_ops: Sequence,
    current_function_ref: CallTargetRef,
    analysis_scope_key,
    return_type: Optional[str],
    return_type_obj,
    signedness_result: Optional[SignednessResult],
    effect_summary: EffectSummary,
) -> Optional[FunctionReturnAnalysis]:
    if not self._effect_summary_allows_pre_return_structural_summary(
        effect_summary,
        function=function,
        high_function=high_function,
        return_type=return_type,
        return_type_obj=return_type_obj,
    ):
        return None

    anchor = self._make_pre_return_summary_anchor(function, return_ops)
    skeleton = FunctionReturnAnalysis(
        function_name=function.getName(),
        entry_point=str(function.getEntryPoint()),
        parameters=list(parameters or []),
        returns=[anchor],
        function_ref=current_function_ref,
        analysis_scope_key=analysis_scope_key,
        return_type=return_type,
        return_type_obj=return_type_obj,
        signedness_result=signedness_result,
        deferred_calls=dict(self._current_deferred_calls),
        effect_summary=effect_summary,
        program_is_big_endian=self._program_is_big_endian(),
        binary_id=self._binary_id,
    )
    summarizer = StructuralRecurrenceSummarizer(
        tracer,
        debug=self.debug,
        enable_completed_recovery_proofs=self.enable_completed_recovery_proofs,
    )
    summary = summarizer.try_summarize_pre_return_counted_scalar_loop(
        function,
        high_function,
        skeleton,
        return_ops,
    )
    if summary is None:
        return None

    summary_returns, summary_note = summary
    try:
        proposal = attach_quarantined_recurrence_proposal(
            skeleton,
            proposed_returns=summary_returns,
            summary_note=summary_note,
        )
    except (TypeError, ValueError):
        return None
    if proposal is None:
        return None
    result = skeleton
    if summary_note not in result.analysis_notes:
        result.analysis_notes.append(summary_note)
    if "pre_return_counted_loop_summary" not in result.analysis_notes:
        result.analysis_notes.append("pre_return_counted_loop_summary")
    result.unknown_event_count = len(tracer.unknown_tracker.events)
    result.unknown_event_reasons = sorted(
        {
            getattr(event, "reason_str", None) or getattr(event.reason, "value", "unknown")
            for event in tracer.unknown_tracker.events
        }
    )
    self._synchronize_parameters_with_referenced_parameter_expressions(result)
    self._repair_mixed_scalar_signedness(result)
    self._normalize_return_partition(result)
    self._mark_incomplete_control_flow(result)
    self._dump_return_infos(result)
    return result

def _impl__make_pre_return_summary_anchor(
    self,
    function,
    return_ops: Sequence,
) -> ReturnInfo:
    return_op = next(iter(return_ops or []), None)
    seqnum = getattr(return_op, "getSeqnum", lambda: None)() if return_op is not None else None
    address = str(getattr(seqnum, "getTarget", lambda: function.getEntryPoint())())
    pcode_time = getattr(seqnum, "getTime", lambda: None)()
    pcode_order = getattr(seqnum, "getOrder", lambda: None)()
    anchor = self._make_return_info(
        address=address,
        value=Expression.unknown("pre_return_counted_loop_candidate"),
        conditions=[],
        branch_index=20_000,
        site_metadata={
            "pcode_identity": (
                f"{address}:t{pcode_time}:o{pcode_order}"
                if pcode_time is not None and pcode_order is not None
                else None
            ),
            "pcode_time": pcode_time,
            "pcode_order": pcode_order,
            "pcode_op_ref": PcodeOpRef.from_pcode_op(
                return_op,
                binary_id=self._binary_id,
                program_uid=self._program_identity(),
                function_entry=self._function_entry_address(function),
            ),
        },
    )
    anchor.return_kind = "summary_anchor"
    anchor.acceptance_status = "anchor"
    return anchor

def _impl__function_body_has_phase1_pure_return_forbidden_ops(self, function) -> bool:
    if function is None:
        return False
    program = getattr(self, "program", None)
    listing_getter = getattr(program, "getListing", None)
    body_getter = getattr(function, "getBody", None)
    if not callable(listing_getter) or not callable(body_getter):
        return True
    try:
        listing = listing_getter()
        body = body_getter()
    except Exception:
        return True
    if listing is None or body is None:
        return True
    get_instructions = getattr(listing, "getInstructions", None)
    if not callable(get_instructions):
        return True
    try:
        instructions = get_instructions(body, True)
    except TypeError:
        try:
            instructions = get_instructions(body)
        except Exception:
            return True
    except Exception:
        return True
    saw_op = False
    instruction_items, complete = self._collect_java_or_python_iterable(instructions)
    if not complete:
        return True
    for instruction in instruction_items:
        if instruction is None:
            return True
        try:
            pcode_ops = instruction.getPcode()
        except Exception:
            return True
        op_items, complete = self._collect_java_or_python_iterable(pcode_ops)
        if not complete:
            return True
        for op in op_items:
            saw_op = True
            mnemonic = getattr(op, "getMnemonic", lambda: None)()
            if str(mnemonic or "").strip().upper() == "BRANCH":
                if self._phase1_direct_branch_escapes_function_body(instruction, body):
                    return True
                continue
            if self._phase1_pure_return_forbids_mnemonic(mnemonic):
                return True
    return not saw_op

def _impl__high_function_has_phase1_pure_return_forbidden_ops(self, high_function) -> bool:
    if high_function is None:
        return True
    saw_op = False
    blocks, complete = self._collect_java_or_python_iterable(
        getattr(high_function, "getBasicBlocks", lambda: None)()
        if callable(getattr(high_function, "getBasicBlocks", None))
        else None
    )
    if not complete:
        return True
    for block in blocks:
        ops, complete = self._collect_java_or_python_iterable(
            getattr(block, "getIterator", lambda: None)()
        )
        if not complete:
            return True
        for op in ops:
            saw_op = True
            mnemonic = getattr(op, "getMnemonic", lambda: None)()
            if self._phase1_pure_return_forbids_mnemonic(mnemonic):
                return True
    return not saw_op

def _impl__phase1_pure_return_forbids_mnemonic(mnemonic: Optional[str]) -> bool:
    name = str(mnemonic or "").strip().upper()
    if not name:
        return True
    if name in {"CALL", "CALLIND", "STORE", "LOAD", "BRANCHIND", "CALLOTHER"}:
        return True
    if "FLOAT" in name or name in {"INT2FLOAT", "FLOAT2INT"}:
        return True
    return False

def _impl__phase1_return_type_is_float(return_type: Optional[str], return_type_obj=None) -> bool:
    texts = [return_type, str(return_type_obj) if return_type_obj is not None else None]
    for text in texts:
        normalized = str(text or "").strip().lower()
        if not normalized:
            continue
        if any(token in normalized for token in ("float", "double", "longdouble", "long double")):
            return True
    return False

def _impl__apply_outcome_partition_summaries(
    self,
    function,
    high_function,
    analysis: FunctionReturnAnalysis,
) -> None:
    if analysis is None:
        return
    self._clear_outcome_partition_summaries(analysis)
    applied = self._try_apply_triangular_mod_caller_outcomes(high_function, analysis)
    if not applied:
        applied = self._try_apply_triangular_mod_optimized_outcomes(high_function, analysis)
    if not applied:
        applied = self._try_apply_branch_guarded_while_outcomes(high_function, analysis)
    if not applied:
        self._try_apply_single_guard_nonprogress_loop_outcomes(high_function, analysis)
    _produce_standard_termination_path_effect_evidence(self, analysis)
    _build_function_outcome_seed(analysis)


def _termination_external_provenance(target_ref) -> Optional[Tuple[Any, ...]]:
    if target_ref is None or not target_ref.is_function():
        return None
    if target_ref.is_external is True and target_ref.library_name:
        return ("external_import", str(target_ref.library_name).lower())
    if (
        target_ref.is_thunk is True
        and target_ref.thunked_is_external is True
        and target_ref.thunked_library_name
    ):
        return ("verified_external_thunk", str(target_ref.thunked_library_name).lower())
    return None


def _termination_signature_key(target_ref, expected_parameter_count: int) -> Optional[Tuple[Any, ...]]:
    function = getattr(target_ref, "function_obj", None)
    if function is None:
        return None
    try:
        parameter_count = int(function.getParameterCount())
    except Exception:
        try:
            parameter_count = len(tuple(function.getParameters() or ()))
        except Exception:
            return None
    if parameter_count != int(expected_parameter_count):
        return None
    try:
        parameters = tuple(function.getParameters() or ())
        parameter_type_names = tuple(
            str(parameter.getDataType().getName()).strip().lower()
            for parameter in parameters
        )
    except Exception:
        return None
    if len(parameter_type_names) != parameter_count or any(
        name not in {"int", "signed int", "int32_t"} for name in parameter_type_names
    ):
        return None
    try:
        return_type = function.getReturnType()
        return_name = str(getattr(return_type, "getName", lambda: return_type)()).lower()
    except Exception:
        return None
    if "void" not in return_name:
        return None
    return ("c_abi_signature_v1", "void", parameter_type_names)


def _standard_termination_contract_descriptor(target_ref) -> Optional[Dict[str, Any]]:
    """Return a fully modeled ABI contract; names alone never classify a target."""
    provenance = _termination_external_provenance(target_ref)
    if provenance is None:
        return None
    library = str(provenance[1]).lower().rsplit("/", 1)[-1]
    if not (library == "libc" or library.startswith("libc.so")):
        return None
    raw_name = str(getattr(target_ref, "function_name", None) or "").split("@", 1)[0]
    symbol = raw_name.rsplit("::", 1)[-1]
    # Only _Exit has a bounded observation contract here.  exit/quick_exit,
    # abort/assert failures, traps, and longjmp have cleanup/signal/diagnostic
    # or state-restoration effects that this lane intentionally leaves UNKNOWN.
    if symbol not in {"_Exit", "_exit"}:
        return None
    signature = _termination_signature_key(target_ref, 1)
    if signature is None:
        return None
    callee_contract_key = (
        "termination_callee_contract_v1",
        target_ref.stable_key(),
        provenance,
        symbol,
        signature,
    )
    return {
        "termination_class": "process",
        "semantic_subtype": "immediate_process_exit",
        "payload_schema": "process_exit_payload_v1",
        "callee_contract_key": callee_contract_key,
        "effect_contract": (
            "termination_effect_v2", "process", "immediate_process_exit",
            ("atexit_handlers", False),
            ("quick_exit_handlers", False),
            ("stdio_flush", False),
            ("automatic_object_cleanup", False),
        ),
        "observation_contract": (
            "termination_observation_v2", "process",
            ("process_exit_status", True),
            ("pretermination_memory_effects", "compared_separately"),
        ),
    }


def _produce_standard_termination_path_effect_evidence(self, analysis: FunctionReturnAnalysis) -> None:
    profile = getattr(getattr(analysis, "effect_summary", None), "function_control_effect_profile", None)
    if not callable(getattr(profile, "stable_key", None)):
        analysis.termination_path_effect_evidence = ()
        return
    profile_key = profile.stable_key()
    raw_profile_ops = getattr(profile, "region_pcode_op_keys", ())
    if not (
        isinstance(profile_key, tuple)
        and profile_key[:1] == ("function_control_effect_profile",)
        and isinstance(raw_profile_ops, (tuple, list))
    ):
        analysis.termination_path_effect_evidence = ()
        return
    profile_ops = set(raw_profile_ops)
    produced = []
    unknown_nonreturning = []
    for observation in tuple(getattr(self, "_current_noreturn_terminal_observations", ()) or ()):
        op_ref = observation.get("pcode_op_ref")
        targets = tuple(observation.get("target_refs") or ())
        noreturn_contract_keys = tuple(observation.get("noreturn_contract_keys") or ())
        descriptors = tuple(_standard_termination_contract_descriptor(target) for target in targets)
        guard = tuple(observation.get("conditions") or ())
        if (
            not isinstance(op_ref, PcodeOpRef)
            or op_ref.stable_key() not in profile_ops
            or not targets
            or len(noreturn_contract_keys) != len(targets)
            or any(
                not isinstance(key, tuple)
                or len(key) != 3
                or key[0] != "resolved_noreturn_function_v1"
                or tuple(key[1]) != tuple(target.stable_key())
                for key, target in zip(noreturn_contract_keys, targets)
            )
            or any(descriptor is None for descriptor in descriptors)
            or len({repr(descriptor) for descriptor in descriptors}) != 1
        ):
            unknown_nonreturning.append(UnknownOutcome(
                guard=guard,
                reason="unknown_nonreturning_contract",
                evidence={
                    "terminal_op_ref": op_ref.stable_key() if isinstance(op_ref, PcodeOpRef) else None,
                    "target_keys": tuple(target.stable_key() for target in targets),
                    "noreturn_contract_keys": noreturn_contract_keys,
                },
            ))
            continue
        descriptor = descriptors[0]
        termination_class = descriptor["termination_class"]
        terminal_id = ("termination_terminal", op_ref.stable_key())
        guard_key = tuple(sorted((condition.structural_key() for condition in guard), key=repr))
        source_key = (
            "terminal_path_effect_evidence_v1", op_ref.stable_key(), profile_key, guard_key,
        )
        contract = TerminationContractRef(
            termination_class=termination_class,
            object_identity_key=op_ref.stable_key(),
            payload_key=(
                descriptor["payload_schema"], descriptor["semantic_subtype"],
                descriptor["callee_contract_key"],
                tuple(observation.get("argument_keys") or ()),
            ),
            effect_key=descriptor["effect_contract"],
            observation_contract_key=descriptor["observation_contract"],
            source_contract_key=source_key,
        )
        produced.append(TerminationPathEffectEvidence(
            terminal_candidate_id=terminal_id,
            terminal_op_ref=op_ref,
            control_effect_profile_key=profile_key,
            path_guard_key=guard_key,
            contract=contract,
            path_guard=guard,
        ))
    analysis.termination_path_effect_evidence = tuple(produced)
    if unknown_nonreturning:
        analysis.unknown_outcomes = tuple(getattr(analysis, "unknown_outcomes", ()) or ()) + tuple(
            unknown_nonreturning
        )


def _build_function_outcome_seed(analysis: FunctionReturnAnalysis) -> None:
    terminals = []
    regions = []
    terminal_ids = set()
    return_sources = tuple(getattr(analysis, "return_outcomes", ()) or ())
    if not return_sources:
        return_sources = tuple(
            ReturnOutcome(
                guard=tuple(getattr(info, "conditions", ()) or ()),
                value=info.value,
                provenance={"source": "extracted_return"},
                return_info=info,
            )
            for info in (getattr(analysis, "returns", ()) or ())
        )
    for index, outcome in enumerate(return_sources):
        info = getattr(outcome, "return_info", None)
        op_ref = getattr(info, "pcode_op_ref", None)
        terminal_id = (
            "return_terminal",
            op_ref.stable_key() if op_ref is not None else getattr(info, "site_key", lambda: index)(),
        )
        if terminal_id not in terminal_ids:
            terminal_ids.add(terminal_id)
            terminals.append(TerminalCandidate(
                candidate_id=terminal_id,
                terminal_kind_candidate="return",
                op_ref=op_ref,
                cfg_reachable=None,
                evidence_key=("existing_return_terminal", terminal_id),
            ))
        regions.append(SymbolicRegionCandidate(
            candidate_id=("return_region", terminal_id),
            terminal_candidate_id=terminal_id,
            guard=tuple(getattr(outcome, "guard", ()) or ()),
            guard_extraction_complete=False,
            producer_evidence_key=(
                "return_path_evidence",
                info.return_path_evidence.stable_key(),
            ) if info is not None and info.return_path_evidence is not None else (
                "return_path_evidence_missing",
                _outcome_expression_key_safe(getattr(outcome, "value", None)),
            ),
            observed_value=getattr(outcome, "value", None),
        ))
    for index, outcome in enumerate(getattr(analysis, "divergence_outcomes", ()) or ()):
        terminal_id = ("must_diverge_terminal", index, getattr(analysis, "entry_point", None))
        terminals.append(TerminalCandidate(
            candidate_id=terminal_id,
            terminal_kind_candidate="must_diverge",
            cfg_reachable=None,
            evidence_key=("divergence_candidate", index),
        ))
        regions.append(SymbolicRegionCandidate(
            candidate_id=("must_diverge_region", terminal_id),
            terminal_candidate_id=terminal_id,
            guard=tuple(getattr(outcome, "guard", ()) or ()),
            guard_extraction_complete=False,
            producer_evidence_key=("divergence_candidate", index),
        ))
    for index, outcome in enumerate(getattr(analysis, "unknown_outcomes", ()) or ()):
        terminal_id = ("unknown_terminal", index, getattr(analysis, "entry_point", None))
        terminals.append(TerminalCandidate(
            candidate_id=terminal_id,
            terminal_kind_candidate="unknown",
            cfg_reachable=None,
            evidence_key=("unknown_outcome", str(getattr(outcome, "reason", "unknown"))),
        ))
        regions.append(SymbolicRegionCandidate(
            candidate_id=("unknown_region", terminal_id),
            terminal_candidate_id=terminal_id,
            guard=tuple(getattr(outcome, "guard", ()) or ()),
            guard_extraction_complete=False,
            producer_evidence_key=("unknown_outcome", str(getattr(outcome, "reason", "unknown"))),
        ))
    for evidence in tuple(getattr(analysis, "termination_path_effect_evidence", ()) or ()):
        contract = evidence.contract
        kind = {
            "process": "process_termination",
            "exceptional": "exceptional_termination",
            "nonlocal_control_transfer": "nonlocal_control_transfer",
        }.get(contract.termination_class)
        if kind is None:
            continue
        terminals.append(TerminalCandidate(
            candidate_id=evidence.terminal_candidate_id,
            terminal_kind_candidate=kind,
            op_ref=evidence.terminal_op_ref,
            cfg_reachable=None,
            evidence_key=evidence.stable_key(),
            termination_contract=contract,
        ))
        regions.append(SymbolicRegionCandidate(
            candidate_id=("termination_region", evidence.terminal_candidate_id),
            terminal_candidate_id=evidence.terminal_candidate_id,
            guard=tuple(evidence.path_guard),
            guard_extraction_complete=True,
            producer_evidence_key=contract.source_contract_key,
        ))
    unresolved = []
    profile = getattr(getattr(analysis, "effect_summary", None), "function_control_effect_profile", None)
    control_flow_evidence_key = ()
    if callable(getattr(profile, "stable_key", None)):
        candidate_profile_key = profile.stable_key()
        if (
            isinstance(candidate_profile_key, tuple)
            and candidate_profile_key
            and candidate_profile_key[0] == "function_control_effect_profile"
        ):
            control_flow_evidence_key = candidate_profile_key
    if getattr(analysis, "incomplete_control_flow", False):
        unresolved.append(("incomplete_control_flow",))
    for reason in getattr(analysis, "unknown_event_reasons", ()) or ():
        if any(token in str(reason).lower() for token in ("branch", "control", "terminal", "callind")):
            unresolved.append(("analysis_unknown", str(reason)))
    analysis.outcome_seed = FunctionOutcomeSeed(
        function_identity=analysis.outcome_function_identity(),
        input_domain_contract=(
            "parameter_domain_v1",
            tuple(
                (item.get("index"), item.get("size"), item.get("data_type"), item.get("is_signed"))
                for item in (getattr(analysis, "parameters", ()) or ())
            ),
        ),
        terminal_candidates=tuple(terminals),
        symbolic_regions=tuple(regions),
        unresolved_control_evidence=tuple(unresolved),
        control_flow_evidence_key=tuple(control_flow_evidence_key or ()),
        partition_revision=int(getattr(analysis, "partition_revision", 0) or 0),
    )

def _impl__clear_outcome_partition_summaries(self, analysis: FunctionReturnAnalysis) -> None:
    """Drop synthetic outcome partition state before rebuilding it from current returns."""
    analysis.return_outcomes = ()
    analysis.divergence_outcomes = ()
    analysis.unknown_outcomes = ()

def _impl__try_apply_single_guard_nonprogress_loop_outcomes(
    self,
    high_function,
    analysis: FunctionReturnAnalysis,
) -> bool:
    if len(getattr(analysis, "parameters", []) or []) != 1:
        self._debug_print("Outcome loop summary declined: expected one parameter")
        return False
    if len(getattr(analysis, "returns", []) or []) != 1:
        self._debug_print("Outcome loop summary declined: expected one return")
        return False
    if getattr(analysis, "deferred_calls", None):
        self._debug_print("Outcome loop summary declined: deferred calls present")
        return False
    if self._high_function_has_forbidden_control_outcome_ops(high_function, allow_call=False):
        self._debug_print("Outcome loop summary declined: forbidden control/effect op present")
        return False
    if self._high_function_cbranch_count(high_function) < 1:
        self._debug_print("Outcome loop summary declined: no control guard")
        return False

    ret = analysis.returns[0]
    if self._constant_int_value(ret.value) != 0:
        self._debug_print("Outcome loop summary declined: return value is not zero")
        return False
    if len(ret.conditions or ()) != 1:
        self._debug_print("Outcome loop summary declined: expected one return guard")
        return False
    param = self._parameter_expression(analysis, 0)
    if param is None:
        self._debug_print("Outcome loop summary declined: parameter expression unavailable")
        return False
    nonpositive = self._signed_positive_condition(param).negate()
    if not (
        self._conditions_equivalent(ret.conditions, [nonpositive])
        or (
            len(ret.conditions or ()) == 1
            and self._condition_is_signed_nonpositive_of_param(ret.conditions[0], param)
        )
    ):
        self._debug_print("Outcome loop summary declined: return guard is not param nonpositive")
        return False
    divergence_guard = self._signed_positive_condition(param)

    analysis.return_outcomes = (
        ReturnOutcome(
            guard=tuple(ret.conditions or ()),
            value=ret.value,
            provenance={"source": "existing_return_partition"},
            return_info=ret,
        ),
    )
    divergence_proof = self._prove_single_guard_nonprogress_region_must_diverge(
        high_function,
        analysis,
        divergence_guard=divergence_guard,
        param=param,
    )
    if divergence_proof is not None:
        analysis.divergence_outcomes = (
            DivergenceOutcome(
                guard=(divergence_guard,),
                proof=divergence_proof,
            ),
        )
        analysis.unknown_outcomes = ()
        if "outcome_partition_proved_nonprogress_loop_divergence" not in analysis.analysis_notes:
            analysis.analysis_notes.append("outcome_partition_proved_nonprogress_loop_divergence")
    else:
        analysis.divergence_outcomes = ()
        analysis.unknown_outcomes = (
            UnknownOutcome(
                guard=(divergence_guard,),
                reason="must_diverge_proof_missing",
                evidence={
                    "candidate_rule": "side_effect_free_nonprogress_loop_guard_complement",
                    "loop_has_cfg_cycle": self._high_function_has_cfg_cycle(high_function),
                    "nonreturning_region_candidate": self._high_function_has_nonreturning_region_candidate(high_function),
                    "has_control_guard": self._high_function_cbranch_count(high_function) > 0,
                    "forbidden_ops_absent": True,
                    "return_guard_equivalent_to_param_nonpositive": True,
                    "missing_proof": "scc_exit_impossibility_and_guard_preservation",
                },
            ),
        )
        if "outcome_partition_unknown_nonprogress_loop" not in analysis.analysis_notes:
            analysis.analysis_notes.append("outcome_partition_unknown_nonprogress_loop")
    return True

def _impl__analysis_has_positive_region_outcome_obligation(
    self,
    analysis: Optional[FunctionReturnAnalysis],
) -> bool:
    if analysis is None:
        return False
    if len(getattr(analysis, "parameters", []) or []) != 1:
        return False
    param = self._parameter_expression(analysis, 0)
    if param is None:
        return False
    return_outcomes = tuple(getattr(analysis, "return_outcomes", ()) or ())
    unknown_outcomes = tuple(getattr(analysis, "unknown_outcomes", ()) or ())
    divergence_outcomes = tuple(getattr(analysis, "divergence_outcomes", ()) or ())
    if len(return_outcomes) != 1 or not (unknown_outcomes or divergence_outcomes):
        return False
    ret = return_outcomes[0]
    if self._constant_int_value(getattr(ret, "value", None)) != 0:
        return False
    nonpositive = self._signed_positive_condition(param).negate()
    if not (
        self._conditions_equivalent(tuple(getattr(ret, "guard", ()) or ()), [nonpositive])
        or (
            len(tuple(getattr(ret, "guard", ()) or ())) == 1
            and self._condition_is_signed_nonpositive_of_param(tuple(getattr(ret, "guard", ()) or ())[0], param)
        )
    ):
        return False
    positive = self._signed_positive_condition(param)
    for outcome in (*unknown_outcomes, *divergence_outcomes):
        guard = tuple(getattr(outcome, "guard", ()) or ())
        if self._conditions_equivalent(guard, [positive]) or (
            len(guard) == 1
            and self._condition_is_signed_positive_of_param(guard[0], param)
        ):
            return True
    return False

def _impl__acc_phi_flows_to_return_origin_phi(
    self,
    acc_phi,
    return_origin_keys: Set[Tuple[Any, ...]],
    *,
    summarizer: StructuralRecurrenceSummarizer,
    high_function,
) -> bool:
    if acc_phi is None or not return_origin_keys:
        return False
    acc_phi_key = self._pcode_op_stable_key(acc_phi)
    if not isinstance(acc_phi_key, tuple):
        return False
    for block in summarizer._iter_basic_blocks(high_function):
        for op in summarizer._iter_block_ops(block):
            if getattr(op, "getMnemonic", lambda: None)() != "MULTIEQUAL":
                continue
            op_key = self._pcode_op_stable_key(op)
            if op_key not in return_origin_keys:
                continue
            if self._pcode_op_input_def_reaches_phi(
                op,
                acc_phi_key,
                max_depth=8,
            ):
                return True
            if self._return_origin_phi_has_acc_output_input(op, acc_phi):
                return True
    return False

def _impl__return_origin_phi_has_acc_output_input(self, return_phi, acc_phi) -> bool:
    acc_output = getattr(acc_phi, "getOutput", lambda: None)()
    if acc_output is None:
        return False
    acc_parent = getattr(acc_phi, "getParent", lambda: None)()
    return_parent = getattr(return_phi, "getParent", lambda: None)()
    if acc_parent is None or return_parent is None:
        return False
    try:
        input_count = int(return_phi.getNumInputs())
    except Exception:
        input_count = 0
    for index in range(input_count):
        try:
            candidate = return_phi.getInput(index)
        except Exception:
            continue
        if not self._varnodes_same_storage(candidate, acc_output):
            continue
        try:
            predecessor = return_parent.getIn(index)
        except Exception:
            predecessor = None
        if predecessor is None:
            continue
        if self._block_debug_key(predecessor) != self._block_debug_key(acc_parent):
            continue
        return True
    return False

def _impl__return_info_candidate_phi_origin_keys(self, ret: Optional[ReturnInfo]) -> Set[Tuple[Any, ...]]:
    if ret is None:
        return set()
    keys = set(self._phi_circular_origin_stable_keys(getattr(ret, "value", None)))
    keys.update(
        self._candidate_phi_origin_keys_from_summary_source_key(
            getattr(ret, "summary_candidate_source_key", None)
        )
    )
    return keys

def _impl__return_info_return_phi_origin_keys(self, ret: Optional[ReturnInfo]) -> Set[Tuple[Any, ...]]:
    if ret is None:
        return set()
    keys = set(self._phi_circular_origin_stable_keys(getattr(ret, "value", None)))
    keys.update(
        self._return_phi_origin_keys_from_summary_source_key(
            getattr(ret, "summary_candidate_source_key", None)
        )
    )
    return keys

def _impl__return_phi_origin_keys_from_summary_source_key(self, value) -> Set[Tuple[Any, ...]]:
    keys: Set[Tuple[Any, ...]] = set()
    if not isinstance(value, tuple):
        return keys
    for item in value:
        if (
            isinstance(item, tuple)
            and len(item) == 2
            and item[0] == "return_phi_origin_keys"
        ):
            raw_keys = item[1]
            for raw_key in tuple(raw_keys or ()):
                if isinstance(raw_key, tuple):
                    keys.add(raw_key)
            continue
        if isinstance(item, tuple):
            keys.update(self._return_phi_origin_keys_from_summary_source_key(item))
    return keys

def _impl__return_conditions_cover_region(
    self,
    region_conditions: Sequence[Condition],
    returns: Sequence[ReturnInfo],
) -> bool:
    if any(
        self._condition_lists_equivalent(
            list(region_conditions or ()),
            list(getattr(ret, "conditions", ()) or ()),
        )
        or (
            self._conditions_imply(region_conditions, tuple(getattr(ret, "conditions", ()) or ()))
            and self._conditions_imply(tuple(getattr(ret, "conditions", ()) or ()), region_conditions)
        )
        for ret in returns or ()
    ):
        return True
    guard_exprs: List[Expression] = []
    for ret in returns or ():
        guard = Condition.combine_and(list(getattr(ret, "conditions", ()) or ()))
        if guard is None:
            return True
        guard_exprs.append(
            Expression.unary_op("BOOL_NEGATE", guard.expression)
            if guard.negated
            else guard.expression
        )
    if not guard_exprs:
        return False
    disjunction = guard_exprs[0]
    for expr in guard_exprs[1:]:
        disjunction = Expression.binary_op("BOOL_OR", disjunction, expr)
    return self._conditions_are_unsat(tuple(region_conditions or ()) + (Condition(disjunction, True),))

def _impl__return_info_summary_identity_key(self, ret: ReturnInfo) -> Tuple[Any, ...]:
    return (
        "return_info",
        self._return_site_key(ret),
        tuple(
            getattr(condition, "structural_key", lambda: ("condition", condition.to_string()))()
            for condition in tuple(getattr(ret, "conditions", ()) or ())
        ),
        expression_key_safe(getattr(ret, "value", None)),
    )

def _impl__try_apply_triangular_mod_optimized_outcomes(
    self,
    high_function,
    analysis: FunctionReturnAnalysis,
) -> bool:
    if len(getattr(analysis, "parameters", []) or []) != 1:
        self._debug_print("Outcome optimized triangular summary declined: expected one parameter")
        return False
    if getattr(analysis, "deferred_calls", None):
        self._debug_print("Outcome optimized triangular summary declined: deferred calls present")
        return False
    if len(getattr(analysis, "returns", []) or []) != 2:
        self._debug_print("Outcome optimized triangular summary declined: expected two returns")
        return False
    if self._high_function_has_forbidden_control_outcome_ops(high_function, allow_call=False):
        self._debug_print("Outcome optimized triangular summary declined: forbidden control/effect op present")
        return False
    param = self._parameter_expression(analysis, 0)
    if param is None:
        self._debug_print("Outcome optimized triangular summary declined: parameter expression unavailable")
        return False
    return_size = self._analysis_return_size_bytes(analysis)
    zero_ret = None
    one_ret = None
    for ret in analysis.returns:
        if self._constant_int_value(ret.value) == 0:
            zero_ret = ret
        elif (
            self._expression_is_same_parameter_ignoring_subpiece(ret.value, param)
            or self._constant_int_value(ret.value) == 1
        ):
            one_ret = ret
    if zero_ret is None or one_ret is None:
        self._debug_print("Outcome optimized triangular summary declined: zero/one return partition not recognized")
        return False
    nonpositive = self._signed_positive_condition(param).negate()
    eq_one = Condition(
        Expression.binary_op(
            "INT_EQUAL",
            param,
            Expression.constant(1, max(1, int(param.size or return_size or 4))),
        ),
        False,
    )
    if not (
        self._conditions_equivalent(zero_ret.conditions, [nonpositive])
        or (
            len(zero_ret.conditions or ()) == 1
            and (
                self._condition_is_signed_nonpositive_of_param(zero_ret.conditions[0], param)
                or self._condition_is_signed_less_than_one_of_param(zero_ret.conditions[0], param)
            )
        )
    ):
        self._debug_print("Outcome optimized triangular summary declined: zero return guard is not param nonpositive")
        return False
    if not (
        self._conditions_equivalent(one_ret.conditions, [eq_one])
        or any(
            self._condition_is_param_equal_const(condition, param, 1)
            for condition in (one_ret.conditions or ())
        )
    ):
        self._debug_print("Outcome optimized triangular summary declined: one return guard is not param eq one")
        return False

    analysis.return_outcomes = (
        ReturnOutcome(guard=tuple(zero_ret.conditions), value=zero_ret.value, provenance={"source": "optimized_triangular_mod_partition"}, return_info=zero_ret),
        ReturnOutcome(guard=tuple(one_ret.conditions), value=one_ret.value, provenance={"source": "optimized_triangular_mod_partition"}, return_info=one_ret),
    )
    analysis.divergence_outcomes = ()
    analysis.unknown_outcomes = (
        UnknownOutcome(
            guard=(self._return_partition_miss_guard([zero_ret, one_ret]),),
            reason="optimized_missing_region_proof_missing",
            evidence={
                "candidate_rule": "optimized_triangular_mod_missing_region",
                "forbidden_ops_absent": True,
                "nonreturning_region_candidate": self._high_function_has_nonreturning_region_candidate(high_function),
                "return_partition": "param_nonpositive_or_param_eq_one",
                "missing_proof": "object_level_nonreturning_region_or_positive_region_resolution",
            },
        ),
    )
    if "outcome_partition_unknown_optimized_triangular_mod" not in analysis.analysis_notes:
        analysis.analysis_notes.append("outcome_partition_unknown_optimized_triangular_mod")
    return True

def _impl__return_partition_miss_guard(self, returns: Sequence[ReturnInfo]) -> Condition:
    miss_terms = []
    for ret in returns or ():
        guard = Condition.combine_and(list(ret.conditions or ()))
        if guard is None:
            return Condition(Expression.constant(0, 1), False)
        miss_terms.append(
            guard.expression
            if guard.negated
            else Expression.unary_op("BOOL_NEGATE", guard.expression)
        )
    if not miss_terms:
        return Condition(Expression.constant(1, 1), False)
    expr = miss_terms[0]
    for term in miss_terms[1:]:
        expr = Expression.binary_op("BOOL_AND", expr, term)
    return Condition(expr, False)

def _impl__analysis_return_size_bytes(self, analysis: FunctionReturnAnalysis) -> int:
    for ret in getattr(analysis, "returns", []) or []:
        size = int(getattr(ret.value, "size", 0) or 0)
        if size > 0:
            return size
    surface = analysis.get_comparison_surface()
    bits = int(getattr(surface, "explicit_bit_width", 0) or 0)
    if bits > 0:
        return max(1, (bits + 7) // 8)
    return 4

def _impl__make_synthetic_outcome_return(
    self,
    analysis: FunctionReturnAnalysis,
    *,
    value: Expression,
    conditions: Sequence[Condition],
    branch_index: int,
    tag: str,
) -> ReturnInfo:
    return ReturnInfo(
        address=str(getattr(analysis, "entry_point", None) or "outcome-summary"),
        value=value,
        conditions=list(conditions),
        branch_index=branch_index,
        return_kind="outcome_summary",
        acceptance_status="accepted",
        summary_candidate_id=("outcome_partition", tag, getattr(analysis, "function_name", None)),
    )

def _impl__high_function_has_nonreturning_region_candidate(self, high_function) -> bool:
    if self._high_function_has_cfg_cycle(high_function):
        return True
    for block in self._iter_high_basic_blocks(high_function):
        out_size = int(getattr(block, "getOutSize", lambda: 0)() or 0)
        if out_size != 0:
            continue
        has_return = any(
            getattr(op, "getMnemonic", lambda: None)() == "RETURN"
            for op in self._iter_high_block_ops(block)
        )
        if not has_return:
            return True
    return False

def _impl__return_infos_have_conflicting_overlap(
    self,
    return_infos: List[ReturnInfo],
) -> bool:
    for left_index, left in enumerate(return_infos):
        for right in return_infos[left_index + 1:]:
            combined_conditions = ConditionSimplifier.simplify_conditions(
                list(left.conditions or []) + list(right.conditions or [])
            )
            if ConditionSimplifier.is_contradiction(combined_conditions):
                continue
            if _expressions_equivalent(left.value, right.value):
                continue
            if self.debug:
                cond_dump = [
                    ConditionSimplifier.get_simplified_condition_string(cond)
                    for cond in combined_conditions
                ]
                self._debug_print(
                    "Control-region recovery rejected due to overlapping regions: "
                    f"left={self._debug_expr_identity_summary(left.value)} "
                    f"right={self._debug_expr_identity_summary(right.value)} "
                    f"conditions={cond_dump}"
                )
            return True
    return False

def _impl__collect_linear_ops_to_return(
    self,
    block_path: List[Any],
    return_op,
) -> Optional[List[Any]]:
    linear_ops = []
    for block_info in block_path:
        for pcode_op in getattr(block_info, "pcode_ops", []) or []:
            linear_ops.append(pcode_op)
            if self._pcode_ops_match(pcode_op, return_op):
                break
        if linear_ops and self._pcode_ops_match(linear_ops[-1], return_op):
            break

    if not linear_ops or not self._pcode_ops_match(linear_ops[-1], return_op):
        return None
    return linear_ops

def _impl__tracked_return_value_key(self, tracked: _TrackedReturnValue) -> Tuple[Any, ...]:
    varnode_key = self._varnode_location_key(tracked.varnode)
    if varnode_key is None and tracked.varnode is not None:
        varnode_key = ("id", id(tracked.varnode))
    storage = tracked.storage
    storage_key = None
    if storage is not None:
        storage_key = (
            bool(getattr(storage, "is_register", False)),
            getattr(storage, "space_name", None),
            getattr(storage, "offset", None),
            getattr(storage, "size", None),
            getattr(storage, "size_bits", None),
            getattr(storage, "register_name", None),
            getattr(storage, "base_register_name", None),
            getattr(storage, "bit_offset_in_base", None),
        )
    producer_key = self._pcode_op_identity_key(tracked.producer_op)
    if producer_key is None and tracked.producer_op is not None:
        producer_key = ("id", id(tracked.producer_op))
    return (varnode_key, storage_key, producer_key)

def _impl__deduplicate_tracked_return_values(
    self,
    tracked_values: List[_TrackedReturnValue],
) -> List[_TrackedReturnValue]:
    deduped: List[_TrackedReturnValue] = []
    seen: Set[Tuple[Any, ...]] = set()
    for tracked in tracked_values:
        key = self._tracked_return_value_key(tracked)
        if key in seen:
            continue
        seen.add(key)
        deduped.append(tracked)
    return deduped

def _impl__make_tracked_return_value(
    self,
    varnode,
    tracer: Optional[PcodeTracer],
    *,
    storage: Optional[StorageInfo] = None,
    producer_op=None,
) -> _TrackedReturnValue:
    resolved_storage = storage
    if resolved_storage is None and tracer is not None and varnode is not None:
        try:
            resolved_storage = tracer._get_storage_info_from_varnode(varnode)
        except Exception:
            resolved_storage = None
    return _TrackedReturnValue(
        varnode=varnode,
        storage=resolved_storage,
        producer_op=producer_op,
    )

def _impl__make_tracked_return_storage_value(
    self,
    storage: Optional[StorageInfo],
    *,
    producer_op=None,
) -> _TrackedReturnValue:
    return _TrackedReturnValue(
        varnode=None,
        storage=storage,
        producer_op=producer_op,
    )

def _impl__make_tracked_return_value_from_affecting_op(
    self,
    pcode_op,
    target_storage: Optional[StorageInfo],
    tracer: Optional[PcodeTracer],
) -> Optional[_TrackedReturnValue]:
    if pcode_op is None:
        return None

    output = getattr(pcode_op, "getOutput", lambda: None)()
    if output is not None:
        return self._make_tracked_return_value(
            output,
            tracer,
            storage=target_storage,
            producer_op=pcode_op,
        )

    if self._is_pcode_call_op(pcode_op):
        return self._make_tracked_return_storage_value(
            target_storage,
            producer_op=pcode_op,
        )
    return None

def _impl__resolve_implicit_return_tracked_values(
    self,
    return_op,
    tracer: PcodeTracer,
    condition_tracker: ConditionTracker,
    current_function=None,
    block_path=None,
) -> List[_TrackedReturnValue]:
    search_blocks = None
    if block_path:
        search_blocks = list(block_path)
    else:
        return_parent = getattr(return_op, "getParent", lambda: None)()
        return_block = condition_tracker.get_block_by_hash(return_parent)
        if return_block is None:
            return []
        search_blocks = [return_block]

    target_storages = self._get_implicit_return_target_storages(current_function, tracer)
    if not target_storages:
        return []

    tracked_values: List[_TrackedReturnValue] = []
    for target_storage in target_storages:
        candidate: Optional[_TrackedReturnValue] = None
        for block_info in search_blocks:
            for pcode_op in getattr(block_info, "pcode_ops", []) or []:
                if self._pcode_ops_match(pcode_op, return_op):
                    break
                if not self._pcode_op_affects_tracked_storage(
                    pcode_op,
                    target_storage,
                    tracer,
                    current_function=current_function,
                ):
                    continue
                candidate = self._make_tracked_return_value_from_affecting_op(
                    pcode_op,
                    target_storage,
                    tracer,
                )
        if candidate is not None:
            tracked_values.append(candidate)

    tracked_values = self._deduplicate_tracked_return_values(tracked_values)
    if tracked_values and self.debug:
        for tracked in tracked_values:
            if tracked.producer_op is not None:
                self._debug_print(
                    "Implicit return source matched to terminal producer "
                    f"{self._pcode_op_debug_name(tracked.producer_op)}"
                )
            elif tracked.varnode is not None:
                self._debug_print(
                    f"Implicit return source matched to block-local output {tracked.varnode}"
                )
    return tracked_values

def _impl__tracked_return_value_is_affected_by_op(
    self,
    tracked: _TrackedReturnValue,
    pcode_op,
    *,
    tracer: Optional[PcodeTracer],
    current_function=None,
) -> bool:
    output = getattr(pcode_op, "getOutput", lambda: None)()
    output_storage = None
    if tracer is not None and output is not None:
        try:
            output_storage = tracer._get_storage_info_from_varnode(output)
        except Exception:
            output_storage = None

    if tracked.varnode is not None and output is not None and self._varnodes_may_alias(tracked.varnode, output):
        return True

    tracked_storage = tracked.storage
    if tracked_storage is None and tracked.varnode is not None and tracer is not None:
        try:
            tracked_storage = tracer._get_storage_info_from_varnode(tracked.varnode)
        except Exception:
            tracked_storage = None

    if tracked_storage is not None and output_storage is not None:
        if self._storages_overlap_for_return_recovery(tracked_storage, output_storage):
            return True

    if output is None and self._is_pcode_call_op(pcode_op) and tracked_storage is not None and tracer is not None:
        for return_storage in self._get_implicit_return_target_storages(current_function, tracer):
            if self._storages_overlap_for_return_recovery(tracked_storage, return_storage):
                return True
    return False

def _impl__resolve_local_return_expression(
    self,
    pcode_op,
    tracer,
    local_values: Dict[Tuple[str, int, int], Expression],
    local_storages: Dict[Tuple[str, int, int], Any],
    local_memory: Dict[Tuple[StructuralKey, int], Expression],
    current_function=None,
) -> Expression:
    if pcode_op.getNumInputs() >= 2:
        return self._evaluate_local_varnode_expression(
            pcode_op.getInput(1),
            tracer,
            local_values,
            local_storages,
            local_memory,
        )

    for return_varnode in self._get_function_return_varnodes(current_function):
        expr = self._evaluate_local_varnode_expression(
            return_varnode,
            tracer,
            local_values,
            local_storages,
            local_memory,
        )
        if expr is not None and expr.expr_type != ExpressionType.UNKNOWN:
            self._debug_print(
                f"Local target RETURN without explicit value; using return storage {return_varnode}"
            )
            return expr

    for return_storage in self._get_implicit_return_target_storages(current_function, tracer):
        expr = self._lookup_local_expression_for_storage(
            return_storage,
            local_values,
            local_storages,
        )
        if expr is not None and expr.expr_type != ExpressionType.UNKNOWN:
            self._debug_print(
                "Local target RETURN without explicit value; using implicit return storage "
                f"{getattr(return_storage, 'base_register_name', None) or getattr(return_storage, 'register_name', None)}"
            )
            return expr

    self._debug_print("Local target RETURN without explicit value; defaulting to 0")
    return Expression.constant(0, 1)

def _impl__get_function_return_varnodes(self, function) -> List[Any]:
    if function is None:
        return []
    try:
        return_var = function.getReturn()
        if return_var is None:
            return []
        storage = return_var.getVariableStorage()
        if storage is None:
            return []
        get_varnodes = getattr(storage, "getVarnodes", None)
        if callable(get_varnodes):
            raw_varnodes = cast(Iterable[Any], get_varnodes())
            return [vn for vn in raw_varnodes if vn is not None]
    except Exception:
        return []
    return []

def _impl__get_current_prototype_return_varnodes(self) -> List[Any]:
    prototype = self._current_function_prototype
    if prototype is None:
        return []
    try:
        storage = prototype.getReturnStorage()
        if storage is None:
            return []
        get_varnodes = getattr(storage, "getVarnodes", None)
        if callable(get_varnodes):
            raw_varnodes = cast(Iterable[Any], get_varnodes())
            return [vn for vn in raw_varnodes if vn is not None]
    except Exception:
        return []
    return []

def _impl__infer_abi_return_storages(self) -> List[StorageInfo]:
    """関数シグネチャが void に潰れていても使える保守的な返り値レジスタ候補。"""
    try:
        lang = self.program.getLanguage() if self.program is not None else None
        lang_id = str(lang.getLanguageID()) if lang is not None else ""
        processor = str(lang.getProcessor()) if lang is not None else ""
        pointer_size = int(self.program.getDefaultPointerSize()) if self.program is not None else 8
    except Exception:
        lang_id = ""
        processor = ""
        pointer_size = 8

    arch_tag = f"{lang_id} {processor}".upper()
    base_bits = max(pointer_size * 8, 32)

    def _reg(base_name: str) -> StorageInfo:
        return StorageInfo(
            is_register=True,
            space_name="register",
            size=max(base_bits // 8, 4),
            size_bits=base_bits,
            register_name=base_name,
            base_register_name=base_name,
            base_register_size=max(base_bits // 8, 4),
            base_register_size_bits=base_bits,
            bit_offset_in_base=0,
        )

    if "MIPS" in arch_tag:
        return [_reg("v0")]
    if "AARCH64" in arch_tag or "ARM:LE:64" in arch_tag or "ARM:BE:64" in arch_tag:
        return [_reg("x0")]
    if "ARM" in arch_tag:
        return [_reg("r0")]
    if "X86" in arch_tag and "64" in arch_tag:
        return [_reg("rax")]
    if "X86" in arch_tag or "IA-32" in arch_tag:
        return [_reg("eax")]
    return []

def _impl__get_return_type_info(self, high_function):
    """戻り値の型オブジェクトと表示名を取得"""
    try:
        func_proto = high_function.getFunctionPrototype()
        if func_proto:
            ret_type = func_proto.getReturnType()
            if ret_type:
                return ret_type, self._get_return_type(high_function) or str(ret_type)
    except Exception as e:
        self._debug_print(f"Failed to get return type: {e}")
    return None, None

def _impl__get_return_type(self, high_function) -> Optional[str]:
    """後方互換: 戻り値の表示名だけを返す。"""
    try:
        func_proto = high_function.getFunctionPrototype()
        if func_proto:
            ret_type = func_proto.getReturnType()
            if ret_type:
                return str(ret_type)
    except Exception as e:
        self._debug_print(f"Failed to get return type: {e}")
    return None

def _impl__analyze_return_op(
    self,
    return_op,
    tracer: PcodeTracer,
    condition_tracker: ConditionTracker,
    return_index: int,
    current_function,
    active_functions: Set[Tuple[Any, ...]],
    return_type_obj=None,
) -> List[ReturnInfo]:
    """単一のRETURNを解析"""
    site_metadata = self._describe_pcode_site(return_op, "unknown")
    site_metadata["_return_op_object"] = return_op
    address = cast(str, site_metadata.get("address") or "unknown")

    num_inputs = return_op.getNumInputs()
    self._debug_print(f"RETURN at {address}, inputs: {num_inputs}")

    raw_path_entries = None
    path_coverage_status = "inconclusive"
    get_path_coverage = getattr(condition_tracker, "get_path_coverage_to_return", None)
    if callable(get_path_coverage):
        coverage = get_path_coverage(return_op)
        candidate_status = getattr(coverage, "status", None)
        candidate_paths = getattr(coverage, "block_paths", None)
        if candidate_status in {"complete", "inconclusive", "incomplete"} and isinstance(
            candidate_paths, (tuple, list)
        ):
            path_coverage_status = str(candidate_status)
            raw_path_entries = candidate_paths
    if raw_path_entries is None:
        get_block_paths = getattr(condition_tracker, "get_all_valid_block_paths_to_return", None)
        if callable(get_block_paths):
            raw_path_entries = get_block_paths(return_op)

    path_entries = self._coerce_block_path_entries(raw_path_entries)
    blocked_path_conditions: List[List[Condition]] = []
    if path_entries:
        path_entries, blocked_path_conditions = self._filter_noreturn_return_path_entries(
            path_entries,
            tracer,
            return_op,
        )
        if not path_entries:
            if self.debug:
                self._debug_print(
                    "All RETURN path variants were pruned as noreturn/unreachable; skipping RETURN"
                )
            return []
        all_valid_path_conditions = [list(conditions) for _blocks, conditions in path_entries]
        path_conditions = list(all_valid_path_conditions[0]) if all_valid_path_conditions else []
    else:
        # Fall back to the pre-existing condition-only API if block paths are unavailable.
        path_conditions = condition_tracker.get_path_conditions_to_return(return_op)
        all_valid_path_conditions = condition_tracker.get_all_valid_paths_to_return(return_op)
        if not isinstance(path_conditions, (tuple, list)):
            path_conditions = []
        if not isinstance(all_valid_path_conditions, (tuple, list)):
            all_valid_path_conditions = [list(path_conditions or ())]

    def condition_group_key(conditions):
        return tuple(sorted((condition.structural_key() for condition in conditions or ()), key=repr))

    path_block_keys = tuple(
        tuple(
            ("path_block", int(getattr(block_info, "index", -1)), str(getattr(block_info, "start", "")))
            for block_info in blocks
        )
        for blocks, _conditions in (path_entries or ())
    )
    terminal_ref = site_metadata.get("pcode_op_ref")
    site_metadata["return_path_evidence"] = ReturnPathEvidence(
        terminal_op_ref=terminal_ref if isinstance(terminal_ref, PcodeOpRef) else None,
        coverage_status=(
            "complete"
            if path_coverage_status == "complete" and not blocked_path_conditions
            else "inconclusive"
        ),
        path_block_keys=path_block_keys,
        path_guard_keys=tuple(sorted(
            {condition_group_key(conditions) for conditions in (all_valid_path_conditions or ())},
            key=repr,
        )),
        pruning_proof_keys=(),
    )

    if self.debug and path_conditions:
        cond_strs = [ConditionSimplifier.get_simplified_condition_string(c) for c in path_conditions]
        self._debug_print(f"Path conditions to RETURN: {cond_strs}")
    if self.debug and len(all_valid_path_conditions) > 1:
        self._debug_print(
            f"RETURN has {len(all_valid_path_conditions)} valid path variants",
        )

    previous_blocked = list(self._current_blocked_return_path_conditions)
    self._current_blocked_return_path_conditions = [
        list(conditions) for conditions in blocked_path_conditions
    ]
    try:
        if return_type_obj is not None and self._is_void_type(return_type_obj):
            fallback_condition_sets = list(all_valid_path_conditions or [])
            if not fallback_condition_sets:
                fallback_condition_sets = [list(path_conditions)]
            fallback_returns: List[ReturnInfo] = []
            for path_idx, candidate_conditions in enumerate(fallback_condition_sets):
                simplified_conds = ConditionSimplifier.simplify_conditions_object_centric(
                    list(candidate_conditions)
                )
                fallback_returns.append(
                    self._make_return_info(
                        address=address,
                        value=Expression.unknown("void"),
                        conditions=simplified_conds,
                        branch_index=return_index * 1000 + path_idx,
                        site_metadata=site_metadata,
                    )
                )
            return self._merge_equivalent_return_infos(
                self._prune_less_precise_return_infos(fallback_returns)
            )
        if num_inputs >= 2:
            return_varnode = return_op.getInput(1)
            return self._analyze_return_value(
                return_varnode,
                address,
                tracer,
                condition_tracker,
                path_conditions,
                return_index,
                all_path_conditions=all_valid_path_conditions,
                active_functions=active_functions,
                current_function=current_function,
                site_metadata=site_metadata,
            )
        else:
            implicit_results = self._analyze_implicit_return_value(
                return_op,
                address,
                tracer,
                condition_tracker,
                path_conditions,
                return_index,
                all_path_conditions=all_valid_path_conditions,
                path_entries=path_entries,
                active_functions=active_functions,
                current_function=current_function,
                site_metadata=site_metadata,
                return_type_obj=return_type_obj,
            )
            if implicit_results is not None:
                return implicit_results
            return self._merge_equivalent_return_infos(
                self._prune_less_precise_return_infos(
                    [
                        self._make_return_info(
                            address=address,
                            value=Expression.unknown("void"),
                            conditions=ConditionSimplifier.simplify_conditions_object_centric(
                                list(candidate_conditions)
                            ),
                            branch_index=return_index * 1000 + path_idx,
                            site_metadata=site_metadata,
                        )
                        for path_idx, candidate_conditions in enumerate(
                            list(all_valid_path_conditions or []) or [list(path_conditions)]
                        )
                    ]
                )
            )
    finally:
        self._current_blocked_return_path_conditions = previous_blocked

def _impl__function_has_no_return(self, function) -> bool:
    if function is None:
        return False
    for attr_name in ("hasNoReturn", "isNoReturn", "getNoReturn"):
        attr = getattr(function, attr_name, None)
        if callable(attr):
            try:
                if bool(attr()):
                    return True
            except Exception:
                continue
    return False

def _impl__analyze_implicit_return_value(
    self,
    return_op,
    address: str,
    tracer: PcodeTracer,
    condition_tracker: ConditionTracker,
    path_conditions: List[Condition],
    return_index: int,
    all_path_conditions: Optional[List[List[Condition]]] = None,
    path_entries=None,
    active_functions: Optional[Set[Tuple[Any, ...]]] = None,
    current_function=None,
    site_metadata: Optional[Dict[str, Optional[object]]] = None,
    return_type_obj=None,
) -> Optional[List[ReturnInfo]]:
    """RETURN オペランドが欠落している場合に、返り値レジスタ由来の値を復元する。"""
    if return_type_obj is not None and self._is_void_type(return_type_obj):
        return None
    path_recovered = self._recover_implicit_return_from_block_paths(
        return_op,
        address,
        tracer,
        condition_tracker,
        return_index,
        path_entries,
        active_functions=active_functions,
        current_function=current_function,
        site_metadata=site_metadata,
    )
    if path_recovered is not None:
        return path_recovered

    tracked_sources = self._resolve_implicit_return_tracked_values(
        return_op,
        tracer,
        condition_tracker,
        current_function,
    )
    if tracked_sources:
        self._debug_print(
            "RETURN has no explicit value; retrying via object-centric return provenance"
        )
        recovered_results = self._recover_return_infos_from_tracked_sources(
            tracked_sources,
            address,
            tracer,
            condition_tracker,
            path_conditions,
            return_index,
            all_path_conditions=all_path_conditions,
            active_functions=active_functions,
            current_function=current_function,
            site_metadata=site_metadata,
        )
        if recovered_results is not None:
            return recovered_results
    elif self.debug:
        self._debug_print(
            "Implicit return storage recovery did not find a terminal producer"
        )

    if self.debug:
        self._debug_print(
            "Implicit return object-centric recovery did not find a materializable producer"
        )
    return None

def _impl__recover_return_infos_from_tracked_sources(
    self,
    tracked_sources: List[_TrackedReturnValue],
    address: str,
    tracer: PcodeTracer,
    condition_tracker: ConditionTracker,
    path_conditions: List[Condition],
    return_index_base: int,
    all_path_conditions: Optional[List[List[Condition]]] = None,
    active_functions: Optional[Set[Tuple[Any, ...]]] = None,
    current_function=None,
    site_metadata: Optional[Dict[str, Optional[object]]] = None,
) -> Optional[List[ReturnInfo]]:
    recovered_results: List[ReturnInfo] = []
    for tracked_index, tracked in enumerate(tracked_sources):
        materialized = self._materialize_tracked_return_source(
            tracked,
            address,
            tracer,
            condition_tracker,
            path_conditions,
            return_index_base + tracked_index,
            all_path_conditions=all_path_conditions,
            active_functions=active_functions,
            current_function=current_function,
            site_metadata=site_metadata,
        )
        if materialized:
            recovered_results.extend(materialized)

    if not recovered_results:
        return None
    return self._merge_equivalent_return_infos(recovered_results)

def _impl__materialize_tracked_return_source(
    self,
    tracked: _TrackedReturnValue,
    address: str,
    tracer: PcodeTracer,
    condition_tracker: ConditionTracker,
    path_conditions: List[Condition],
    return_index: int,
    all_path_conditions: Optional[List[List[Condition]]] = None,
    active_functions: Optional[Set[Tuple[Any, ...]]] = None,
    current_function=None,
    site_metadata: Optional[Dict[str, Optional[object]]] = None,
) -> Optional[List[ReturnInfo]]:
    producer_op = tracked.producer_op
    if producer_op is not None and self._is_pcode_call_op(producer_op):
        return self._recover_implicit_return_from_terminal_call(
            producer_op,
            address,
            tracer,
            condition_tracker,
            path_conditions,
            return_index,
            all_path_conditions=all_path_conditions,
            active_functions=active_functions,
            current_function=current_function,
            site_metadata=site_metadata,
        )

    if tracked.varnode is None:
        return None

    value_site_metadata = self._site_metadata_with_return_value_pcode_op_refs(
        site_metadata,
        return_varnode=tracked.varnode,
        producer_op=producer_op,
    )
    return self._analyze_return_value(
        tracked.varnode,
        address,
        tracer,
        condition_tracker,
        path_conditions,
        return_index,
        all_path_conditions=all_path_conditions,
        active_functions=active_functions,
        current_function=current_function,
        site_metadata=value_site_metadata,
    )

def _impl__storages_overlap_for_return_recovery(self, left, right) -> bool:
    if left is None or right is None:
        return False
    try:
        if getattr(left, "is_register", False) and getattr(right, "is_register", False):
            return (
                left.shares_base_register_with(right)
                and left.bit_range_overlaps_with(right)
            )
    except Exception:
        return False

    return (
        getattr(left, "space_name", None) == getattr(right, "space_name", None)
        and getattr(left, "offset", None) == getattr(right, "offset", None)
        and getattr(left, "size", None) == getattr(right, "size", None)
    )

def _impl__analyze_return_value(
    self,
    return_varnode,
    address: str,
    tracer: PcodeTracer,
    condition_tracker: ConditionTracker,
    path_conditions: List[Condition],
    return_index: int,
    all_path_conditions: Optional[List[List[Condition]]] = None,
    active_functions: Optional[Set[Tuple[Any, ...]]] = None,
    current_function=None,
    site_metadata: Optional[Dict[str, Optional[object]]] = None,
) -> List[ReturnInfo]:
    """Return値を解析"""
    from ...transform import ExpressionExpander

    value_site_metadata = self._site_metadata_with_return_value_pcode_op_refs(
        site_metadata,
        return_varnode=return_varnode,
        tracer=tracer,
    )

    tracer.clear_cache()

    # MULTIEQUALが含まれるかチェック
    has_multiequal = self._contains_multiequal(return_varnode)
    if has_multiequal:
        self._debug_print("Return value contains MULTIEQUAL - using PHI-based expansion")
        expander = ExpressionExpander(
            tracer,
            condition_tracker,
            debug=self.debug,
            call_resolver=self._make_call_resolver(active_functions or set(), current_function),
            effect_summary=self._current_effect_summary,
            parameters=self._current_parameters,
            resolve_callee_parameters=self._get_freshest_callee_parameters,
            read_memory_value=self._read_memory_value,
            image_base=self.program.getImageBase().getOffset(),
            record_deferred_call=self._make_deferred_call_recorder(current_function),
        )
        expanded_values = expander.expand_from_varnode(return_varnode, [])
    else:
        self._debug_print("Return value has no MULTIEQUAL - using path conditions")
        expander = ExpressionExpander(
            tracer,
            condition_tracker,
            debug=self.debug,
            call_resolver=self._make_call_resolver(active_functions or set(), current_function),
            effect_summary=self._current_effect_summary,
            parameters=self._current_parameters,
            resolve_callee_parameters=self._get_freshest_callee_parameters,
            read_memory_value=self._read_memory_value,
            image_base=self.program.getImageBase().getOffset(),
            record_deferred_call=self._make_deferred_call_recorder(current_function),
        )
        path_condition_sets = all_path_conditions or []
        if not path_condition_sets:
            path_condition_sets = [path_conditions] if path_conditions else [[]]

        expanded_values = []
        for path_idx, conds in enumerate(path_condition_sets):
            if self.debug and len(path_condition_sets) > 1:
                cond_strs = [
                    ConditionSimplifier.get_simplified_condition_string(c)
                    for c in conds
                ]
                self._debug_print(
                    f"Expanding non-PHI return with path[{path_idx}]: {cond_strs}"
                )
            expanded_values.extend(
                expander.expand_from_varnode(return_varnode, conds)
            )

    self._debug_print(f"Expanded to {len(expanded_values)} candidate(s)")

    phi_expansion_candidate_origin_keys: Tuple[Tuple[Any, ...], ...] = ()
    if has_multiequal:
        phi_expansion_candidate_origin_keys = self._phi_origin_keys_from_return_varnode_trace(
            tracer,
            return_varnode,
        )

    results = self._build_return_infos_from_expansions(
        address,
        expanded_values,
        return_index,
        site_metadata=value_site_metadata,
        return_kind="phi_expansion" if has_multiequal else None,
        candidate_phi_origin_keys=phi_expansion_candidate_origin_keys,
    )
    if has_multiequal and results:
        results = self._append_smt_lowerable_phi_return_fallback_infos(
            results,
            tracer=tracer,
            return_varnode=return_varnode,
            path_condition_sets=all_path_conditions or ([path_conditions] if path_conditions else [[]]),
            address=address,
            return_index=return_index,
            site_metadata=value_site_metadata,
        )

    if not results:
        self._debug_print("WARNING: No valid expansions, falling back to simple trace")
        value = tracer.trace_varnode(return_varnode, use_cache=False)
        simplified_conds = ConditionSimplifier.simplify_conditions_object_centric(
            path_conditions
        )
        resolved_value = self._concretize_readonly_loads(value, simplified_conds, self._current_parameters)
        return [self._make_return_info(
            address=address,
            value=resolved_value,
            conditions=simplified_conds,
            branch_index=return_index,
            site_metadata=value_site_metadata,
        )]

    return results

def _impl__append_smt_lowerable_phi_return_fallback_infos(
    self,
    return_infos: List[ReturnInfo],
    *,
    tracer,
    return_varnode,
    path_condition_sets: Sequence[Sequence[Condition]],
    address: str,
    return_index: int,
    site_metadata: Optional[Dict[str, Optional[object]]] = None,
):
    try:
        fallback_value = tracer.trace_varnode(return_varnode, use_cache=False)
    except Exception:
        return return_infos
    if not isinstance(fallback_value, Expression):
        return return_infos
    if not self._expression_contains_phi(fallback_value):
        return return_infos
    rewritten_value, _changed = self._normalize_callother_userop_expression(fallback_value)
    fallback_value = rewritten_value
    if fallback_value is None or expression_contains_unsupported_smt_ops(fallback_value):
        return return_infos
    candidate_phi_origin_keys = tuple(
        sorted(
            self._phi_circular_origin_stable_keys(fallback_value)
            | set(self._phi_origin_keys_from_varnode_defs(return_varnode)),
            key=repr,
        )
    )
    fallback_conditions = list(path_condition_sets or ())
    if not fallback_conditions:
        fallback_conditions = [[]]
    additions = []
    union_condition = self._path_condition_sets_union_condition(fallback_conditions)
    if union_condition is not None:
        union_conditions = ConditionSimplifier.simplify_conditions_object_centric([union_condition])
        if not ConditionSimplifier.object_centric_is_contradiction(union_conditions):
            union_value = self._normalize_expanded_return_value(
                fallback_value,
                union_conditions,
            )
            if union_value is None:
                union_value = fallback_value
            if (
                union_value is not None
                and not expression_contains_unsupported_smt_ops(union_value)
                and not self._expression_contains_phi(union_value)
            ):
                info = self._make_return_info(
                    address=address,
                    value=union_value,
                    conditions=union_conditions,
                    branch_index=return_index * 100 + 80,
                    site_metadata=site_metadata,
                )
                info = replace(
                    info,
                    return_kind="phi_union_reachability_fallback",
                    summary_candidate_source_key=(
                        "phi_union_reachability_fallback",
                        ("candidate_discovery_only_phi_origin_keys", candidate_phi_origin_keys),
                    ) if candidate_phi_origin_keys else getattr(info, "summary_candidate_source_key", None),
                )
                additions.append(info)
    for index, conditions in enumerate(fallback_conditions):
        simplified = ConditionSimplifier.simplify_conditions_object_centric(
            list(conditions or [])
        )
        if ConditionSimplifier.object_centric_is_contradiction(simplified):
            continue
        normalized_value = self._normalize_expanded_return_value(
            fallback_value,
            simplified,
        )
        if normalized_value is None:
            normalized_value = fallback_value

        if self._expression_contains_phi(normalized_value):
            finite_candidates = self._phi_free_finite_fallback_candidates(
                fallback_value,
                simplified,
            )
        else:
            finite_candidates = [(simplified, normalized_value)]

        for finite_index, (finite_conditions, finite_value) in enumerate(finite_candidates):
            if self._expression_contains_phi(finite_value):
                continue
            if any(
                self._expression_contains_phi(getattr(condition, "expression", None))
                or self._expression_contains_unknown_or_call(getattr(condition, "expression", None))
                for condition in finite_conditions or ()
            ):
                continue
            branch_index = return_index * 100 + 90 + index
            if len(finite_candidates) > 1:
                branch_index = branch_index * 100 + finite_index
            info = self._make_return_info(
                address=address,
                value=finite_value,
                conditions=finite_conditions,
                branch_index=branch_index,
                site_metadata=site_metadata,
            )
            info = replace(
                info,
                return_kind="phi_reachability_fallback",
                summary_candidate_source_key=(
                    "phi_reachability_fallback",
                    ("candidate_phi_origin_keys", candidate_phi_origin_keys),
                    ("return_phi_origin_keys", candidate_phi_origin_keys),
                ) if candidate_phi_origin_keys else getattr(info, "summary_candidate_source_key", None),
            )
            additions.append(info)
    if not additions:
        return return_infos
    if self.debug:
        self._debug_print(
            "Preserved SMT-lowerable PHI return fallback for broad return-path coverage"
        )
    return self._merge_equivalent_return_infos(
        self._prune_less_precise_return_infos(list(return_infos or []) + additions)
    )

def _impl__phi_origin_keys_from_return_varnode_trace(
    self,
    tracer,
    return_varnode,
) -> Tuple[Tuple[Any, ...], ...]:
    keys: Set[Tuple[Any, ...]] = set(self._phi_origin_keys_from_varnode_defs(return_varnode))
    try:
        fallback_value = tracer.trace_varnode(return_varnode, use_cache=False)
    except Exception:
        fallback_value = None
    if isinstance(fallback_value, Expression):
        keys.update(self._phi_circular_origin_stable_keys(fallback_value))
    return tuple(sorted(keys, key=repr))

def _impl__build_return_infos_from_expansions(
    self,
    address: str,
    expanded_values,
    return_index: int,
    site_metadata: Optional[Dict[str, Optional[object]]] = None,
    return_kind: Optional[str] = None,
    candidate_phi_origin_keys: Sequence[Tuple[Any, ...]] = (),
) -> List[ReturnInfo]:
    results = []
    for i, ev in enumerate(expanded_values):
        if not ev.is_valid():
            self._debug_print(f"Skipping contradictory expansion {i}")
            continue

        simplified_conds = ConditionSimplifier.simplify_conditions_object_centric(
            ev.conditions
        )
        if self.debug:
            cond_strs = [
                ConditionSimplifier.get_simplified_condition_string(c)
                for c in simplified_conds
            ]
            self._debug_print(
                f"Expansion {i}: raw={self._debug_expr_identity_summary(ev.value)}"
            )
            self._debug_print(f"  raw_conditions={cond_strs}")
        split_cases = self._split_effect_sensitive_return_case(
            ev.value,
            simplified_conds,
        )
        object_centric_cases: List[Tuple[Expression, List[Condition]]] = []
        for split_value, split_conditions in split_cases:
            object_centric_cases.extend(
                self._split_object_centric_return_case(
                    split_value,
                    split_conditions,
                )
            )
        split_cases = object_centric_cases or split_cases
        branch_base = return_index * 100 + i
        for split_index, (split_value, split_conditions) in enumerate(split_cases):
            if self.debug:
                split_cond_strs = [
                    ConditionSimplifier.get_simplified_condition_string(c)
                    for c in split_conditions
                ]
                self._debug_print(
                    f"Expansion {i}.{split_index}: split={self._debug_expr_identity_summary(split_value)}"
                )
                self._debug_print(f"  split_conditions={split_cond_strs}")
            preserve_split_value = (
                not _expressions_equivalent(split_value, ev.value)
                and not expression_contains_post_state_reads(split_value)
                and not _expression_contains_observed_loads(split_value)
            )
            normalized_value = (
                split_value
                if preserve_split_value
                else self._normalize_expanded_return_value(
                    split_value,
                    split_conditions,
                )
            )
            if self.debug and normalized_value is not split_value:
                self._debug_print(
                    "  normalized="
                    f"{self._debug_expr_identity_summary(normalized_value)}"
                )
            resolved_value = self._concretize_readonly_loads(
                normalized_value,
                split_conditions,
                self._current_parameters,
            )
            if self.debug and resolved_value is not normalized_value:
                self._debug_print(
                    "  concretized="
                    f"{self._debug_expr_identity_summary(resolved_value)}"
                )

            if self.debug:
                cond_strs = [
                    ConditionSimplifier.get_simplified_condition_string(c)
                    for c in split_conditions
                ]
                self._debug_print(
                    f"Expansion {i}.{split_index}: value={self._debug_expr_summary(resolved_value)}"
                )
                self._debug_print(f"  conditions={cond_strs}")

            if self._matches_blocked_return_path_conditions(split_conditions):
                if self.debug:
                    self._debug_print(
                        f"Skipping expansion {i}.{split_index} because its conditions match a blocked noreturn path"
                    )
                continue

            info = self._make_return_info(
                address=address,
                value=resolved_value,
                conditions=split_conditions,
                branch_index=(
                    branch_base
                    if len(split_cases) == 1
                    else branch_base * 10 + split_index
                ),
                site_metadata=site_metadata,
            )
            split_candidate_phi_origin_keys = tuple(
                sorted(
                    self._phi_circular_origin_stable_keys(split_value)
                    or self._phi_circular_origin_stable_keys(ev.value)
                    or set(candidate_phi_origin_keys or ()),
                    key=repr,
                )
            )
            if return_kind:
                source_key_items: List[Tuple[Any, ...]] = []
                if split_candidate_phi_origin_keys:
                    source_key_items.append(("candidate_phi_origin_keys", split_candidate_phi_origin_keys))
                    source_key_items.append(("return_phi_origin_keys", split_candidate_phi_origin_keys))
                info = replace(
                    info,
                    return_kind=return_kind,
                    summary_candidate_source_key=(
                        (return_kind, *source_key_items)
                        if source_key_items
                        else getattr(info, "summary_candidate_source_key", None)
                    ),
                )
            results.append(info)
    pruned = self._prune_less_precise_return_infos(results)
    return self._merge_equivalent_return_infos(pruned)

def _impl__split_object_centric_return_case(
    self,
    value: Expression,
    conditions: List[Condition],
) -> List[Tuple[Expression, List[Condition]]]:
    expanded = self._expand_object_centric_expression_cases(
        value,
        conditions,
    )
    if not expanded:
        return [(value, conditions)]

    normalized: List[Tuple[Expression, List[Condition]]] = []
    for case_value, case_conditions in expanded:
        simplified_conditions = ConditionSimplifier.simplify_conditions_object_centric(
            list(case_conditions or [])
        )
        if ConditionSimplifier.object_centric_is_contradiction(simplified_conditions):
            continue
        folded_value = self._fold_constant_expression(case_value, fallback_expr=case_value)
        normalized.append((folded_value, simplified_conditions))

    deduplicated = self._deduplicate_expression_cases(normalized)
    if (
        len(deduplicated) == 1
        and _expressions_equivalent(deduplicated[0][0], value)
        and self._condition_lists_equivalent(deduplicated[0][1], conditions)
    ):
        return [(value, conditions)]

    if self.debug and len(deduplicated) > 1:
        self._debug_print(
            "Split return into object-centric value cases: "
            f"{self._debug_expr_identity_summary(value)}"
        )
        for case_index, (case_value, case_conditions) in enumerate(deduplicated):
            cond_dump = [
                ConditionSimplifier.get_simplified_condition_string(cond)
                for cond in case_conditions
            ]
            self._debug_print(
                f"  value-case[{case_index}]: {self._debug_expr_identity_summary(case_value)}"
            )
            self._debug_print(f"    conditions={cond_dump}")
    return deduplicated or [(value, conditions)]

def _impl__prune_less_precise_return_infos(
    self,
    return_infos: List[ReturnInfo],
) -> List[ReturnInfo]:
    if len(return_infos) < 2:
        return return_infos

    grouped: Dict[Tuple[str, str], List[ReturnInfo]] = {}
    for info in return_infos:
        key = (
            self._return_site_key(info),
            self._pruning_conditions_signature(info.conditions),
        )
        grouped.setdefault(key, []).append(info)

    pruned: List[ReturnInfo] = []
    for group in grouped.values():
        precise_group = [
            info
            for info in group
            if not self._expression_contains_unresolved_value(info.value)
        ]
        unresolved_group = [
            info
            for info in group
            if self._expression_contains_unresolved_value(info.value)
        ]
        if not precise_group or not unresolved_group:
            pruned.extend(group)
            continue

        canonical_precise = precise_group[0]
        precise_values_are_unanimous = all(
            _expressions_equivalent(canonical_precise.value, info.value)
            for info in precise_group[1:]
        )
        if not precise_values_are_unanimous:
            if self.debug:
                self._debug_print(
                    "Preserved unresolved return cases because precise cases "
                    "under the same condition region disagree"
                )
            pruned.extend(group)
            continue
        if any(
            self._return_value_is_multiplicative_phi_recurrence_candidate(info.value)
            for info in unresolved_group
        ):
            if self.debug:
                self._debug_print(
                    "Preserved unresolved multiplicative PHI return cases for "
                    "structural recurrence summary validation"
                )
            pruned.extend(group)
            continue

        dropped = len(unresolved_group)
        if dropped > 0 and self.debug:
            self._debug_print(
                "Dropped less precise unresolved return cases under an "
                "already-resolved condition region"
            )
        pruned.extend(precise_group)

    return pruned

def _impl__return_value_is_multiplicative_phi_recurrence_candidate(self, value: Optional[Expression]) -> bool:
    if getattr(value, "expr_type", None) != ExpressionType.BINARY_OP:
        return False
    if getattr(value, "operator", None) not in {"INT_MULT", "INT_LEFT"}:
        return False
    operands = tuple(getattr(value, "operands", ()) or ())
    if len(operands) != 2:
        return False
    has_phi_unknown = any(self._expression_contains_phi_circular_marker(operand) for operand in operands)
    has_constant = any(getattr(operand, "expr_type", None) == ExpressionType.CONSTANT for operand in operands)
    return bool(has_phi_unknown and has_constant)

def _impl__exclusivize_return_regions(
    self,
    return_infos: List[ReturnInfo],
) -> List[ReturnInfo]:
    preserved: List[ReturnInfo] = []
    ordered_return_infos = sorted(
        enumerate(return_infos),
        key=cmp_to_key(self._compare_return_region_order),
    )
    for index, (original_index, info) in enumerate(ordered_return_infos):
        current_regions: List[List[Condition]] = [
            self._return_info_effective_region_conditions(info)
        ]
        if ConditionSimplifier.object_centric_is_contradiction(current_regions[0]):
            continue

        for other_index, (_other_original_index, other) in enumerate(ordered_return_infos):
            if other_index >= index:
                break
            if _expressions_equivalent(other.value, info.value):
                continue

            other_conditions = self._return_info_effective_region_conditions(other)
            next_regions: List[List[Condition]] = []
            for region in current_regions:
                if ConditionSimplifier.object_centric_is_contradiction(region):
                    continue
                if not ConditionSimplifier.build_constraint_set(region).overlaps_with(other_conditions):
                    next_regions.append(region)
                    continue
                if not self._return_region_can_be_shadowed_by_prior(
                    region,
                    info,
                    other,
                    prior_conditions=other_conditions,
                ):
                    next_regions.append(region)
                    continue
                next_regions.extend(
                    self._subtract_return_region_conjunction(
                        region,
                        other_conditions,
                    )
                )
            current_regions = [
                region
                for region in next_regions
                if not ConditionSimplifier.object_centric_is_contradiction(region)
            ]
            if not current_regions:
                break

        for split_index, region in enumerate(current_regions):
            preserved.append(
                replace(
                    info,
                    value=info.value,
                    conditions=region,
                    branch_index=self._split_branch_index(info.branch_index, original_index, split_index),
                )
            )
    return preserved

def _impl__return_region_priority_key(
    self,
    info: ReturnInfo,
    original_index: int,
) -> Tuple[int, int, int, int, int, int]:
    conditions = self._return_info_effective_region_conditions(info)
    exact_equality_count = sum(
        1 for condition in conditions if self._condition_is_constant_equality_guard(condition)
    )
    readonly_contract_score = self._readonly_reduction_contract_priority_score(info)
    unresolved_score = 1 if self._expression_contains_unresolved_value(info.value) else 0
    phi_score = 1 if self._expression_contains_phi(info.value) else 0
    return (
        -int(exact_equality_count),
        -int(readonly_contract_score),
        -len(conditions),
        unresolved_score,
        phi_score,
        int(original_index),
    )

def _impl__compare_return_region_order(
    self,
    left_item: Tuple[int, ReturnInfo],
    right_item: Tuple[int, ReturnInfo],
) -> int:
    left_original_index, left = left_item
    right_original_index, right = right_item
    left_conditions = self._return_info_effective_region_conditions(left)
    right_conditions = self._return_info_effective_region_conditions(right)

    if not ConditionSimplifier.object_centric_is_contradiction(
        list(left_conditions) + list(right_conditions)
    ):
        left_implies_right = self._return_region_conditions_imply(
            left_conditions,
            right_conditions,
        )
        right_implies_left = self._return_region_conditions_imply(
            right_conditions,
            left_conditions,
        )
        if left_implies_right and not right_implies_left:
            return -1
        if right_implies_left and not left_implies_right:
            return 1

    left_key = self._return_region_priority_key(left, left_original_index)
    right_key = self._return_region_priority_key(right, right_original_index)
    if left_key < right_key:
        return -1
    if left_key > right_key:
        return 1
    return 0

def _impl__return_region_can_be_shadowed_by_prior(
    self,
    region: Sequence[Condition],
    current: ReturnInfo,
    prior: ReturnInfo,
    *,
    prior_conditions: Optional[Sequence[Condition]] = None,
) -> bool:
    prior_conditions = ConditionSimplifier.simplify_conditions_object_centric(
        prior_conditions
        if prior_conditions is not None
        else self._return_info_effective_region_conditions(prior)
    )
    if not self._return_region_conditions_mutually_imply(region, prior_conditions):
        if (
            self._expression_contains_deferred_call_value(current.value)
            and not _expressions_equivalent(prior.value, current.value)
        ):
            if self.debug:
                self._debug_print(
                    "preserving deferred-call return region because prior concrete "
                    "case does not prove the unresolved region redundant"
                )
            return False
        return True

    prior_score = self._readonly_reduction_contract_priority_score(prior)
    current_score = self._readonly_reduction_contract_priority_score(current)
    if prior_score > current_score:
        return True
    if current_score > prior_score:
        return False

    # Same condition region with different values is not a valid partition
    # refinement unless one side carries a proof-backed semantic contract.
    return False

def _impl__return_region_conditions_imply(
    self,
    antecedent: Sequence[Condition],
    consequent: Sequence[Condition],
) -> bool:
    consequent = list(consequent or [])
    if not consequent:
        return True
    antecedent_set = ConditionSimplifier.build_constraint_set(antecedent or [])
    if antecedent_set.is_contradictory:
        return False
    return antecedent_set.implies_all(consequent)

def _impl__return_region_conditions_mutually_imply(
    self,
    left: Sequence[Condition],
    right: Sequence[Condition],
) -> bool:
    return self._return_region_conditions_imply(
        left,
        right,
    ) and self._return_region_conditions_imply(
        right,
        left,
    )

def _impl__subtract_return_region_conjunction(
    self,
    base_conditions: List[Condition],
    subtract_conditions: List[Condition],
) -> List[List[Condition]]:
    base = ConditionSimplifier.simplify_conditions_object_centric(base_conditions or [])
    subtract = ConditionSimplifier.simplify_conditions_object_centric(subtract_conditions or [])

    if not subtract:
        return [base]

    overlap = ConditionSimplifier.simplify_conditions_object_centric(base + subtract)
    if ConditionSimplifier.object_centric_is_contradiction(overlap):
        return [base]

    base_constraint_set = ConditionSimplifier.build_constraint_set(base)
    if base_constraint_set.implies_all(subtract):
        return []

    subtract_constraint_set = ConditionSimplifier.build_constraint_set(subtract)
    subtract_residual = subtract_constraint_set.residual_against(base)
    if not subtract_residual:
        return []

    residual_regions: List[List[Condition]] = []
    required_prefix: List[Condition] = []

    for condition in subtract_residual:
        candidate = ConditionSimplifier.simplify_conditions_object_centric(
            list(base) + list(required_prefix) + [condition.negate()]
        )
        if not ConditionSimplifier.object_centric_is_contradiction(candidate):
            residual_regions.append(candidate)
        required_prefix.append(condition)

    return residual_regions

def _impl__analysis_has_ambiguous_condition_region_returns(
    self,
    analysis: Optional[FunctionReturnAnalysis],
) -> bool:
    if analysis is None or len(analysis.returns or []) < 2:
        return False

    grouped: Dict[Tuple[str, str], List[ReturnInfo]] = {}
    for info in analysis.returns or []:
        key = (
            self._return_site_key(info),
            self._pruning_conditions_signature(info.conditions),
        )
        grouped.setdefault(key, []).append(info)

    for group in grouped.values():
        precise_group = [
            info
            for info in group
            if not self._expression_contains_unresolved_value(info.value)
        ]
        if len(precise_group) < 2:
            continue
        first = precise_group[0]
        if any(
            not _expressions_equivalent(first.value, candidate.value)
            for candidate in precise_group[1:]
        ):
            return True
    return False

def _impl__merge_equivalent_return_infos(
    self,
    return_infos: List[ReturnInfo],
) -> List[ReturnInfo]:
    if len(return_infos) < 2:
        return return_infos

    merged = list(return_infos)
    changed = True
    while changed:
        changed = False
        for i in range(len(merged)):
            for j in range(i + 1, len(merged)):
                combined = self._merge_return_info_pair(
                    merged[i],
                    merged[j],
                    merged,
                    i,
                    j,
                )
                if combined is None:
                    continue
                merged[i] = combined
                del merged[j]
                changed = True
                break
            if changed:
                break
    return merged

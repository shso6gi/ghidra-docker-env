# -*- coding: utf-8 -*-

import hashlib
from copy import deepcopy
from typing import Tuple
from unittest.mock import Mock

from scripts.function_tracer_pcode.analysis.effect_summary import (
    CanonicalLocation,
    CallArgumentEvidence,
    CallTargetResolutionEvidence,
    EffectSummary,
    StoreEffect,
    UnsupportedCallEffectRef,
    post_state_read_expression_for_location,
)
from scripts.function_tracer_pcode.equivalence.formula.builder import FormulaBuilderResult
from scripts.function_tracer_pcode.equivalence.formula.types import ParameterInfo
from scripts.function_tracer_pcode.equivalence.strategies.monolithic import MonolithicStrategy
from scripts.function_tracer_pcode.equivalence.strategies.pairwise import PairwiseStrategy
from scripts.function_tracer_pcode.equivalence.strategies.base import ReturnCoverageCheckResult
from scripts.function_tracer_pcode.equivalence.strategies.pairwise_models import (
    QueryResult,
    ReturnCase,
)
from scripts.function_tracer_pcode.equivalence.unknown_reason import (
    UnknownRecoveryActionStatus,
    UnknownRecoveryProofObligation,
    UnknownRecoveryProofKind,
    UnknownReasonRecord,
    UnknownReasonId,
    build_proof_obligation_id,
    build_unknown_recovery_actions,
    make_unknown_reason,
)
from scripts.function_tracer_pcode.model import (
    CallTargetRef,
    Condition,
    DeferredCallInfo,
    DeferredCallRef,
    Expression,
    FunctionReturnAnalysis,
    PcodeOpRef,
    ReturnInfo,
    StorageInfo,
    expression_provenance_key,
)
from scripts.function_tracer_pcode.model.runtime_refs import LocationBaseRef
from scripts.function_tracer_pcode.model.runtime_refs import UnknownValueRef
from scripts.function_tracer_pcode.smt import ParallelResult, SolverResult, SolverStatus
from scripts.function_tracer_pcode.validation.phase2_equivalence_blocking_unsafety import (
    _object_target_key_is_specific,
)


def _param(name: str, index: int = 0, size: int = 4, data_type: str = "int"):
    return {
        "name": name,
        "index": index,
        "size": size,
        "data_type": data_type,
        "is_signed": "unsigned" not in data_type,
    }


def _const(value: int, size: int = 4) -> Expression:
    return Expression.constant(value, size)


def _eq(lhs: Expression, rhs: Expression) -> Condition:
    return Condition(Expression.binary_op("INT_EQUAL", lhs, rhs), False)


def _ne(lhs: Expression, rhs: Expression) -> Condition:
    return Condition(Expression.binary_op("INT_NOTEQUAL", lhs, rhs), False)


def _deep_zext_target(name: str, index: int, depth: int = 300) -> Expression:
    expr = Expression.parameter(name, index, size=8)
    for _ in range(depth):
        expr = Expression.unary_op("INT_ZEXT", expr)
    return expr


def _deep_target_with_tail_op(
    name: str,
    index: int,
    tail_operator: str,
    depth: int = 8200,
) -> Expression:
    expr = Expression.parameter(name, index, size=8)
    expr = Expression.unary_op(tail_operator, expr)
    for _ in range(max(0, depth - 1)):
        expr = Expression.unary_op("INT_ZEXT", expr)
    return expr


def _build_symbolic_post_state_analysis(name: str) -> FunctionReturnAnalysis:
    params = [_param("trace", index=0, size=8, data_type="int *")]
    value = post_state_read_expression_for_location(
        CanonicalLocation("trace", 0, 4),
        params,
        symbolic=True,
    )
    return FunctionReturnAnalysis(
        function_name=name,
        entry_point="0x1000",
        parameters=params,
        returns=[ReturnInfo(address="0x1000", value=value, conditions=[])],
        return_type="int",
    )


def _base_context_for_single_int_param():
    return {
        "header_lines": [
            "(declare-const x_1 (_ BitVec 32))",
            "(declare-const x_2 (_ BitVec 32))",
            "(assert (= x_1 x_2))",
        ],
        "params1": [ParameterInfo(original_name="x", smt_name="x_1", bit_width=32, index=0)],
        "params2": [ParameterInfo(original_name="x", smt_name="x_2", bit_width=32, index=0)],
        "extra_vars1": [],
        "extra_vars2": [],
        "constrained_fragments": [],
        "return_size1": 32,
        "return_size2": 32,
    }


def _patch_pairwise_single_unsat_case(monkeypatch, strategy, analysis1, analysis2):
    case1 = ReturnCase(
        index=0,
        conditions=[],
        value_expr=analysis1.returns[0].value,
        return_info=analysis1.returns[0],
        return_type=analysis1.return_type or "int",
        parameters=analysis1.parameters,
    )
    case2 = ReturnCase(
        index=0,
        conditions=[],
        value_expr=analysis2.returns[0].value,
        return_info=analysis2.returns[0],
        return_type=analysis2.return_type or "int",
        parameters=analysis2.parameters,
    )
    monkeypatch.setattr(
        strategy,
        "_extract_return_cases",
        lambda analysis: [case1] if analysis.function_name == analysis1.function_name else [case2],
    )
    monkeypatch.setattr(strategy, "_prune_unreachable_cases", lambda cases, *_args, **_kwargs: cases)
    monkeypatch.setattr(strategy, "_cases_are_contradictory", lambda *_args, **_kwargs: False)
    monkeypatch.setattr(strategy, "_case_contains_unresolved_expression", lambda *_args, **_kwargs: False)
    strategy._solve_query_twostage = Mock(return_value=QueryResult(is_equivalent=True))


def _patch_pairwise_single_case(monkeypatch, strategy, analysis1, analysis2):
    case1 = ReturnCase(
        index=0,
        conditions=[],
        value_expr=analysis1.returns[0].value,
        return_info=analysis1.returns[0],
        return_type=analysis1.return_type or "int",
        parameters=analysis1.parameters,
    )
    case2 = ReturnCase(
        index=0,
        conditions=[],
        value_expr=analysis2.returns[0].value,
        return_info=analysis2.returns[0],
        return_type=analysis2.return_type or "int",
        parameters=analysis2.parameters,
    )
    monkeypatch.setattr(
        strategy,
        "_extract_return_cases",
        lambda analysis: [case1] if analysis.function_name == analysis1.function_name else [case2],
    )
    monkeypatch.setattr(strategy, "_prune_unreachable_cases", lambda cases, *_args, **_kwargs: cases)
    monkeypatch.setattr(strategy, "_cases_are_contradictory", lambda *_args, **_kwargs: False)


def _return_coverage_gap_analyses():
    x = Expression.parameter("x", 0, size=4)
    analysis1 = FunctionReturnAnalysis(
        function_name="func1",
        entry_point="0x1",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1", value=_const(1), conditions=[_eq(x, _const(0))])],
        return_type="int",
    )
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x2",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2", value=_const(1), conditions=[])],
        return_type="int",
    )
    return analysis1, analysis2


def _patch_pairwise_return_coverage_gap_case(monkeypatch, strategy, analysis1, analysis2):
    case1 = ReturnCase(
        index=0,
        conditions=[_eq(Expression.parameter("x", 0, size=4), _const(0))],
        value_expr=analysis1.returns[0].value,
        return_info=analysis1.returns[0],
        return_type=analysis1.return_type or "int",
        parameters=analysis1.parameters,
    )
    case2 = ReturnCase(
        index=0,
        conditions=[],
        value_expr=analysis2.returns[0].value,
        return_info=analysis2.returns[0],
        return_type=analysis2.return_type or "int",
        parameters=analysis2.parameters,
    )
    monkeypatch.setattr(
        strategy,
        "_extract_return_cases",
        lambda analysis: [case1] if analysis.function_name == analysis1.function_name else [case2],
    )
    monkeypatch.setattr(strategy, "_prune_unreachable_cases", lambda cases, *_args, **_kwargs: cases)
    monkeypatch.setattr(strategy, "_cases_are_contradictory", lambda *_args, **_kwargs: False)
    monkeypatch.setattr(strategy, "_case_contains_unresolved_expression", lambda *_args, **_kwargs: False)
    strategy._solve_query_twostage = Mock(return_value=QueryResult(is_equivalent=True))


def _analysis_with_unsupported_call_effect() -> FunctionReturnAnalysis:
    site = UnsupportedCallEffectRef(
        pcode_op_ref=PcodeOpRef(address_offset=0x3020, seq_time=4, seq_order=1, mnemonic="CALLIND"),
        target_ref=None,
        target_expr=Expression.parameter("fp", 0, size=8),
        reason="target_identity_unavailable",
        order_key=9,
    )
    return FunctionReturnAnalysis(
        function_name="func1",
        entry_point="0x1000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1000", value=_const(1), conditions=[])],
        return_type="int",
        effect_summary=EffectSummary(
            parameter_names=["x"],
            effects=[],
            has_unsupported_call=True,
            unsupported_call_sites=(site,),
        ),
    )


def _analysis_with_unknown_indirect_call_effect(
    *,
    function_name: str,
    binary_id: str,
    entry: int,
    target_param_index: int = 0,
    argument_indices=(1, 2),
    target_expr_missing: bool = False,
    reason: str = "target_identity_unavailable",
    path_conditions=(),
) -> FunctionReturnAnalysis:
    parameters = [
        _param("fp", index=0, size=8),
        _param("a", index=1, size=4),
        _param("b", index=2, size=4),
    ]
    target_expr = None
    if not target_expr_missing:
        target_expr = Expression.parameter(
            parameters[target_param_index]["name"],
            target_param_index,
            size=parameters[target_param_index]["size"],
        )
    arguments = tuple(
        Expression.parameter(
            parameters[index]["name"],
            index,
            size=parameters[index]["size"],
        )
        for index in argument_indices
    )
    pcode_ref = PcodeOpRef(
        address_offset=entry + 0x20,
        seq_time=4,
        seq_order=1,
        block_index=0,
        mnemonic="CALLIND",
        input_sizes=(8, 4, 4),
        binary_id=binary_id,
        function_entry_space="ram",
        function_entry_offset=entry,
        target_space="ram",
        target_offset=entry + 0x20,
        opcode=8,
        local_op_ordinal=0,
    )
    site = UnsupportedCallEffectRef(
        pcode_op_ref=pcode_ref,
        target_ref=None,
        target_expr=target_expr,
        arguments=arguments,
        path_conditions=tuple(path_conditions or ()),
        reason=reason,
        order_key=9,
    )
    return FunctionReturnAnalysis(
        function_name=function_name,
        entry_point=hex(entry),
        function_ref=CallTargetRef.from_name(function_name, program_id=entry, entry_offset=entry),
        binary_id=binary_id,
        parameters=parameters,
        returns=[ReturnInfo(address=hex(entry), value=_const(1), conditions=[])],
        return_type="int",
        effect_summary=EffectSummary(
            parameter_names=[param["name"] for param in parameters],
            effects=[],
            has_unsupported_call=True,
            unsupported_call_sites=(site,),
        ),
    )


def _analysis_with_known_unsupported_call_effect(
    *,
    function_name: str,
    binary_id: str,
    entry: int,
    argument_indices=(1, 2),
    target_expr_missing: bool = False,
    reason: str = "callee_unsupported_call_may_expose_parameter_memory",
) -> FunctionReturnAnalysis:
    analysis = _analysis_with_unknown_indirect_call_effect(
        function_name=function_name,
        binary_id=binary_id,
        entry=entry,
        argument_indices=argument_indices,
        target_expr_missing=target_expr_missing,
        reason=reason,
    )
    if not analysis.effect_summary.unsupported_call_sites:
        return analysis

    target_ref = CallTargetRef.from_code_address(
        entry + 0x20,
        program_id=entry,
        display_hint="known_callee",
    )
    site = analysis.effect_summary.unsupported_call_sites[0]
    analysis.effect_summary.unsupported_call_sites = (
        UnsupportedCallEffectRef(
            pcode_op_ref=site.pcode_op_ref,
            target_ref=target_ref,
            target_expr=site.target_expr,
            arguments=site.arguments,
            path_conditions=site.path_conditions,
            reason=site.reason,
            order_key=site.order_key,
        ),
    )
    return analysis


def _analysis_with_deferred_call_argument_blocker(
    *,
    function_name: str,
    binary_id: str,
    entry: int,
    target_param_index: int = 0,
    argument_indices=(1, 2),
    target_expr_missing: bool = False,
    duplicate: bool = False,
    return_deferred_unknown: bool = False,
    unknown_size: int = 4,
    call_argument_recovery_status: str = CallArgumentEvidence.RECOVERY_INCONCLUSIVE,
) -> FunctionReturnAnalysis:
    parameters = [
        _param("fp", index=0, size=8),
        _param("a", index=1, size=4),
        _param("b", index=2, size=4),
    ]
    target_expr = None
    if not target_expr_missing:
        target_expr = Expression.parameter(
            parameters[target_param_index]["name"],
            target_param_index,
            size=parameters[target_param_index]["size"],
        )
    arguments = [
        Expression.parameter(
            parameters[index]["name"],
            index,
            size=parameters[index]["size"],
        )
        for index in argument_indices
    ]

    def _deferred(sequence: int, address_delta: int) -> DeferredCallInfo:
        pcode_ref = PcodeOpRef(
            address_offset=entry + address_delta,
            seq_time=4 + sequence,
            seq_order=1,
            block_index=0,
            mnemonic="CALLIND",
            input_sizes=(8, 4, 4),
            binary_id=binary_id,
            function_entry_space="ram",
            function_entry_offset=entry,
            target_space="ram",
            target_offset=entry + address_delta,
            opcode=8,
            local_op_ordinal=sequence,
        )
        return DeferredCallInfo(
            placeholder_name=f"call_out_of_scope:{function_name}#{sequence}",
            target_ref=CallTargetRef.unknown(),
            arguments=arguments,
            call_target_expr=target_expr,
            deferred_call_ref=DeferredCallRef(
                caller_program_id=entry,
                caller_entry_offset=entry,
                pcode_op_ref=pcode_ref,
                target_ref=CallTargetRef.unknown(),
                sequence=sequence,
            ),
            call_argument_recovery_status=call_argument_recovery_status,
            call_argument_recovery_reason="argument_recovery_inconclusive",
        )

    deferred = _deferred(1, 0x20)
    deferred_calls = {deferred.deferred_call_ref.stable_key(): deferred}
    if duplicate:
        other = _deferred(2, 0x40)
        deferred_calls[other.deferred_call_ref.stable_key()] = other
    return_value = _const(1)
    if return_deferred_unknown:
        return_value = Expression.unknown(
            deferred.placeholder_name,
            runtime_ref=deferred.unknown_ref,
        ).clone_with(size=unknown_size)
    return FunctionReturnAnalysis(
        function_name=function_name,
        entry_point=hex(entry),
        function_ref=CallTargetRef.from_name(function_name, program_id=entry, entry_offset=entry),
        binary_id=binary_id,
        parameters=parameters,
        returns=[ReturnInfo(address=hex(entry), value=return_value, conditions=[])],
        return_type="int",
        effect_summary=EffectSummary(
            parameter_names=[param["name"] for param in parameters],
            effects=[],
        ),
        deferred_calls=deferred_calls,
    )


def _analysis_with_self_recursive_unsupported_call_effect(
    *,
    binary_id: str = "B1",
    entry: int = 0x1000,
    target_entry: int = 0x1000,
    target_name: str = "func1",
    reason: str = "callee_effect_summary_missing",
) -> FunctionReturnAnalysis:
    target_ref = CallTargetRef.from_name(target_name, program_id=1, entry_offset=target_entry)
    site = UnsupportedCallEffectRef(
        pcode_op_ref=PcodeOpRef(
            address_offset=entry + 0x20,
            seq_time=7,
            seq_order=3,
            block_index=1,
            mnemonic="CALL",
            input_sizes=(8,),
            binary_id=binary_id,
            function_entry_space="ram",
            function_entry_offset=entry,
            target_space="ram",
            target_offset=entry + 0x20,
            opcode=7,
            local_op_ordinal=3,
        ),
        target_ref=target_ref,
        target_expr=Expression.constant(target_entry, 8),
        reason=reason,
        order_key=11,
    )
    return FunctionReturnAnalysis(
        function_name="func1",
        entry_point=hex(entry),
        function_ref=CallTargetRef.from_name("func1", program_id=1, entry_offset=entry),
        parameters=[_param("x")],
        returns=[ReturnInfo(address=hex(entry), value=_const(1), conditions=[])],
        return_type="int",
        effect_summary=EffectSummary(
            parameter_names=["x"],
            effects=[],
            has_unsupported_call=True,
            unsupported_call_sites=(site,),
        ),
        binary_id=binary_id,
    )


def _analysis_with_effect_call_argument_evidence() -> FunctionReturnAnalysis:
    pcode_ref = PcodeOpRef(
        address_offset=0x1020,
        seq_time=5,
        seq_order=1,
        block_index=0,
        mnemonic="CALL",
        input_sizes=(8, 4),
        binary_id="B1",
        function_entry_space="ram",
        function_entry_offset=0x1000,
        target_space="ram",
        target_offset=0x1020,
        opcode=7,
        local_op_ordinal=2,
    )
    target_ref = CallTargetRef.from_name("callee", program_id=1, entry_offset=0x2000)
    evidence = CallArgumentEvidence(
        pcode_op_ref=pcode_ref,
        target_ref=target_ref,
        callee_param_identities=(("parameter", 0),),
        arguments=(Expression.parameter("x", 0, size=4),),
        sources=("reaching_def",),
        path_conditions=((),),
        coverage_complete=True,
    )
    return FunctionReturnAnalysis(
        function_name="func1",
        entry_point="0x1000",
        function_ref=CallTargetRef.from_name("func1", program_id=1, entry_offset=0x1000),
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1000", value=_const(1), conditions=[])],
        return_type="int",
        effect_summary=EffectSummary(
            parameter_names=["x"],
            effects=[],
            call_argument_evidence={pcode_ref.stable_key(): evidence},
        ),
        binary_id="B1",
    )


def _analysis_with_two_effect_call_argument_evidences() -> Tuple[
    FunctionReturnAnalysis,
    PcodeOpRef,
    PcodeOpRef,
]:
    target_ref = CallTargetRef.from_name("callee", program_id=1, entry_offset=0x2000)
    incomplete_pcode_ref = PcodeOpRef(
        address_offset=0x1020,
        seq_time=5,
        seq_order=1,
        block_index=0,
        mnemonic="CALL",
        input_sizes=(8, 4),
        binary_id="B1",
        function_entry_space="ram",
        function_entry_offset=0x1000,
        target_space="ram",
        target_offset=0x1020,
        opcode=7,
        local_op_ordinal=2,
    )
    complete_pcode_ref = PcodeOpRef(
        address_offset=0x1030,
        seq_time=7,
        seq_order=2,
        block_index=0,
        mnemonic="CALL",
        input_sizes=(8, 4),
        binary_id="B1",
        function_entry_space="ram",
        function_entry_offset=0x1000,
        target_space="ram",
        target_offset=0x1030,
        opcode=7,
        local_op_ordinal=3,
    )
    incomplete_evidence = CallArgumentEvidence(
        pcode_op_ref=incomplete_pcode_ref,
        target_ref=target_ref,
        callee_param_identities=(
            ("parameter", 0),
        ),
        arguments=(Expression.parameter("x", 0, size=4),),
        sources=("reaching_def",),
        path_conditions=((),),
        coverage_complete=False,
    )
    complete_evidence = CallArgumentEvidence(
        pcode_op_ref=complete_pcode_ref,
        target_ref=target_ref,
        callee_param_identities=(
            ("parameter", 0),
        ),
        arguments=(Expression.parameter("x", 0, size=4),),
        sources=("reaching_def",),
        path_conditions=((),),
        coverage_complete=True,
    )
    return (
        FunctionReturnAnalysis(
            function_name="func1",
            entry_point="0x1000",
            function_ref=CallTargetRef.from_name("func1", program_id=1, entry_offset=0x1000),
            parameters=[_param("x")],
            returns=[ReturnInfo(address="0x1000", value=_const(1), conditions=[])],
            return_type="int",
            effect_summary=EffectSummary(
                parameter_names=["x"],
                effects=[],
                call_argument_evidence={
                    incomplete_pcode_ref.stable_key(): incomplete_evidence,
                    complete_pcode_ref.stable_key(): complete_evidence,
                },
            ),
            binary_id="B1",
        ),
        incomplete_pcode_ref,
        complete_pcode_ref,
    )


def _analysis_with_effect_call_target_resolution_evidence() -> FunctionReturnAnalysis:
    pcode_ref = PcodeOpRef(
        address_offset=0x1030,
        seq_time=7,
        seq_order=1,
        block_index=0,
        mnemonic="CALLIND",
        input_sizes=(8, 4),
        binary_id="B1",
        function_entry_space="ram",
        function_entry_offset=0x1000,
        target_space="ram",
        target_offset=0x1030,
        opcode=8,
        local_op_ordinal=3,
    )
    target_expr = Expression.parameter("fp", 0, size=8)
    target_ref = CallTargetRef.from_name("dispatch_impl", program_id=1, entry_offset=0x3000)
    evidence = CallTargetResolutionEvidence(
        pcode_op_ref=pcode_ref,
        target_ref=target_ref,
        target_expr=target_expr,
        resolution_kind="pathless_target_resolution",
        path_condition_keys=(
            (
                "condition",
                False,
                _eq(Expression.parameter("selector", 0, size=4), _const(1)).structural_key(),
            ),
        ),
        target_condition_keys=(),
        order_key=3,
    )
    return FunctionReturnAnalysis(
        function_name="func1",
        entry_point="0x1000",
        function_ref=CallTargetRef.from_name("func1", program_id=1, entry_offset=0x1000),
        parameters=[_param("fp", index=0, size=8), _param("selector", index=1)],
        returns=[ReturnInfo(address="0x1000", value=_const(1), conditions=[])],
        return_type="int",
        effect_summary=EffectSummary(
            parameter_names=["fp", "selector"],
            effects=[],
            call_target_resolution_evidence=(evidence,),
        ),
        binary_id="B1",
    )


def _call_effect_summary_proof_evidence(object_target_key=None, **overrides):
    target_expr_key = ("typed_target_expression", ("runtime_ref", ("param", "fp", 0)))
    callee_identity = ("unknown", "B1", ("target_expression", target_expr_key))
    pcode_key = (
        "pcode_op",
        "B1",
        ("function_entry", "ram", 0x1000),
        ("seq_target", "ram", 0x3020),
        4,
        1,
        "CALLIND",
        0,
    )
    object_target_key = object_target_key or (
        "unsupported_call_effect",
        "function1",
        ("function_ref", ("function", "B1", 0x1000)),
        (
            "runtime_ref",
            "unsupported_call_effect",
            ("pcode_op_ref", pcode_key),
            ("callee_identity", callee_identity),
            ("typed_target_expression", target_expr_key),
            ("argument_keys", ()),
        ),
        (
            "callsite_storage",
            ("pcode_op_ref", pcode_key),
            ("callee_identity", callee_identity),
            ("target_expression", target_expr_key),
            ("argument_keys", ()),
        ),
        ("effect_ordinal", 9),
        "target_identity_unavailable",
    )
    evidence = {
        "object_derived": True,
        "status": "complete",
        "reason_id": UnknownReasonId.EQUIVALENCE_BLOCKING_UNSAFETY.value,
        "recovery_proof_kind": UnknownRecoveryProofKind.CALL_EFFECT_SUMMARY_PROOF.value,
        "proof_stage": "object_evidence_collected",
        "evidence_kind": "call_effect_summary",
        "object_target_key": object_target_key,
    }
    evidence["proof_obligation_id"] = _expected_call_effect_summary_proof_id(evidence)
    evidence.update(overrides)
    return evidence


def _call_effect_summary_proof_content(object_target_key):
    kind = object_target_key[0] if object_target_key else None
    runtime_ref = ("runtime_ref", "unsupported_call_effect", object_target_key)
    callsite_storage = ("callsite_storage", "unsupported_call_effect", object_target_key)
    peer_object_target_key = object_target_key
    if kind == "call_argument_evidence":
        runtime_ref = (
            "runtime_ref",
            "call_argument",
            ("pcode_op_ref", object_target_key[3]),
            ("callee_identity", object_target_key[4]),
        )
        callsite_storage = (
            "callsite_storage",
            "call_argument",
            ("argument_keys", object_target_key[5]),
        )
    elif kind == "call_target_resolution_evidence":
        runtime_ref = object_target_key[3]
        callsite_storage = object_target_key[4]
    elif kind == "unsupported_call_effect":
        runtime_ref = object_target_key[3]
        callsite_storage = object_target_key[4]
        peer_object_target_key = (
            object_target_key[0],
            "function2" if object_target_key[1] == "function1" else "function1",
            *object_target_key[2:],
        )
    local_callsite_path_guard = PairwiseStrategy._unsupported_call_effect_path_condition_key(
        object_target_key
    )
    peer_callsite_path_guard = PairwiseStrategy._unsupported_call_effect_path_condition_key(
        peer_object_target_key
    )
    content = {
        "object_derived": True,
        "status": "complete",
        "proof_rule": (
            "matched_unknown_indirect_no_store_call_effect"
            if kind == "unsupported_call_effect"
            else "call_argument_evidence_phase15_complete"
            if kind == "call_argument_evidence"
            else "call_effect_object_evidence_complete"
        ),
        "object_target_key": object_target_key,
        "peer_object_target_key": peer_object_target_key,
        "call_effect_summary": {
            "status": "complete",
            "summary_source": ("effect_summary", kind),
            "evidence_kind": "call_effect_summary",
            "object_target_key": object_target_key,
            "peer_object_target_key": peer_object_target_key,
            "unsupported_reason": "target_identity_unavailable",
            "local_store_effect_count": 0,
            "matching_local_unsupported_call_site_count": (
                1 if kind == "unsupported_call_effect" else None
            ),
            "matching_peer_unsupported_call_site_count": (
                1 if kind == "unsupported_call_effect" else None
            ),
        },
        "runtime_ref": {
            "status": "complete",
            "runtime_ref": runtime_ref,
            "peer_runtime_ref": peer_object_target_key[3] if kind == "unsupported_call_effect" else runtime_ref,
            "matched_target_expression_key": (
                PairwiseStrategy._cross_binary_call_effect_component_key(
                    PairwiseStrategy._unsupported_call_effect_target_expression_key(object_target_key)
                )
                if kind == "unsupported_call_effect"
                else None
            ),
        },
        "callsite_storage": {
            "status": "complete",
            "callsite_storage": callsite_storage,
            "peer_callsite_storage": (
                peer_object_target_key[4] if kind == "unsupported_call_effect" else callsite_storage
            ),
            "matched_argument_keys": (
                PairwiseStrategy._cross_binary_call_effect_component_key(
                    PairwiseStrategy._unsupported_call_effect_argument_keys(object_target_key)
                )
                if kind == "unsupported_call_effect"
                else None
            ),
        },
        "compatibility_policy": (
            PairwiseStrategy._unsupported_call_effect_compatibility_policy_evidence(
                object_target_key,
                peer_object_target_key,
            )
            if kind == "unsupported_call_effect"
            else None
        ),
    }
    if kind == "unsupported_call_effect":
        content["call_effect_surface"] = {
            "status": "complete",
            "guard_equivalence_mode": "path_guard_equivalence",
            "local_callsite_path_guard_key": local_callsite_path_guard,
            "peer_callsite_path_guard_key": peer_callsite_path_guard,
            "call_occurrence": {
                "status": "complete",
                "analysis_key": object_target_key[2],
                "effect_ordinal": object_target_key[5],
                "occurrence_index": 0,
                "unsupported_call_site_count": 1,
                "call_order_key_sequence": (object_target_key[5],),
            },
            "peer_call_occurrence": {
                "status": "complete",
                "analysis_key": peer_object_target_key[2],
                "effect_ordinal": peer_object_target_key[5],
                "occurrence_index": 0,
                "unsupported_call_site_count": 1,
                "call_order_key_sequence": (peer_object_target_key[5],),
            },
            "caller_observed_memory_write": {
                "status": "complete",
                "scope": "whole_function_effect_summary",
                "local_store_effect_count": 0,
                "peer_store_effect_count": 0,
                "local_incomplete_reason_count": 0,
                "peer_incomplete_reason_count": 0,
            },
            "call_output_use": {
                "status": "complete",
                "classification": "not_exposed_to_return_or_call_effect_surface",
                "pcode_op_ref": PairwiseStrategy._unsupported_call_effect_pcode_ref_key(
                    object_target_key
                ),
                "checked_surface": "return_values_return_guards_and_call_effect_inputs",
            },
            "peer_call_output_use": {
                "status": "complete",
                "classification": "not_exposed_to_return_or_call_effect_surface",
                "pcode_op_ref": PairwiseStrategy._unsupported_call_effect_pcode_ref_key(
                    peer_object_target_key
                ),
                "checked_surface": "return_values_return_guards_and_call_effect_inputs",
            },
        }
    if kind == "call_argument_evidence":
        bounded_refinement = _bounded_call_refinement_section(object_target_key)
        content.update(
            {
                "callee_summary_completion": {
                    "status": "complete",
                    "object_target_key": object_target_key,
                    "callee_identity": object_target_key[4],
                    "return_coverage_status": "complete",
                    "effect_summary_status": "complete",
                    "memory_policy_status": "complete",
                    "unsupported_call_policy_status": "complete",
                    "bounded_refinement_evidence_ref": bounded_refinement["object_target_key"],
                    "callee_return_partition_key": bounded_refinement["callee_return_partition_key"],
                },
                "callee_precondition": {
                    "status": "complete",
                    "object_target_key": object_target_key,
                    "caller_guard_implies_callee_precondition": True,
                    "abi_coercion": {
                        "status": "complete",
                        "argument_widths": ("same_width",),
                        "sign_zero_extension": "identity",
                        "abi_narrow_wide_coercion": "none",
                        "callee_parameter_interpretation": "same_integer_value",
                    },
                },
                "argument_value_provenance": {
                    "status": "complete",
                    "object_target_key": object_target_key,
                    "argument_keys": object_target_key[5],
                    "value_provenance_equivalent": True,
                },
                "proof_dependency_graph": {
                    "status": "complete",
                    "object_target_key": object_target_key,
                    "cycle_policy": "acyclic",
                },
                "bounded_refinement": bounded_refinement,
            }
        )
    return content


def _bounded_call_refinement_section(object_target_key, **overrides):
    bounded_key = (
        "bounded_call_refinement_expansion",
        ("analysis", "caller"),
        object_target_key[3],
        object_target_key[4],
        tuple(("argument_signature", index) for index, _arg in enumerate(object_target_key[5])),
        ("analysis", "callee"),
        (("return", 0, ("const", 1)),),
        (),
        1,
        2,
    )
    section = {
        "object_derived": True,
        "status": "complete",
        "evidence_kind": "bounded_call_refinement_expansion",
        "object_target_key": bounded_key,
        "call_argument_object_target_key": object_target_key,
        "callsite_pcode_key": object_target_key[3],
        "callee_identity": object_target_key[4],
        "callee_return_partition_key": bounded_key[6],
        "callee_summary_requires_completed_proof": False,
        "callee_completed_proof_ids": (),
        "callee_completed_proof_evidence_ids": (),
        "result_count": 1,
        "dependency_cycle": False,
        "truncated": False,
    }
    section.update(overrides)
    return section


def _complete_call_effect_summary_proof_evidence(object_target_key, **overrides):
    evidence = _call_effect_summary_proof_evidence(object_target_key=object_target_key)
    evidence["proof_content"] = _call_effect_summary_proof_content(object_target_key)
    evidence.update(overrides)
    return evidence


def _attach_bounded_call_refinement_expansion_evidence(
    analysis,
    object_target_key,
    *,
    content_overrides=None,
):
    section = _bounded_call_refinement_section(object_target_key, **(content_overrides or {}))
    record = {
        "object_derived": True,
        "status": "complete",
        "evidence_kind": "bounded_call_refinement_expansion",
        "proof_stage": "bounded_call_refinement",
        "object_target_key": section["object_target_key"],
        "proof_source": "bounded_call_refinement_deferred_expanded",
        "proof_content": {
            "object_derived": True,
            "status": section["status"],
            "object_target_key": section["object_target_key"],
            "callsite_pcode_key": section["callsite_pcode_key"],
            "callee_identity": section["callee_identity"],
            "argument_signature": section["object_target_key"][4],
            "callee_analysis_entry": section["object_target_key"][5],
            "callee_return_partition_key": section["callee_return_partition_key"],
            "callee_return_case_count": 1,
            "callee_summary_requires_completed_proof": section[
                "callee_summary_requires_completed_proof"
            ],
            "callee_completed_proof_ids": section["callee_completed_proof_ids"],
            "callee_completed_proof_evidence_ids": section["callee_completed_proof_evidence_ids"],
            "callee_effect_summary_clean": True,
            "target_conditions_key": (),
            "result_count": section["result_count"],
            "max_unroll": 2,
            "dependency_cycle": section["dependency_cycle"],
            "truncated": section["truncated"],
        },
    }
    if content_overrides:
        record["proof_content"].update(content_overrides)
    analysis.completed_recovery_proof_evidence = tuple(
        getattr(analysis, "completed_recovery_proof_evidence", ()) or ()
    ) + (record,)


def _completed_proof_ids_for_call_effect_evidence(evidence):
    analysis = FunctionReturnAnalysis(
        function_name="func1",
        entry_point="0x1000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1000", value=_const(1), conditions=[])],
        return_type="int",
        completed_recovery_proof_evidence=(evidence,),
    )
    return PairwiseStrategy._completed_recovery_proof_ids(analysis)


def _blocking_unsafety_object_target_key(blocking_reason, analysis1):
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x2000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=_const(1), conditions=[])],
        return_type="int",
    )
    reason = strategy._make_blocking_unsafety_unknown_reason(
        blocking_reason,
        analysis1,
        analysis2,
        stage="S_PAIRWISE",
    )
    return reason.object_target_key


def _analysis_with_call_effect_summary_proof_evidence(**evidence_overrides) -> FunctionReturnAnalysis:
    return FunctionReturnAnalysis(
        function_name="func1",
        entry_point="0x1000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1000", value=_const(1), conditions=[])],
        return_type="int",
        completed_recovery_proof_evidence=(
            _call_effect_summary_proof_evidence(**evidence_overrides),
        ),
    )


def _expected_call_effect_summary_proof_id(evidence):
    return build_proof_obligation_id(
        UnknownReasonId.EQUIVALENCE_BLOCKING_UNSAFETY.value,
        evidence["proof_stage"],
        evidence["recovery_proof_kind"],
        evidence["evidence_kind"],
        evidence["object_target_key"],
    )


def _return_coverage_structural_fixture_from_target(object_target_key):
    cases = PairwiseStrategy._return_coverage_target_partition_cases(object_target_key)
    assert cases is not None
    guard_entries = []
    miss_entries = []
    for index, case in enumerate(cases):
        fields = {
            field[0]: field[1]
            for field in case[1:]
            if isinstance(field, tuple) and len(field) == 2
        }
        guard_entries.append(
            (
                "return_case_guard_set",
                index,
                ("guard_structural_keys", fields["guards"]),
                ("return_value_structural_key", fields["return_value"]),
            )
        )
        miss_entries.append(
            (
                "case_miss_formula",
                index,
                fields["case_miss_formula"],
            )
        )
    guard_entries = PairwiseStrategy._canonicalize_key_sequence(guard_entries)
    miss_entries = PairwiseStrategy._canonicalize_key_sequence(miss_entries)
    return {
        "structural_guard_keys": {
            "status": "complete",
            "case_count": len(guard_entries),
            "keys": guard_entries,
        },
        "structural_miss_formula_keys": {
            "status": "complete",
            "case_count": len(miss_entries),
            "keys": miss_entries,
        },
    }


def _return_coverage_completion_evidence(
    action,
    reason_id: UnknownReasonId = UnknownReasonId.RETURN_COVERAGE_GAP,
    **overrides,
):
    structural_fixture = _return_coverage_structural_fixture_from_target(action.object_target_key)
    proof_content = {
        "proof_schema_version": PairwiseStrategy._RETURN_COVERAGE_PROOF_SCHEMA_VERSION,
        "normalization_schema_version": PairwiseStrategy._RETURN_COVERAGE_NORMALIZATION_SCHEMA_VERSION,
        "proof_target_identity": action.object_target_key,
        **structural_fixture,
        "coverage_solver_evidence": {
            "status": "unsat",
            "proof_method": "smt_coverage_query",
        },
        "bit_width_signedness_metadata": {
            "status": "complete",
            "bit_widths": (32,),
            "signedness": ("equality",),
        },
        "case_guard_disjunction": {
            "status": "complete",
            "query_cases": ("(true)",),
            "case_count": 1,
        },
        "normalized_guard_formula": {
            "status": "complete",
            "query": "(or true)",
        },
        "coverage_guard_evidence": {
            "status": "complete",
            "guard_source": "return_partition_guard_set",
            "coverage_status": "covered",
            "coverage_proof_method": "test_fixture",
            "case_count": 1,
            "normalized_guard_formula_sha256": hashlib.sha256(b"(or true)").hexdigest(),
        },
    }
    evidence = {
        "object_derived": True,
        "status": "complete",
        "reason_id": reason_id.value,
        "recovery_proof_kind": UnknownRecoveryProofKind.RETURN_COVERAGE_COMPLETION.value,
        "target_schema_version": PairwiseStrategy._RETURN_COVERAGE_TARGET_SCHEMA_VERSION,
        "proof_schema_version": PairwiseStrategy._RETURN_COVERAGE_PROOF_SCHEMA_VERSION,
        "proof_stage": action.proof_stage,
        "evidence_kind": action.evidence_kind,
        "object_target_key": action.object_target_key,
        "proof_obligation_id": action.proof_obligation_id,
        "proof_content": proof_content,
    }
    evidence.update(overrides)
    return evidence


def _return_coverage_completion_evidence_without_proof_id(action):
    evidence = _return_coverage_completion_evidence(action)
    evidence.pop("proof_obligation_id", None)
    return evidence


def _normalization_aware_return_coverage_evidence(action):
    evidence = _return_coverage_completion_evidence(action)
    policy = PairwiseStrategy._return_coverage_normalization_policy(
        rules=(
            {
                "rule_id": "subpiece_low32_guard",
                "expression_kind": "guard",
                "width": 32,
                "signedness": "signed",
            },
        )
    )
    policy_digest = PairwiseStrategy._return_coverage_normalization_policy_digest(policy)
    query = evidence["proof_content"]["normalized_guard_formula"]["query"]
    raw_identity = ("raw_guard_identity", ("guard", "raw"))
    normalized_identity = ("normalized_guard_identity", ("guard", "normalized"))
    evidence["proof_schema_version"] = PairwiseStrategy._RETURN_COVERAGE_NORMALIZATION_AWARE_PROOF_SCHEMA_VERSION
    evidence["normalization_required"] = True
    evidence["proof_content"] = deepcopy(evidence["proof_content"])
    evidence["proof_content"].update(
        {
            "proof_schema_version": PairwiseStrategy._RETURN_COVERAGE_NORMALIZATION_AWARE_PROOF_SCHEMA_VERSION,
            "normalization_required": True,
            "normalization_policy": policy,
            "normalization_policy_digest": policy_digest,
            "raw_normalized_correspondence": {
                "status": "complete",
                "normalization_policy_digest": policy_digest,
                "raw_guard_identity": raw_identity,
                "normalized_guard_identity": normalized_identity,
                "rule_id": "subpiece_low32_guard",
                "before_structural_key": ("before", raw_identity),
                "after_structural_key": ("after", normalized_identity),
                "equivalence_proof": {
                    "status": "unsat",
                    "proof_method": "smt_equivalence_under_active_guard",
                },
            },
            "normalized_guard_payload": {
                "normalization_policy_digest": policy_digest,
                "raw_identity": raw_identity,
                "normalized_identity": normalized_identity,
                "final_query_sha256": hashlib.sha256(query.encode("utf-8")).hexdigest(),
            },
        }
    )
    return evidence


def _retarget_return_coverage_evidence(evidence, object_target_key):
    retargeted = deepcopy(evidence)
    retargeted["object_target_key"] = object_target_key
    retargeted["proof_content"]["proof_target_identity"] = object_target_key
    retargeted["proof_obligation_id"] = build_proof_obligation_id(
        retargeted["reason_id"],
        retargeted["proof_stage"],
        retargeted["recovery_proof_kind"],
        retargeted["evidence_kind"],
        object_target_key,
    )
    return retargeted


def _sat_unsafety_resolution_evidence(action, counterexample_raw=None, **overrides):
    if counterexample_raw is None:
        counterexample_raw = {"x_1": 0, "x_2": 0}
    evidence = {
        "object_derived": True,
        "status": "complete",
        "reason_id": UnknownReasonId.SAT_UNSAFETY.value,
        "recovery_proof_kind": UnknownRecoveryProofKind.SAT_UNSAFETY_RESOLUTION.value,
        "proof_stage": action.proof_stage,
        "evidence_kind": action.evidence_kind,
        "object_target_key": action.object_target_key,
        "proof_obligation_id": action.proof_obligation_id,
        "proof_content": {
            "object_derived": True,
            "object_target_key": action.object_target_key,
            "counterexample_replay": {
                "status": "replayed",
                "model_ref": ("query_model", "pair", action.pair_or_case),
                "fixed_model_assertion_count": 2,
                "counterexample_symbol_keys": ("x_1", "x_2"),
                "counterexample_model_sha256": (
                    PairwiseStrategy._counterexample_model_fingerprint(counterexample_raw)
                ),
            },
            "active_unsafety_discharge": {
                "status": "discharged",
                "discharged_reason_refs": tuple(action.evidence_refs),
            },
            "coverage_effect_safety": {
                "status": "proven",
                "coverage_status": "covered",
                "effect_status": "supported",
            },
        },
    }
    evidence.update(overrides)
    return evidence


def _sat_unsafety_resolution_action():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    analysis1 = _analysis_with_unsupported_call_effect()
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x2000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=_const(2), conditions=[])],
        return_type="int",
    )
    case1 = ReturnCase(
        index=0,
        conditions=[],
        value_expr=analysis1.returns[0].value,
        return_info=analysis1.returns[0],
        return_type=analysis1.return_type or "int",
        parameters=analysis1.parameters,
    )
    case2 = ReturnCase(
        index=0,
        conditions=[],
        value_expr=analysis2.returns[0].value,
        return_info=analysis2.returns[0],
        return_type=analysis2.return_type or "int",
        parameters=analysis2.parameters,
    )
    reason = strategy._make_sat_unsafety_unknown_reason(
        ("function1:unsupported_call_effect_summary",),
        analysis1,
        analysis2,
        case1=case1,
        case2=case2,
        pair_id="(0,0)",
        stage="S_PAIRWISE",
    )
    return build_unknown_recovery_actions([reason])[0]


def _monolithic_return_coverage_gap_setup():
    class _CoverageGapUnsatSolverRunner:
        def __init__(self):
            self.timeout = 5

        def run_parallel(self, _query: str):
            return ParallelResult(results=[SolverResult("fake", SolverStatus.UNSAT)])

        def run_sequential(self, query: str):
            if "Return coverage gap query: function1" in query:
                return ParallelResult(
                    results=[SolverResult("fake", SolverStatus.SAT, model={"x_1": 7, "x_2": 7})]
                )
            return ParallelResult(results=[SolverResult("fake", SolverStatus.UNSAT)])

    analysis1, analysis2 = _return_coverage_gap_analyses()
    formula_builder = Mock()
    formula_builder.build_equivalence_formula_extended.return_value = FormulaBuilderResult(
        formula="(set-logic QF_BV)\n(check-sat)",
        return_var1="return_1",
        return_var2="return_2",
        constrained_fragments=[],
        extra_vars1=[],
        extra_vars2=[],
        param_fragment_constrained=[],
    )
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    strategy = MonolithicStrategy(formula_builder, _CoverageGapUnsatSolverRunner(), debug=False)
    return strategy, analysis1, analysis2


def test_function_return_analysis_marks_symbolic_post_state_reads_as_sat_unsafe():
    analysis = _build_symbolic_post_state_analysis("with_locread")

    assert analysis.has_symbolic_post_state_reads() is True
    assert "symbolic_post_state_reads" in analysis.get_decisive_sat_unsafety_reasons()


def test_function_return_analysis_treats_lowerable_post_state_reads_as_sat_safe():
    params = [
        _param("trace", index=0, size=8, data_type="int *"),
        _param("delta", index=1, size=4, data_type="int"),
    ]
    trace = Expression.parameter("trace", 0, size=8)
    delta = Expression.parameter("delta", 1, size=4)
    location = CanonicalLocation(
        base_ref=LocationBaseRef.parameter("trace", index=0),
        offset=0,
        size=4,
    )
    analysis = FunctionReturnAnalysis(
        function_name="lowerable",
        entry_point="0x1000",
        parameters=params,
        returns=[
            ReturnInfo(
                address="0x1000",
                value=post_state_read_expression_for_location(
                    location,
                    params,
                    symbolic=True,
                ),
                conditions=[],
            )
        ],
        return_type="int",
        effect_summary=EffectSummary(
            parameter_names=["trace", "delta"],
            effects=[
                StoreEffect(
                    location=location,
                    value=Expression.binary_op("INT_ADD", Expression.memory(trace, size=4), delta),
                    conditions=[],
                    order_key=1,
                )
            ],
        ),
    )

    assert analysis.has_symbolic_post_state_reads() is False
    assert "symbolic_post_state_reads" not in analysis.get_decisive_sat_unsafety_reasons()


def test_function_return_analysis_marks_effect_sensitive_raw_memory_reads_as_sat_unsafe():
    params = [_param("trace", index=0, size=8, data_type="int *")]
    trace = Expression.parameter("trace", 0, size=8)
    field = Expression.binary_op("INT_ADD", trace, Expression.constant(4, 8))
    location = CanonicalLocation(
        base_ref=LocationBaseRef.parameter("trace", index=0),
        offset=4,
        size=4,
    )
    analysis = FunctionReturnAnalysis(
        function_name="raw_read_after_effect",
        entry_point="0x1000",
        parameters=params,
        returns=[
            ReturnInfo(
                address="0x1000",
                value=Expression.memory(field, size=4),
                conditions=[],
            )
        ],
        return_type="int",
        effect_summary=EffectSummary(
            parameter_names=["trace"],
            effects=[
                StoreEffect(
                    location=location,
                    value=Expression.constant(1, 4),
                    conditions=[],
                    order_key=1,
                )
            ],
        ),
    )

    assert analysis.has_effect_sensitive_raw_memory_reads() is True
    assert "effect_sensitive_raw_memory_reads" in analysis.get_decisive_sat_unsafety_reasons()


def test_function_return_analysis_ignores_effect_sensitive_raw_reads_under_incompatible_guards():
    params = [
        _param("trace", index=0, size=8, data_type="int *"),
        _param("flag", index=1, size=4, data_type="int"),
    ]
    trace = Expression.parameter("trace", 0, size=8)
    flag = Expression.parameter("flag", 1, size=4)
    field = Expression.binary_op("INT_ADD", trace, Expression.constant(4, 8))
    location = CanonicalLocation(
        base_ref=LocationBaseRef.parameter("trace", index=0),
        offset=4,
        size=4,
    )
    analysis = FunctionReturnAnalysis(
        function_name="guarded_raw_read_after_effect",
        entry_point="0x1000",
        parameters=params,
        returns=[
            ReturnInfo(
                address="0x1000",
                value=Expression.memory(field, size=4),
                conditions=[_eq(flag, _const(0))],
            )
        ],
        return_type="int",
        effect_summary=EffectSummary(
            parameter_names=["trace", "flag"],
            effects=[
                StoreEffect(
                    location=location,
                    value=Expression.constant(1, 4),
                    conditions=[_ne(flag, _const(0))],
                    order_key=1,
                )
            ],
        ),
    )

    assert analysis.has_effect_sensitive_raw_memory_reads() is False
    assert "effect_sensitive_raw_memory_reads" not in analysis.get_decisive_sat_unsafety_reasons()


def test_function_return_analysis_checks_raw_read_alias_under_effect_guard():
    params = [
        _param("p", index=0, size=8, data_type="int *"),
        _param("q", index=1, size=8, data_type="int *"),
    ]
    p = Expression.parameter("p", 0, size=8)
    q = Expression.parameter("q", 1, size=8)
    analysis = FunctionReturnAnalysis(
        function_name="guarded_alias_raw_read_after_effect",
        entry_point="0x1000",
        parameters=params,
        returns=[
            ReturnInfo(
                address="0x1000",
                value=Expression.memory(q, size=4),
                conditions=[],
            )
        ],
        return_type="int",
        effect_summary=EffectSummary(
            parameter_names=["p", "q"],
            effects=[
                StoreEffect(
                    location=CanonicalLocation(
                        base_ref=LocationBaseRef.parameter("p", index=0),
                        offset=0,
                        size=4,
                    ),
                    value=Expression.constant(1, 4),
                    conditions=[_eq(p, q)],
                    order_key=1,
                )
            ],
        ),
    )

    assert analysis.has_effect_sensitive_raw_memory_reads() is True
    assert "effect_sensitive_raw_memory_reads" in analysis.get_decisive_sat_unsafety_reasons()


def test_function_return_analysis_scans_raw_sibling_after_lowerable_post_state_read():
    params = [
        _param("trace", index=0, size=8, data_type="int *"),
        _param("flag", index=1, size=4, data_type="int"),
    ]
    trace = Expression.parameter("trace", 0, size=8)
    flag = Expression.parameter("flag", 1, size=4)
    total_location = CanonicalLocation(
        base_ref=LocationBaseRef.parameter("trace", index=0),
        offset=0,
        size=4,
    )
    count_location = CanonicalLocation(
        base_ref=LocationBaseRef.parameter("trace", index=0),
        offset=4,
        size=4,
    )
    count_addr = Expression.binary_op("INT_ADD", trace, Expression.constant(4, 8))
    analysis = FunctionReturnAnalysis(
        function_name="mixed_post_state_and_raw_read",
        entry_point="0x1000",
        parameters=params,
        returns=[
            ReturnInfo(
                address="0x1000",
                value=Expression.binary_op(
                    "INT_ADD",
                    post_state_read_expression_for_location(
                        total_location,
                        params,
                        symbolic=True,
                    ),
                    Expression.memory(count_addr, size=4),
                ),
                conditions=[],
            )
        ],
        return_type="int",
        effect_summary=EffectSummary(
            parameter_names=["trace"],
            effects=[
                StoreEffect(
                    location=total_location,
                    value=Expression.constant(7, 4),
                    conditions=[],
                    order_key=1,
                ),
                StoreEffect(
                    location=count_location,
                    value=Expression.constant(9, 4),
                    conditions=[_ne(flag, _const(0))],
                    order_key=2,
                ),
            ],
        ),
    )

    assert analysis.has_symbolic_post_state_reads() is False
    assert analysis.has_effect_sensitive_raw_memory_reads() is True
    assert "effect_sensitive_raw_memory_reads" in analysis.get_decisive_sat_unsafety_reasons()


def test_function_return_analysis_blocks_equivalence_when_effect_summary_is_unsupported():
    analysis = FunctionReturnAnalysis(
        function_name="unsupported_effect_summary",
        entry_point="0x1000",
        parameters=[],
        returns=[ReturnInfo(address="0x1000", value=_const(0), conditions=[])],
        return_type="int",
        effect_summary=EffectSummary(
            parameter_names=[],
            effects=[],
            has_unsupported_call=True,
        ),
    )

    assert "unsupported_call_effect_summary" in analysis.get_decisive_sat_unsafety_reasons()
    assert "unsupported_call_effect_summary" in analysis.get_equivalence_blocking_unsafety_reasons()


def test_pairwise_strategy_downgrades_sat_when_analysis_retains_symbolic_post_state_reads(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = {
        "header_lines": [],
        "params1": [],
        "params2": [],
        "extra_vars1": [],
        "extra_vars2": [],
        "constrained_fragments": [],
        "return_size1": 32,
        "return_size2": 32,
    }
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)

    analysis1 = _build_symbolic_post_state_analysis("f1")
    analysis2 = FunctionReturnAnalysis(
        function_name="f2",
        entry_point="0x2000",
        parameters=[_param("trace", index=0, size=8, data_type="int *")],
        returns=[ReturnInfo(address="0x2000", value=_const(0), conditions=[])],
        return_type="int",
    )

    trace = Expression.parameter("trace", 0, size=8)
    symbolic_case = ReturnCase(
        index=0,
        conditions=[],
        value_expr=post_state_read_expression_for_location(
            CanonicalLocation("trace", 0, 4),
            analysis1.parameters,
            symbolic=True,
        ),
        return_info=analysis1.returns[0],
        return_type="int",
        parameters=analysis1.parameters,
    )
    const_case = ReturnCase(
        index=0,
        conditions=[],
        value_expr=_const(0),
        return_info=analysis2.returns[0],
        return_type="int",
        parameters=analysis2.parameters,
    )

    monkeypatch.setattr(
        strategy,
        "_extract_return_cases",
        lambda analysis: [symbolic_case] if analysis.function_name == "f1" else [const_case],
    )
    monkeypatch.setattr(strategy, "_prune_unreachable_cases", lambda cases, *_args, **_kwargs: cases)
    monkeypatch.setattr(strategy, "_cases_are_contradictory", lambda *_args, **_kwargs: False)
    monkeypatch.setattr(strategy, "_case_contains_unresolved_expression", lambda *_args, **_kwargs: False)
    monkeypatch.setattr(
        "scripts.function_tracer_pcode.equivalence.strategies.pairwise.validate_counterexample_across_cases",
        lambda *_args, **_kwargs: (_ for _ in ()).throw(
            AssertionError("ambiguous-model validation should not run for SAT-unsafe analyses")
        ),
    )
    strategy._solve_query_twostage = Mock(
        return_value=QueryResult(
            is_equivalent=False,
            counterexample_raw={"trace_1": 1, "trace_2": 1},
        )
    )

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.sat_pairs == 0
    assert result.unknown_pairs == 1


def test_pairwise_unknown_result_preserves_recovery_action_status(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = {
        "header_lines": [],
        "params1": [],
        "params2": [],
        "extra_vars1": [],
        "extra_vars2": [],
        "constrained_fragments": [],
        "return_size1": 32,
        "return_size2": 64,
    }
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)

    analysis1 = FunctionReturnAnalysis(
        function_name="f1",
        entry_point="0x1000",
        parameters=[],
        returns=[ReturnInfo(address="0x1000", value=_const(1, size=4), conditions=[])],
        return_type="int",
    )
    analysis2 = FunctionReturnAnalysis(
        function_name="f2",
        entry_point="0x2000",
        parameters=[],
        returns=[ReturnInfo(address="0x2000", value=_const(1, size=8), conditions=[])],
        return_type="long",
    )
    case1 = ReturnCase(
        index=0,
        conditions=[],
        value_expr=analysis1.returns[0].value,
        return_info=analysis1.returns[0],
        return_type="int",
        parameters=[],
    )
    case2 = ReturnCase(
        index=0,
        conditions=[],
        value_expr=analysis2.returns[0].value,
        return_info=analysis2.returns[0],
        return_type="long",
        parameters=[],
    )
    target = ("return_width_bridge", ("pair", "(0,0)"), ("return_widths", 32, 64))
    query_result = QueryResult(is_equivalent=None)
    query_result.pair_stage = "return-width-mismatch"
    query_result.blocking_reason = UnknownReasonId.RETURN_WIDTH_BRIDGE_MISSING.value
    query_result.blocking_detail = "pairwise value inequality: return width mismatch (32 vs 64)"
    query_result.evidence_kind = "return_width_bridge_status"
    query_result.object_target_key = target
    query_result.object_evidence = ("return_width_bridge_status", ("status", "planned"))
    query_result.action_status = UnknownRecoveryActionStatus.PLANNED

    monkeypatch.setattr(
        strategy,
        "_extract_return_cases",
        lambda analysis: [case1] if analysis.function_name == "f1" else [case2],
    )
    monkeypatch.setattr(strategy, "_prune_unreachable_cases", lambda cases, *_args, **_kwargs: cases)
    monkeypatch.setattr(strategy, "_cases_are_contradictory", lambda *_args, **_kwargs: False)
    monkeypatch.setattr(strategy, "_case_contains_unresolved_expression", lambda *_args, **_kwargs: False)
    strategy._solve_query_twostage = Mock(return_value=query_result)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.unknown_pairs == 1
    assert len(result.unknown_reasons) == 1
    reason = result.unknown_reasons[0]
    assert reason.reason_id == UnknownReasonId.RETURN_WIDTH_BRIDGE_MISSING.value
    assert reason.action_status == UnknownRecoveryActionStatus.PLANNED.value
    assert reason.object_target_key == target
    assert reason.object_evidence == query_result.object_evidence


def test_monolithic_unsupported_intrinsic_is_unresolved_expression_not_strategy_exception():
    formula_builder = Mock()
    formula_builder.build_equivalence_formula_extended.side_effect = ValueError(
        "Unsupported intrinsic for SMT lowering: CALLOTHER"
    )
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = MonolithicStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = FunctionReturnAnalysis(
        function_name="left",
        entry_point="0x1000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1000", value=_const(1), conditions=[])],
        return_type="int",
    )
    analysis2 = FunctionReturnAnalysis(
        function_name="right",
        entry_point="0x2000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=_const(1), conditions=[])],
        return_type="int",
    )

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.unknown_reasons[0].reason_id == UnknownReasonId.UNRESOLVED_EXPRESSION.value
    assert result.unknown_reasons[0].evidence_refs == ("unsupported_intrinsic_smt_lowering",)
    solver_runner.run_parallel.assert_not_called()


def test_monolithic_strategy_downgrades_ambiguous_sat_counterexample_to_unknown():
    class _ValidationSolverRunner:
        def __init__(self):
            self.timeout = 5

        def run_parallel(self, _query: str):
            return ParallelResult(
                results=[
                    SolverResult(
                        "fake",
                        SolverStatus.SAT,
                        elapsed_time=0.01,
                        model={"x_1": 5, "x_2": 5},
                    )
                ]
            )

        def run_sequential(self, query: str):
            if "(assert (= (_ bv7 32) (_ bv7 32)))" in query:
                return ParallelResult(
                    results=[SolverResult("fake", SolverStatus.SAT, model={"x_1": 5, "x_2": 5})]
                )
            if "(assert (= x_1 (bvadd x_2 (_ bv1 32))))" in query:
                return ParallelResult(results=[SolverResult("fake", SolverStatus.UNSAT)])
            return ParallelResult(
                results=[SolverResult("fake", SolverStatus.SAT, model={"x_1": 5, "x_2": 5})]
            )

    x1 = Expression.parameter("x", 0, size=4)
    x2 = Expression.parameter("x", 0, size=4)
    cond1 = _eq(x1, _const(5))
    cond2 = _eq(x2, _const(5))

    analysis1 = FunctionReturnAnalysis(
        function_name="func1",
        entry_point="0x1",
        parameters=[_param("x")],
        returns=[
            ReturnInfo(address="0x1", value=x1, conditions=[]),
            ReturnInfo(address="0x2", value=_const(7), conditions=[cond1]),
        ],
        return_type="int",
    )
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x2",
        parameters=[_param("x")],
        returns=[
            ReturnInfo(
                address="0x3",
                value=Expression.binary_op("INT_ADD", x2, _const(1)),
                conditions=[],
            ),
            ReturnInfo(address="0x4", value=_const(7), conditions=[cond2]),
        ],
        return_type="int",
    )

    params1 = [ParameterInfo(original_name="x", smt_name="x_1", bit_width=32, index=0)]
    params2 = [ParameterInfo(original_name="x", smt_name="x_2", bit_width=32, index=0)]
    formula_builder = Mock()
    formula_builder.build_equivalence_formula_extended.return_value = FormulaBuilderResult(
        formula="(set-logic QF_BV)\n(check-sat)",
        return_var1="return_1",
        return_var2="return_2",
        constrained_fragments=[],
        extra_vars1=[],
        extra_vars2=[],
        param_fragment_constrained=[],
    )
    formula_builder.build_base_context.return_value = {
        "header_lines": [
            "(declare-const x_1 (_ BitVec 32))",
            "(declare-const x_2 (_ BitVec 32))",
            "(assert (= x_1 x_2))",
        ],
        "params1": params1,
        "params2": params2,
        "extra_vars1": [],
        "extra_vars2": [],
        "constrained_fragments": [],
        "return_size1": 32,
        "return_size2": 32,
    }

    strategy = MonolithicStrategy(formula_builder, _ValidationSolverRunner(), debug=False)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.counterexample_raw is None


def test_monolithic_same_function_sat_requires_counterexample_replay(monkeypatch):
    class _SatSolverRunner:
        def __init__(self):
            self.timeout = 5

        def run_parallel(self, _query: str):
            return ParallelResult(
                results=[
                    SolverResult(
                        "fake",
                        SolverStatus.SAT,
                        elapsed_time=0.01,
                        model={"x_1": 0, "x_2": 0},
                    )
                ]
            )

    formula_builder = Mock()
    formula_builder.build_equivalence_formula_extended.return_value = FormulaBuilderResult(
        formula="(set-logic QF_BV)\n(check-sat)",
        return_var1="return_1",
        return_var2="return_2",
        constrained_fragments=[],
        extra_vars1=[],
        extra_vars2=[],
        param_fragment_constrained=[],
    )
    analysis1 = FunctionReturnAnalysis(
        function_name="same_func",
        entry_point="0x1000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1000", value=_const(1), conditions=[])],
        return_type="int",
    )
    analysis2 = FunctionReturnAnalysis(
        function_name="same_func",
        entry_point="0x2000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=_const(2), conditions=[])],
        return_type="int",
    )
    strategy = MonolithicStrategy(formula_builder, _SatSolverRunner(), debug=False)
    monkeypatch.setattr(strategy, "_collect_monolithic_return_coverage_unsafety_reasons", lambda *_args: [])

    def _validated_counterexample(*_args):
        strategy._last_counterexample_replay_fixed_model_assertion_count = 2
        return True

    monkeypatch.setattr(strategy, "_counterexample_is_decisive_across_case_split", _validated_counterexample)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.counterexample_raw is None
    reason = result.unknown_reasons[0]
    assert reason.reason_id == UnknownReasonId.SAT_UNSAFETY.value
    assert reason.evidence_refs == ("counterexample_replay_missing",)
    assert not any(
        evidence.get("proof_source") == "monolithic_global_counterexample_validation"
        for evidence in analysis1.completed_recovery_proof_evidence
    )


def test_monolithic_same_function_sat_accepts_prior_completed_counterexample_replay(monkeypatch):
    class _SatSolverRunner:
        def __init__(self):
            self.timeout = 5

        def run_parallel(self, _query: str):
            return ParallelResult(
                results=[
                    SolverResult(
                        "fake",
                        SolverStatus.SAT,
                        elapsed_time=0.01,
                        model={"x_1": 0, "x_2": 0},
                    )
                ]
            )

    formula_builder = Mock()
    formula_builder.build_equivalence_formula_extended.return_value = FormulaBuilderResult(
        formula="(set-logic QF_BV)\n(check-sat)",
        return_var1="return_1",
        return_var2="return_2",
        constrained_fragments=[],
        extra_vars1=[],
        extra_vars2=[],
        param_fragment_constrained=[],
    )
    analysis1 = FunctionReturnAnalysis(
        function_name="same_func",
        entry_point="0x1000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1000", value=_const(1), conditions=[])],
        return_type="int",
    )
    analysis2 = FunctionReturnAnalysis(
        function_name="same_func",
        entry_point="0x2000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=_const(2), conditions=[])],
        return_type="int",
    )
    strategy = MonolithicStrategy(formula_builder, _SatSolverRunner(), debug=False)
    monkeypatch.setattr(strategy, "_collect_monolithic_return_coverage_unsafety_reasons", lambda *_args: [])
    monkeypatch.setattr(strategy, "_counterexample_is_decisive_across_case_split", lambda *_args: True)
    pending_reason = strategy._make_sat_unsafety_unknown_reason(
        ("counterexample_replay_missing",),
        analysis1,
        analysis2,
        case1=None,
        case2=None,
        pair_id="monolithic",
        stage="S_MONOLITHIC_FALLBACK",
    )
    action = build_unknown_recovery_actions([pending_reason])[0]
    analysis1.completed_recovery_proof_evidence = (
        _sat_unsafety_resolution_evidence(action),
    )

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is False
    assert result.counterexample_raw == {"x_1": 0, "x_2": 0}
    assert result.unknown_reasons == []


def test_monolithic_same_function_sat_with_unfixed_model_is_unknown():
    class _ReturnOnlySatSolverRunner:
        def __init__(self):
            self.timeout = 5

        def run_parallel(self, _query: str):
            return ParallelResult(
                results=[
                    SolverResult(
                        "fake",
                        SolverStatus.SAT,
                        elapsed_time=0.01,
                        model={"return_1": 1, "return_2": 2},
                    )
                ]
            )

        def run_sequential(self, _query: str, timeout=None):
            raise AssertionError("unfixed model should be rejected before replay queries")

    formula_builder = Mock()
    formula_builder.build_equivalence_formula_extended.return_value = FormulaBuilderResult(
        formula="(set-logic QF_BV)\n(check-sat)",
        return_var1="return_1",
        return_var2="return_2",
        constrained_fragments=[],
        extra_vars1=[],
        extra_vars2=[],
        param_fragment_constrained=[],
    )
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    analysis1 = FunctionReturnAnalysis(
        function_name="same_func",
        entry_point="0x1000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1000", value=_const(1), conditions=[])],
        return_type="int",
    )
    analysis2 = FunctionReturnAnalysis(
        function_name="same_func",
        entry_point="0x2000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=_const(2), conditions=[])],
        return_type="int",
    )
    strategy = MonolithicStrategy(formula_builder, _ReturnOnlySatSolverRunner(), debug=False)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.counterexample_raw is None
    reason = result.unknown_reasons[0]
    assert reason.reason_id == UnknownReasonId.SAT_COUNTEREXAMPLE_AMBIGUOUS.value
    assert reason.recovery_proof_kind == UnknownRecoveryProofKind.SAT_UNSAFETY_RESOLUTION.value
    assert reason.proof_stage == "sat_counterexample_safety"
    assert reason.action_status == UnknownRecoveryActionStatus.PENDING_PROOF.value
    assert reason.evidence_kind == "case_partition_replay"
    action = build_unknown_recovery_actions([reason])[0]
    assert action.reason_id == UnknownReasonId.SAT_COUNTEREXAMPLE_AMBIGUOUS.value
    assert action.proof_kind == UnknownRecoveryProofKind.SAT_UNSAFETY_RESOLUTION.value
    assert action.proof_stage == "sat_counterexample_safety"
    assert action.status == UnknownRecoveryActionStatus.PENDING_PROOF.value
    assert analysis1.completed_recovery_proof_evidence == ()


def test_sat_counterexample_ambiguous_reason_has_object_proof_action():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    analysis1 = FunctionReturnAnalysis(
        function_name="func1",
        entry_point="0x1000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1000", value=_const(1), conditions=[])],
        return_type="int",
    )
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x2000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=_const(2), conditions=[])],
        return_type="int",
    )
    case1 = ReturnCase(
        index=0,
        conditions=[],
        value_expr=analysis1.returns[0].value,
        return_info=analysis1.returns[0],
        return_type="int",
        parameters=analysis1.parameters,
    )
    case2 = ReturnCase(
        index=0,
        conditions=[],
        value_expr=analysis2.returns[0].value,
        return_info=analysis2.returns[0],
        return_type="int",
        parameters=analysis2.parameters,
    )

    reason = strategy._make_sat_counterexample_ambiguous_unknown_reason(
        ("with-ineq",),
        analysis1,
        analysis2,
        case1=case1,
        case2=case2,
        pair_id="(0,0)",
        stage="S_PAIRWISE",
    )
    action = build_unknown_recovery_actions([reason])[0]

    assert reason.reason_id == UnknownReasonId.SAT_COUNTEREXAMPLE_AMBIGUOUS.value
    assert reason.decision_effect == "blocks_disequivalence"
    assert reason.reason_scope == "pair"
    assert reason.recovery_proof_kind == UnknownRecoveryProofKind.SAT_UNSAFETY_RESOLUTION.value
    assert reason.proof_stage == "sat_counterexample_safety"
    assert reason.evidence_kind == "case_partition_replay"
    assert reason.object_target_key[0] == "sat_counterexample_ambiguous"
    assert reason.object_evidence["object_derived"] is True
    assert reason.object_evidence["ambiguity_evidence_refs"] == ("with-ineq",)
    assert action.count_kind == "proof_action"
    assert action.reason_id == UnknownReasonId.SAT_COUNTEREXAMPLE_AMBIGUOUS.value
    assert action.proof_kind == UnknownRecoveryProofKind.SAT_UNSAFETY_RESOLUTION.value
    assert action.proof_stage == "sat_counterexample_safety"
    assert action.evidence_kind == "case_partition_replay"
    assert action.status == UnknownRecoveryActionStatus.PENDING_PROOF.value
    assert action.proof_obligation_id == build_proof_obligation_id(
        UnknownReasonId.SAT_COUNTEREXAMPLE_AMBIGUOUS.value,
        "sat_counterexample_safety",
        UnknownRecoveryProofKind.SAT_UNSAFETY_RESOLUTION.value,
        "case_partition_replay",
        reason.object_target_key,
    )


def test_pairwise_strategy_downgrades_sat_when_return_cases_leave_coverage_gap(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = {
        "header_lines": [
            "(declare-const x_1 (_ BitVec 32))",
            "(declare-const x_2 (_ BitVec 32))",
            "(assert (= x_1 x_2))",
        ],
        "params1": [ParameterInfo(original_name="x", smt_name="x_1", bit_width=32, index=0)],
        "params2": [ParameterInfo(original_name="x", smt_name="x_2", bit_width=32, index=0)],
        "extra_vars1": [],
        "extra_vars2": [],
        "constrained_fragments": [],
        "return_size1": 32,
        "return_size2": 32,
    }
    solver_runner = Mock()
    solver_runner.timeout = 5
    solver_runner.run_sequential.return_value = ParallelResult(
        results=[SolverResult("fake", SolverStatus.SAT, model={"x_1": 7, "x_2": 7})]
    )
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)

    x = Expression.parameter("x", 0, size=4)
    analysis1 = FunctionReturnAnalysis(
        function_name="func1",
        entry_point="0x1",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1", value=_const(1), conditions=[_eq(x, _const(0))])],
        return_type="int",
    )
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x2",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2", value=_const(2), conditions=[])],
        return_type="int",
    )

    case1 = ReturnCase(
        index=0,
        conditions=[_eq(Expression.parameter("x", 0, size=4), _const(0))],
        value_expr=_const(1),
        return_info=analysis1.returns[0],
        return_type="int",
        parameters=analysis1.parameters,
    )
    case2 = ReturnCase(
        index=0,
        conditions=[],
        value_expr=_const(2),
        return_info=analysis2.returns[0],
        return_type="int",
        parameters=analysis2.parameters,
    )

    monkeypatch.setattr(
        strategy,
        "_extract_return_cases",
        lambda analysis: [case1] if analysis.function_name == "func1" else [case2],
    )
    monkeypatch.setattr(strategy, "_prune_unreachable_cases", lambda cases, *_args, **_kwargs: cases)
    monkeypatch.setattr(strategy, "_cases_are_contradictory", lambda *_args, **_kwargs: False)
    monkeypatch.setattr(strategy, "_case_contains_unresolved_expression", lambda *_args, **_kwargs: False)
    monkeypatch.setattr(
        "scripts.function_tracer_pcode.equivalence.strategies.pairwise.validate_counterexample_across_cases",
        lambda *_args, **_kwargs: (_ for _ in ()).throw(
            AssertionError("pairwise counterexample validation should not run when coverage is incomplete")
        ),
    )
    strategy._solve_query_twostage = Mock(
        return_value=QueryResult(
            is_equivalent=False,
            counterexample_raw={"x_1": 7, "x_2": 7},
        )
    )

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.sat_pairs == 0
    assert result.unknown_pairs == 1
    assert "return_case_coverage_gap" in analysis1.analysis_notes
    assert analysis2.analysis_notes == []


def test_pairwise_strategy_does_not_prove_equivalent_with_return_coverage_gap(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = {
        "header_lines": [
            "(declare-const x_1 (_ BitVec 32))",
            "(declare-const x_2 (_ BitVec 32))",
            "(assert (= x_1 x_2))",
        ],
        "params1": [ParameterInfo(original_name="x", smt_name="x_1", bit_width=32, index=0)],
        "params2": [ParameterInfo(original_name="x", smt_name="x_2", bit_width=32, index=0)],
        "extra_vars1": [],
        "extra_vars2": [],
        "constrained_fragments": [],
        "return_size1": 32,
        "return_size2": 32,
    }
    solver_runner = Mock()
    solver_runner.timeout = 5
    solver_runner.run_sequential.return_value = ParallelResult(
        results=[SolverResult("fake", SolverStatus.SAT, model={"x_1": 7, "x_2": 7})]
    )
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)

    x = Expression.parameter("x", 0, size=4)
    analysis1 = FunctionReturnAnalysis(
        function_name="func1",
        entry_point="0x1",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1", value=_const(1), conditions=[_eq(x, _const(0))])],
        return_type="int",
    )
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x2",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2", value=_const(1), conditions=[])],
        return_type="int",
    )

    case1 = ReturnCase(
        index=0,
        conditions=[_eq(Expression.parameter("x", 0, size=4), _const(0))],
        value_expr=_const(1),
        return_info=analysis1.returns[0],
        return_type="int",
        parameters=analysis1.parameters,
    )
    case2 = ReturnCase(
        index=0,
        conditions=[],
        value_expr=_const(1),
        return_info=analysis2.returns[0],
        return_type="int",
        parameters=analysis2.parameters,
    )

    monkeypatch.setattr(
        strategy,
        "_extract_return_cases",
        lambda analysis: [case1] if analysis.function_name == "func1" else [case2],
    )
    monkeypatch.setattr(strategy, "_prune_unreachable_cases", lambda cases, *_args, **_kwargs: cases)
    monkeypatch.setattr(strategy, "_cases_are_contradictory", lambda *_args, **_kwargs: False)
    monkeypatch.setattr(strategy, "_case_contains_unresolved_expression", lambda *_args, **_kwargs: False)
    strategy._solve_query_twostage = Mock(return_value=QueryResult(is_equivalent=True))

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.unsat_pairs == 1
    assert result.unknown_pairs == 0
    assert "return_case_coverage_gap" in analysis1.analysis_notes


def test_pairwise_global_blocker_dominates_pair_local_unresolved_expression(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1, analysis2 = _return_coverage_gap_analyses()
    _patch_pairwise_return_coverage_gap_case(monkeypatch, strategy, analysis1, analysis2)
    monkeypatch.setattr(strategy, "_case_contains_unresolved_expression", lambda *_args, **_kwargs: True)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.unknown_pairs == 1
    assert {reason.reason_id for reason in result.unknown_reasons} == {
        UnknownReasonId.RETURN_COVERAGE_GAP.value,
    }
    assert all(
        reason.reason_id != UnknownReasonId.UNRESOLVED_EXPRESSION.value
        for reason in result.unknown_reasons
    )
    assert "return_case_coverage_gap" in analysis1.analysis_notes


def test_pairwise_equivalence_blocker_dominates_pair_local_unresolved_expression(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_unsupported_call_effect()
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x2000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=_const(1), conditions=[])],
        return_type="int",
    )
    case1 = ReturnCase(
        index=0,
        conditions=[],
        value_expr=analysis1.returns[0].value,
        return_info=analysis1.returns[0],
        return_type=analysis1.return_type or "int",
        parameters=analysis1.parameters,
    )
    case2 = ReturnCase(
        index=0,
        conditions=[],
        value_expr=analysis2.returns[0].value,
        return_info=analysis2.returns[0],
        return_type=analysis2.return_type or "int",
        parameters=analysis2.parameters,
    )
    monkeypatch.setattr(
        strategy,
        "_extract_return_cases",
        lambda analysis: [case1] if analysis.function_name == analysis1.function_name else [case2],
    )
    monkeypatch.setattr(strategy, "_prune_unreachable_cases", lambda cases, *_args, **_kwargs: cases)
    monkeypatch.setattr(strategy, "_cases_are_contradictory", lambda *_args, **_kwargs: False)
    monkeypatch.setattr(strategy, "_case_contains_unresolved_expression", lambda *_args, **_kwargs: True)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.unknown_pairs == 1
    assert {reason.reason_id for reason in result.unknown_reasons} == {
        UnknownReasonId.EQUIVALENCE_BLOCKING_UNSAFETY.value,
    }
    assert all(
        reason.reason_id != UnknownReasonId.UNRESOLVED_EXPRESSION.value
        for reason in result.unknown_reasons
    )


def test_pairwise_return_coverage_covered_side_emits_completed_proof_evidence(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    solver_runner.run_sequential.return_value = ParallelResult(
        results=[SolverResult("fake", SolverStatus.SAT, model={"x_1": 7, "x_2": 7})]
    )
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1, analysis2 = _return_coverage_gap_analyses()
    _patch_pairwise_return_coverage_gap_case(monkeypatch, strategy, analysis1, analysis2)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert analysis1.completed_recovery_proof_evidence == ()
    evidence = analysis2.completed_recovery_proof_evidence
    assert {item["proof_stage"] for item in evidence} == {
        "return_partition_extraction",
        "return_guard_coverage",
    }
    assert all(item["object_derived"] is True for item in evidence)
    assert all(item["coverage_status"] == "covered" for item in evidence)

    completed_reason = strategy._make_blocking_unsafety_unknown_reason(
        "function2:return_coverage_gap",
        analysis1,
        analysis2,
        stage="S_PAIRWISE",
    )
    expected_actions = build_unknown_recovery_actions([completed_reason])
    assert {
        tuple(item["proof_obligation_id"])
        for item in evidence
    } == {action.proof_obligation_id for action in expected_actions}
    assert PairwiseStrategy._completed_recovery_proof_ids(analysis2) == tuple(
        action.proof_obligation_id for action in expected_actions
    )

    strategy.check(analysis1, analysis2)

    assert len(analysis2.completed_recovery_proof_evidence) == 2


def test_pairwise_completed_recovery_proofs_can_be_disabled(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    solver_runner.run_sequential.return_value = ParallelResult(
        results=[SolverResult("fake", SolverStatus.SAT, model={"x_1": 7, "x_2": 7})]
    )
    strategy = PairwiseStrategy(
        formula_builder,
        solver_runner,
        debug=False,
        enable_completed_recovery_proofs=False,
    )
    analysis1, analysis2 = _return_coverage_gap_analyses()
    _patch_pairwise_return_coverage_gap_case(monkeypatch, strategy, analysis1, analysis2)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert [reason.reason_id for reason in result.unknown_reasons] == [
        UnknownReasonId.RETURN_COVERAGE_GAP.value,
    ]
    assert {reason.action_status for reason in result.unknown_reasons} == {
        UnknownRecoveryActionStatus.PENDING_PROOF.value
    }
    assert analysis1.completed_recovery_proof_evidence == ()
    assert analysis2.completed_recovery_proof_evidence == ()


def test_pairwise_disabled_completed_proofs_do_not_create_new_return_gap_without_active_blocker(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(
        formula_builder,
        solver_runner,
        debug=False,
        enable_completed_recovery_proofs=False,
    )
    analysis1, analysis2 = _return_coverage_gap_analyses()
    analysis1.analysis_notes = []
    analysis2.analysis_notes = []
    monkeypatch.setattr(
        strategy,
        "_check_return_case_coverage_gap",
        lambda *_args, **_kwargs: ReturnCoverageCheckResult("covered"),
    )

    reasons = strategy._collect_return_coverage_unsafety_reasons(
        _base_context_for_single_int_param(),
        [],
        [],
        lambda value: value,
        lambda value: value,
        analysis1,
        analysis2,
    )

    assert reasons == []
    assert analysis1.completed_recovery_proof_evidence == ()
    assert analysis2.completed_recovery_proof_evidence == ()


def test_pairwise_disabled_completed_proofs_ignore_stale_summary_dependency_note(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(
        formula_builder,
        solver_runner,
        debug=False,
        enable_completed_recovery_proofs=False,
    )
    analysis1, analysis2 = _return_coverage_gap_analyses()
    analysis1.analysis_notes = []
    analysis2.analysis_notes = ["state_transition_loop_summary"]
    monkeypatch.setattr(
        strategy,
        "_check_return_case_coverage_gap",
        lambda *_args, **_kwargs: ReturnCoverageCheckResult("covered"),
    )

    reasons = strategy._collect_return_coverage_unsafety_reasons(
        _base_context_for_single_int_param(),
        [],
        [],
        lambda value: value,
        lambda value: value,
        analysis1,
        analysis2,
    )

    assert reasons == []
    assert analysis1.completed_recovery_proof_evidence == ()
    assert analysis2.completed_recovery_proof_evidence == ()


def test_pairwise_collect_return_coverage_reason_uses_current_coverage_check_when_notes_are_stale(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(
        formula_builder,
        solver_runner,
        debug=False,
        enable_completed_recovery_proofs=False,
    )
    analysis1, analysis2 = _return_coverage_gap_analyses()
    analysis1.analysis_notes = ["return_case_coverage_inconclusive"]
    monkeypatch.setattr(
        strategy,
        "_check_return_case_coverage_gap",
        lambda *_args, **_kwargs: ReturnCoverageCheckResult("covered"),
    )

    reasons = strategy._collect_return_coverage_unsafety_reasons(
        _base_context_for_single_int_param(),
        [],
        [],
        lambda value: value,
        lambda value: value,
        analysis1,
        analysis2,
    )

    assert reasons == []


def test_pairwise_disabled_completed_proofs_do_not_block_switch_or_control_region_recovery(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(
        formula_builder,
        solver_runner,
        debug=False,
        enable_completed_recovery_proofs=False,
    )
    analysis1, analysis2 = _return_coverage_gap_analyses()
    analysis1.analysis_notes = []
    analysis2.analysis_notes = [
        "switch_return_recovery",
        "control_region_return_recovery",
    ]
    monkeypatch.setattr(
        strategy,
        "_check_return_case_coverage_gap",
        lambda *_args, **_kwargs: ReturnCoverageCheckResult("covered"),
    )

    reasons = strategy._collect_return_coverage_unsafety_reasons(
        _base_context_for_single_int_param(),
        [],
        [],
        lambda value: value,
        lambda value: value,
        analysis1,
        analysis2,
    )

    assert reasons == []
    assert analysis1.completed_recovery_proof_evidence == ()
    assert analysis2.completed_recovery_proof_evidence == ()


def test_pairwise_return_coverage_gap_requires_all_completed_proof_ids(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    solver_runner.run_sequential.return_value = ParallelResult(
        results=[SolverResult("fake", SolverStatus.SAT, model={"x_1": 7, "x_2": 7})]
    )
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1, analysis2 = _return_coverage_gap_analyses()
    analysis1.get_decisive_sat_unsafety_reasons = lambda: ["return_coverage_gap"]
    pending_reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:return_coverage_gap",
        analysis1,
        analysis2,
        stage="S_PAIRWISE",
    )
    actions = build_unknown_recovery_actions([pending_reason])
    analysis1.completed_recovery_proof_evidence = (
        _return_coverage_completion_evidence(actions[0]),
    )
    _patch_pairwise_return_coverage_gap_case(monkeypatch, strategy, analysis1, analysis2)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.unknown_reasons[0].reason_id == UnknownReasonId.RETURN_COVERAGE_GAP.value
    assert result.unknown_reasons[0].action_status == UnknownRecoveryActionStatus.PENDING_PROOF.value


def test_pairwise_return_coverage_gap_completed_proofs_allow_equivalent(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    solver_runner.run_sequential.return_value = ParallelResult(
        results=[SolverResult("fake", SolverStatus.SAT, model={"x_1": 7, "x_2": 7})]
    )
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1, analysis2 = _return_coverage_gap_analyses()
    analysis1.get_decisive_sat_unsafety_reasons = lambda: ["return_coverage_gap"]
    pending_reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:return_coverage_gap",
        analysis1,
        analysis2,
        stage="S_PAIRWISE",
    )
    actions = build_unknown_recovery_actions([pending_reason])
    analysis1.completed_recovery_proof_evidence = tuple(
        _return_coverage_completion_evidence(action)
        for action in actions
    )
    _patch_pairwise_return_coverage_gap_case(monkeypatch, strategy, analysis1, analysis2)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is True
    assert result.unknown_reasons == []
    assert result.unsat_pairs == 1
    assert result.unknown_pairs == 0


def test_return_coverage_proof_content_requires_disjunction_and_normalized_guard():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    analysis1, analysis2 = _return_coverage_gap_analyses()
    pending_reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:return_coverage_gap",
        analysis1,
        analysis2,
        stage="S_PAIRWISE",
    )
    proof_stage_actions = build_unknown_recovery_actions([pending_reason])
    action = proof_stage_actions[0]
    evidence = _return_coverage_completion_evidence(action, reason_id=UnknownReasonId.RETURN_COVERAGE_GAP)
    assert strategy._return_coverage_proof_content_is_complete(
        evidence,
        UnknownReasonId.RETURN_COVERAGE_GAP,
    )

    invalid_empty_cases = dict(evidence)
    invalid_empty_cases["proof_content"] = {
        "case_guard_disjunction": {
            "status": "complete",
            "query_cases": ("(true)",),
        },
        "normalized_guard_formula": {
            "status": "complete",
            "query": "(or true)",
        },
    }
    assert not strategy._return_coverage_proof_content_is_complete(
        invalid_empty_cases,
        UnknownReasonId.RETURN_COVERAGE_GAP,
    )

    valid_guard_evidence = deepcopy(evidence)
    assert strategy._return_coverage_proof_content_is_complete(
        valid_guard_evidence,
        UnknownReasonId.RETURN_COVERAGE_GAP,
    )


def test_return_coverage_proof_completion_rejects_empty_case_guard_disjunction(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    solver_runner.run_sequential.return_value = ParallelResult(
        results=[SolverResult("fake", SolverStatus.SAT, model={"x_1": 7, "x_2": 7})
        ]
    )
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1, analysis2 = _return_coverage_gap_analyses()
    analysis1.get_decisive_sat_unsafety_reasons = lambda: ["return_coverage_gap"]
    pending_reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:return_coverage_gap",
        analysis1,
        analysis2,
        stage="S_PAIRWISE",
    )
    actions = build_unknown_recovery_actions([pending_reason])
    analysis1.completed_recovery_proof_evidence = (
        _return_coverage_completion_evidence(
            actions[0],
            reason_id=UnknownReasonId.RETURN_COVERAGE_GAP,
            proof_content={
                "case_guard_disjunction": {
                    "status": "complete",
                    "query_cases": (),
                },
                "normalized_guard_formula": {
                    "status": "complete",
                    "query": "(or true)",
                },
            },
        ),
    )
    _patch_pairwise_return_coverage_gap_case(monkeypatch, strategy, analysis1, analysis2)
    _patch_pairwise_single_unsat_case(monkeypatch, strategy, analysis1, analysis2)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.unknown_reasons
    assert result.unknown_reasons[0].reason_id == UnknownReasonId.RETURN_COVERAGE_GAP.value


def test_pairwise_return_coverage_gap_wrong_completed_proof_id_does_not_recover(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    solver_runner.run_sequential.return_value = ParallelResult(
        results=[SolverResult("fake", SolverStatus.SAT, model={"x_1": 7, "x_2": 7})]
    )
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1, analysis2 = _return_coverage_gap_analyses()
    pending_reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:return_coverage_gap",
        analysis1,
        analysis2,
        stage="S_PAIRWISE",
    )
    actions = build_unknown_recovery_actions([pending_reason])
    wrong_id = build_proof_obligation_id(
        UnknownReasonId.RETURN_COVERAGE_GAP,
        actions[0].proof_stage,
        UnknownRecoveryProofKind.RETURN_COVERAGE_COMPLETION,
        actions[0].evidence_kind,
        ("return_coverage", "different-target"),
    )
    analysis1.completed_recovery_proof_evidence = (
        _return_coverage_completion_evidence(actions[0], proof_obligation_id=wrong_id),
        _return_coverage_completion_evidence(actions[1]),
    )
    _patch_pairwise_return_coverage_gap_case(monkeypatch, strategy, analysis1, analysis2)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.unknown_reasons[0].reason_id == UnknownReasonId.RETURN_COVERAGE_GAP.value


def test_pairwise_return_coverage_gap_missing_completed_proof_id_does_not_recover(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    solver_runner.run_sequential.return_value = ParallelResult(
        results=[SolverResult("fake", SolverStatus.SAT, model={"x_1": 7, "x_2": 7})]
    )
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1, analysis2 = _return_coverage_gap_analyses()
    pending_reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:return_coverage_gap",
        analysis1,
        analysis2,
        stage="S_PAIRWISE",
    )
    actions = build_unknown_recovery_actions([pending_reason])
    analysis1.completed_recovery_proof_evidence = tuple(
        _return_coverage_completion_evidence_without_proof_id(action)
        for action in actions
    )
    _patch_pairwise_return_coverage_gap_case(monkeypatch, strategy, analysis1, analysis2)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.unknown_reasons[0].reason_id == UnknownReasonId.RETURN_COVERAGE_GAP.value
    assert result.unknown_reasons[0].action_status == UnknownRecoveryActionStatus.PENDING_PROOF.value


def test_pairwise_return_coverage_inconclusive_unknown_does_not_complete_proof(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    solver_runner.run_sequential.return_value = ParallelResult(
        results=[SolverResult("fake", SolverStatus.SAT, model={"x_1": 7, "x_2": 7})]
    )
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1, analysis2 = _return_coverage_gap_analyses()
    for label, analysis in (("function1", analysis1), ("function2", analysis2)):
        blocking_reason = f"{label}:return_coverage_inconclusive"
        reason = strategy._make_blocking_unsafety_unknown_reason(
            blocking_reason,
            analysis1,
            analysis2,
            stage="S_PAIRWISE",
        )
        actions = build_unknown_recovery_actions([reason])
        analysis.completed_recovery_proof_evidence = tuple(
            _return_coverage_completion_evidence(
                action,
                reason_id=UnknownReasonId.RETURN_COVERAGE_INCONCLUSIVE,
            )
            for action in actions
        )
    monkeypatch.setattr(
        strategy,
        "_check_return_case_coverage_gap",
        lambda *_args, **_kwargs: ReturnCoverageCheckResult(
            status="inconclusive",
            reason_id=UnknownReasonId.RETURN_COVERAGE_INCONCLUSIVE,
        ),
    )
    _patch_pairwise_return_coverage_gap_case(monkeypatch, strategy, analysis1, analysis2)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert [reason.reason_id for reason in result.unknown_reasons] == [
        UnknownReasonId.RETURN_COVERAGE_INCONCLUSIVE.value,
        UnknownReasonId.RETURN_COVERAGE_INCONCLUSIVE.value,
    ]
    assert result.unsat_pairs == 1
    assert result.unknown_pairs == 0


def test_pairwise_return_coverage_inconclusive_query_unknown_records_recovery_proof(monkeypatch):
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    analysis1 = FunctionReturnAnalysis(
        function_name="func1",
        entry_point="0x1",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1", value=_const(1), conditions=[_eq(Expression.parameter("x", 0, size=4), _const(0))])],
        return_type="int",
    )
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x2",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2", value=_const(1), conditions=[])],
        return_type="int",
    )
    case1 = ReturnCase(
        index=0,
        conditions=[_eq(Expression.parameter("x", 0, size=4), _const(0))],
        value_expr=analysis1.returns[0].value,
        return_info=analysis1.returns[0],
        return_type=analysis1.return_type or "int",
        parameters=analysis1.parameters,
    )
    case2 = ReturnCase(
        index=0,
        conditions=[],
        value_expr=analysis2.returns[0].value,
        return_info=analysis2.returns[0],
        return_type=analysis2.return_type or "int",
        parameters=analysis2.parameters,
    )

    monkeypatch.setattr(
        strategy,
        "_check_return_case_coverage_gap",
        lambda *_args, **_kwargs: ReturnCoverageCheckResult(
            status="inconclusive",
            reason_id=UnknownReasonId.RETURN_COVERAGE_INCONCLUSIVE,
            can_record_completion_proof=True,
            detail="function1 return-case coverage query was inconclusive",
        ),
    )
    reasons = strategy._collect_return_coverage_unsafety_reasons(
        _base_context_for_single_int_param(),
        [case1],
        [case2],
        lambda value: value,
        lambda value: value,
        analysis1,
        analysis2,
    )

    assert reasons == ["function1:return_coverage_inconclusive", "function2:return_coverage_inconclusive"]
    reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:return_coverage_inconclusive",
        analysis1,
        analysis2,
        stage="S_PAIRWISE",
    )
    actions = build_unknown_recovery_actions([reason])
    assert actions
    assert analysis1.completed_recovery_proof_evidence == ()


def test_pairwise_return_coverage_inconclusive_unresolved_expression_does_not_auto_complete(monkeypatch):
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    analysis1, analysis2 = _return_coverage_gap_analyses()
    case1 = ReturnCase(
        index=0,
        conditions=[_eq(Expression.parameter("x", 0, size=4), _const(0))],
        value_expr=analysis1.returns[0].value,
        return_info=analysis1.returns[0],
        return_type=analysis1.return_type or "int",
        parameters=analysis1.parameters,
    )
    case2 = ReturnCase(
        index=0,
        conditions=[],
        value_expr=analysis2.returns[0].value,
        return_info=analysis2.returns[0],
        return_type=analysis2.return_type or "int",
        parameters=analysis2.parameters,
    )
    monkeypatch.setattr(
        strategy,
        "_check_return_case_coverage_gap",
        lambda *_args, **_kwargs: ReturnCoverageCheckResult(
            status="inconclusive",
            reason_id=UnknownReasonId.RETURN_COVERAGE_INCONCLUSIVE,
            detail=(
                "function1 return-case coverage query skipped:"
                " unresolved condition expression"
            ),
        ),
    )
    reasons = strategy._collect_return_coverage_unsafety_reasons(
        _base_context_for_single_int_param(),
        [case1],
        [case2],
        lambda value: value,
        lambda value: value,
        analysis1,
        analysis2,
    )

    assert reasons == ["function1:return_coverage_inconclusive", "function2:return_coverage_inconclusive"]
    assert analysis1.completed_recovery_proof_evidence == ()


def test_pairwise_return_coverage_non_dischargeable_inconclusive_causes_do_not_auto_complete(monkeypatch):
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    analysis1, analysis2 = _return_coverage_gap_analyses()
    case1 = ReturnCase(
        index=0,
        conditions=[_eq(Expression.parameter("x", 0, size=4), _const(0))],
        value_expr=analysis1.returns[0].value,
        return_info=analysis1.returns[0],
        return_type=analysis1.return_type or "int",
        parameters=analysis1.parameters,
    )
    case2 = ReturnCase(
        index=0,
        conditions=[],
        value_expr=analysis2.returns[0].value,
        return_info=analysis2.returns[0],
        return_type=analysis2.return_type or "int",
        parameters=analysis2.parameters,
    )

    for cause in ("object_identity_unsupported", "unresolved_expression", "missing_header_context"):
        analysis1.completed_recovery_proof_evidence = ()
        monkeypatch.setattr(
            strategy,
            "_check_return_case_coverage_gap",
            lambda *_args, cause=cause, **_kwargs: ReturnCoverageCheckResult(
                status="inconclusive",
                reason_id=UnknownReasonId.RETURN_COVERAGE_INCONCLUSIVE,
                can_record_completion_proof=True,
                inconclusive_cause=cause,
            ),
        )
        reasons = strategy._collect_return_coverage_unsafety_reasons(
            _base_context_for_single_int_param(),
            [case1],
            [case2],
            lambda value: value,
            lambda value: value,
            analysis1,
            analysis2,
        )

        assert reasons == ["function1:return_coverage_inconclusive", "function2:return_coverage_inconclusive"]
        assert analysis1.completed_recovery_proof_evidence == ()


def test_pairwise_return_coverage_inconclusive_invalid_proof_content_is_not_recorded(monkeypatch):
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    analysis1, analysis2 = _return_coverage_gap_analyses()
    case1 = ReturnCase(
        index=0,
        conditions=[_eq(Expression.parameter("x", 0, size=4), _const(0))],
        value_expr=analysis1.returns[0].value,
        return_info=analysis1.returns[0],
        return_type=analysis1.return_type or "int",
        parameters=analysis1.parameters,
    )
    case2 = ReturnCase(
        index=0,
        conditions=[],
        value_expr=analysis2.returns[0].value,
        return_info=analysis2.returns[0],
        return_type=analysis2.return_type or "int",
        parameters=analysis2.parameters,
    )

    monkeypatch.setattr(
        strategy,
        "_check_return_case_coverage_gap",
        lambda *_args, **_kwargs: ReturnCoverageCheckResult(
            status="inconclusive",
            reason_id=UnknownReasonId.RETURN_COVERAGE_INCONCLUSIVE,
            can_record_completion_proof=True,
            detail="function1 return-case coverage query was inconclusive",
        ),
    )
    monkeypatch.setattr(
        strategy,
        "_return_coverage_inconclusive_proof_content",
        lambda **_kwargs: {},
    )
    reasons = strategy._collect_return_coverage_unsafety_reasons(
        _base_context_for_single_int_param(),
        [case1],
        [case2],
        lambda value: value,
        lambda value: value,
        analysis1,
        analysis2,
    )

    assert reasons == ["function1:return_coverage_inconclusive", "function2:return_coverage_inconclusive"]
    assert analysis1.completed_recovery_proof_evidence == ()


def test_return_coverage_non_smt_covered_proof_content_does_not_claim_unsat():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    analysis = FunctionReturnAnalysis(
        function_name="func",
        entry_point="0x1",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1", value=_const(1), conditions=[])],
        return_type="int",
    )
    case = ReturnCase(
        index=0,
        conditions=[],
        value_expr=analysis.returns[0].value,
        return_info=analysis.returns[0],
        return_type=analysis.return_type or "int",
        parameters=analysis.parameters,
    )

    proof_content = strategy._return_coverage_covered_proof_content(
        base_ctx=_base_context_for_single_int_param(),
        label="function1",
        cases=[case],
        replace_fn=lambda value: value,
        coverage_proof_method="unconditional_return_case",
        solver_status=None,
    )

    assert proof_content["coverage_solver_evidence"]["status"] == "not_applicable"
    assert proof_content["coverage_solver_evidence"]["proof_method"] == "unconditional_return_case"


def test_unsupported_call_effect_reason_group_is_used_for_signature_matching():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)

    assert strategy._unsupported_call_effect_reason_is_compatible(
        "target_identity_unavailable",
        "callee_unsupported_call_may_expose_parameter_memory",
    )
    assert not strategy._unsupported_call_effect_reason_is_compatible(
        "target_identity_unavailable",
        "return_storage_missing_identity",
    )
    signature = strategy._unsupported_call_effect_reason_signature(
        "target_identity_unavailable",
    )
    assert "target_identity_unavailable" in signature
    assert "callee_unsupported_call_may_expose_parameter_memory" in signature


def test_unsupported_call_effect_semantics_respects_compatible_reason_groups():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)

    left = (
        "unsupported_call_effect",
        "function1",
        "analysis-1",
        (
            "runtime_ref",
            "unsupported_call_effect",
            ("callee_identity", ("unknown", "B1", ("target_expression", ("target", "A")))),
            ("typed_target_expression", ("target", "A")),
            ("argument_keys", (("argument", 0, ("arg", 0)),)),
        ),
        (
            "callsite_storage",
            ("callee_identity", ("unknown", "B1", ("target_expression", ("target", "A")))),
            ("target_expression", ("target", "A")),
            ("argument_keys", (("argument", 0, ("arg", 0)),)),
        ),
        ("effect_ordinal", 0),
        "target_identity_unavailable",
    )
    right = (
        "unsupported_call_effect",
        "function2",
        "analysis-2",
        (
            "runtime_ref",
            "unsupported_call_effect",
            ("callee_identity", ("unknown", "B2", ("target_expression", ("target", "A")))),
            ("typed_target_expression", ("target", "A")),
            ("argument_keys", (("argument", 0, ("arg", 0)),)),
        ),
        (
            "callsite_storage",
            ("callee_identity", ("unknown", "B2", ("target_expression", ("target", "A")))),
            ("target_expression", ("target", "A")),
            ("argument_keys", (("argument", 0, ("arg", 0)),)),
        ),
        ("effect_ordinal", 0),
        "callee_unsupported_call_may_expose_parameter_memory",
    )
    assert strategy._unsupported_call_effects_semantically_match(left, right)

    different_target = (
        right[0],
        right[1],
        right[2],
        (
            "runtime_ref",
            "unsupported_call_effect",
            ("callee_identity", ("unknown", "B2", ("target_expression", ("target", "B")))),
            ("typed_target_expression", ("target", "B")),
            ("argument_keys", (("argument", 0, ("arg", 0)),)),
        ),
        (
            "callsite_storage",
            ("callee_identity", ("unknown", "B2", ("target_expression", ("target", "B")))),
            ("target_expression", ("target", "B")),
            ("argument_keys", (("argument", 0, ("arg", 0)),)),
        ),
        right[5],
        right[6],
    )
    assert not strategy._unsupported_call_effects_semantically_match(left, different_target)

    right = tuple(list(right[:-1]) + ["return_storage_missing_identity"])
    assert not strategy._unsupported_call_effects_semantically_match(left, right)


def test_unsupported_call_effect_completed_proof_requires_compatibility_policy():
    evidence = _complete_call_effect_summary_proof_evidence(
        _call_effect_summary_proof_evidence()["object_target_key"]
    )

    assert _completed_proof_ids_for_call_effect_evidence(evidence)
    evidence["proof_content"].pop("compatibility_policy")

    assert _completed_proof_ids_for_call_effect_evidence(evidence) == ()


def test_call_effect_blocker_completed_proof_revalidates_selected_candidate_policy():
    selected_candidate = _call_effect_summary_proof_evidence()["object_target_key"]
    object_target_key = (
        "call_effect_blocker",
        "function1",
        ("function_ref", ("function", "B1", 0x1000)),
        "unsupported_call_effect_summary",
        "unsupported_call_effect_summary",
        (selected_candidate,),
        (),
        (),
        (),
    )
    selected_content = _call_effect_summary_proof_content(selected_candidate)
    expected_refs = PairwiseStrategy._expected_call_effect_proof_content_refs(
        object_target_key,
        candidate=selected_candidate,
    )
    assert expected_refs is not None
    runtime_ref, callsite_storage = expected_refs
    proof_content = {
        "object_derived": True,
        "status": "complete",
        "proof_rule": "call_effect_blocker_resolution",
        "object_target_key": object_target_key,
        "selected_candidate_key": selected_candidate,
        "selected_candidate_kind": "unsupported_call_effect",
        "selected_candidate_proof_content": selected_content,
        "peer_object_target_key": selected_content["peer_object_target_key"],
        "call_effect_summary": {
            "status": "complete",
            "summary_source": ("effect_summary", "call_effect_blocker"),
            "evidence_kind": "call_effect_summary",
            "object_target_key": object_target_key,
        },
        "runtime_ref": {
            "status": "complete",
            "runtime_ref": runtime_ref,
        },
        "callsite_storage": {
            "status": "complete",
            "callsite_storage": callsite_storage,
        },
    }
    evidence = _call_effect_summary_proof_evidence(object_target_key=object_target_key)
    evidence["proof_content"] = proof_content

    assert _completed_proof_ids_for_call_effect_evidence(evidence)

    incomplete = deepcopy(evidence)
    incomplete["proof_content"]["selected_candidate_proof_content"].pop(
        "compatibility_policy"
    )

    assert _completed_proof_ids_for_call_effect_evidence(incomplete) == ()


def test_unsupported_call_effect_semantics_requires_exact_target_expression_match_for_same_reason():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)

    left = (
        "unsupported_call_effect",
        "function1",
        "analysis-1",
        (
            "runtime_ref",
            "unsupported_call_effect",
            ("callee_identity", ("unknown", "B1", ("target_expression", ("target", "A")))),
            ("typed_target_expression", ("target", "A")),
            ("argument_keys", (("argument", 0, ("arg", 0)),)),
        ),
        (
            "callsite_storage",
            ("callee_identity", ("unknown", "B1", ("target_expression", ("target", "A")))),
            ("target_expression", ("target", "A")),
            ("argument_keys", (("argument", 0, ("arg", 0)),)),
        ),
        ("effect_ordinal", 0),
        "target_identity_unavailable",
    )
    right = (
        "unsupported_call_effect",
        "function1",
        "analysis-1",
        (
            "runtime_ref",
            "unsupported_call_effect",
            ("callee_identity", ("unknown", "B1", ("target_expression", ("target", "B")))),
            ("typed_target_expression", ("target", "B")),
            ("argument_keys", (("argument", 0, ("arg", 0)),)),
        ),
        (
            "callsite_storage",
            ("callee_identity", ("unknown", "B1", ("target_expression", ("target", "B")))),
            ("target_expression", ("target", "B")),
            ("argument_keys", (("argument", 0, ("arg", 0)),)),
        ),
        ("effect_ordinal", 0),
        "target_identity_unavailable",
    )

    assert not strategy._unsupported_call_effects_semantically_match(left, right)


def test_pairwise_strategy_does_not_prove_equivalent_with_incomplete_effect_summary(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = {
        "header_lines": [
            "(declare-const x_1 (_ BitVec 32))",
            "(declare-const x_2 (_ BitVec 32))",
            "(assert (= x_1 x_2))",
        ],
        "params1": [ParameterInfo(original_name="x", smt_name="x_1", bit_width=32, index=0)],
        "params2": [ParameterInfo(original_name="x", smt_name="x_2", bit_width=32, index=0)],
        "extra_vars1": [],
        "extra_vars2": [],
        "constrained_fragments": [],
        "return_size1": 32,
        "return_size2": 32,
    }
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)

    analysis1 = FunctionReturnAnalysis(
        function_name="func1",
        entry_point="0x1",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1", value=_const(1), conditions=[])],
        return_type="int",
        effect_summary=EffectSummary(
            parameter_names=["x"],
            effects=[],
            has_unsupported_call=True,
            incomplete_reasons=("effect_summary_path_coverage_incomplete",),
        ),
    )
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x2",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2", value=_const(1), conditions=[])],
        return_type="int",
    )
    case1 = ReturnCase(
        index=0,
        conditions=[],
        value_expr=_const(1),
        return_info=analysis1.returns[0],
        return_type="int",
        parameters=analysis1.parameters,
    )
    case2 = ReturnCase(
        index=0,
        conditions=[],
        value_expr=_const(1),
        return_info=analysis2.returns[0],
        return_type="int",
        parameters=analysis2.parameters,
    )

    monkeypatch.setattr(
        strategy,
        "_extract_return_cases",
        lambda analysis: [case1] if analysis.function_name == "func1" else [case2],
    )
    monkeypatch.setattr(strategy, "_prune_unreachable_cases", lambda cases, *_args, **_kwargs: cases)
    monkeypatch.setattr(strategy, "_cases_are_contradictory", lambda *_args, **_kwargs: False)
    monkeypatch.setattr(strategy, "_case_contains_unresolved_expression", lambda *_args, **_kwargs: False)
    strategy._solve_query_twostage = Mock(return_value=QueryResult(is_equivalent=True))

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.unsat_pairs == 1
    assert result.unknown_pairs == 0


def test_pairwise_strategy_does_not_prove_equivalent_with_unsupported_effect_summary(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = {
        "header_lines": [
            "(declare-const x_1 (_ BitVec 32))",
            "(declare-const x_2 (_ BitVec 32))",
            "(assert (= x_1 x_2))",
        ],
        "params1": [ParameterInfo(original_name="x", smt_name="x_1", bit_width=32, index=0)],
        "params2": [ParameterInfo(original_name="x", smt_name="x_2", bit_width=32, index=0)],
        "extra_vars1": [],
        "extra_vars2": [],
        "constrained_fragments": [],
        "return_size1": 32,
        "return_size2": 32,
    }
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)

    analysis1 = FunctionReturnAnalysis(
        function_name="func1",
        entry_point="0x1",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1", value=_const(1), conditions=[])],
        return_type="int",
        effect_summary=EffectSummary(
            parameter_names=["x"],
            effects=[],
            has_unsupported_call=True,
            incomplete_reasons=(),
        ),
    )
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x2",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2", value=_const(1), conditions=[])],
        return_type="int",
    )
    case1 = ReturnCase(
        index=0,
        conditions=[],
        value_expr=_const(1),
        return_info=analysis1.returns[0],
        return_type="int",
        parameters=analysis1.parameters,
    )
    case2 = ReturnCase(
        index=0,
        conditions=[],
        value_expr=_const(1),
        return_info=analysis2.returns[0],
        return_type="int",
        parameters=analysis2.parameters,
    )

    monkeypatch.setattr(
        strategy,
        "_extract_return_cases",
        lambda analysis: [case1] if analysis.function_name == "func1" else [case2],
    )
    monkeypatch.setattr(strategy, "_prune_unreachable_cases", lambda cases, *_args, **_kwargs: cases)
    monkeypatch.setattr(strategy, "_cases_are_contradictory", lambda *_args, **_kwargs: False)
    monkeypatch.setattr(strategy, "_case_contains_unresolved_expression", lambda *_args, **_kwargs: False)
    strategy._solve_query_twostage = Mock(return_value=QueryResult(is_equivalent=True))

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.unsat_pairs == 1
    assert result.unknown_pairs == 0


def test_pairwise_call_effect_summary_proof_pending_blocks_equivalent(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_unsupported_call_effect()
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x2000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=_const(1), conditions=[])],
        return_type="int",
    )
    _patch_pairwise_single_unsat_case(monkeypatch, strategy, analysis1, analysis2)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.unknown_reasons[0].reason_id == UnknownReasonId.EQUIVALENCE_BLOCKING_UNSAFETY.value
    assert result.unknown_reasons[0].action_status == UnknownRecoveryActionStatus.PENDING_PROOF.value
    assert result.unknown_reasons[0].proof_obligation_id is not None


def test_pairwise_sat_unsafety_emits_object_derived_pending_proof_backlog(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_unsupported_call_effect()
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x2000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=_const(2), conditions=[])],
        return_type="int",
    )
    _patch_pairwise_single_unsat_case(monkeypatch, strategy, analysis1, analysis2)
    strategy._solve_query_twostage = Mock(
        return_value=QueryResult(
            is_equivalent=False,
            counterexample_raw={"x_1": 0, "x_2": 0},
        )
    )

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.sat_pairs == 0
    assert result.unknown_pairs == 1
    reason = result.unknown_reasons[0]
    assert reason.reason_id == UnknownReasonId.SAT_UNSAFETY.value
    assert reason.decision_effect == "blocks_disequivalence"
    assert reason.recovery_proof_kind == UnknownRecoveryProofKind.SAT_UNSAFETY_RESOLUTION.value
    assert reason.action_status == UnknownRecoveryActionStatus.PENDING_PROOF.value
    assert reason.recovery_action == "sat_unsafety_resolution_required"
    assert reason.object_target_key[0] == "sat_unsafety"
    assert reason.object_evidence is not None
    assert reason.object_evidence["object_derived"] is True
    assert reason.object_evidence["evidence_kind"] == "active_unsafety_summary"
    assert reason.object_evidence["object_target_key"] == reason.object_target_key
    active_unsafety = reason.object_evidence["active_unsafety"]
    assert len(active_unsafety) == 1
    assert active_unsafety[0]["reason_kind"] == "unsupported_call_effect_summary"
    assert active_unsafety[0]["call_effect"]["object_derived"] is True
    assert active_unsafety[0]["call_effect"]["object_target_kind"] == "unsupported_call_effect"
    assert reason.proof_obligation_id == build_proof_obligation_id(
        UnknownReasonId.SAT_UNSAFETY,
        "sat_counterexample_safety",
        UnknownRecoveryProofKind.SAT_UNSAFETY_RESOLUTION,
        "active_unsafety_summary",
        reason.object_target_key,
    )
    actions = build_unknown_recovery_actions([reason])
    assert len(actions) == 1
    assert actions[0].required_evidence == (
        "counterexample_replay",
        "active_unsafety_discharge",
        "coverage_effect_safety",
    )
    assert actions[0].proof_obligation_id == reason.proof_obligation_id


def test_pairwise_keeps_global_coverage_gap_with_sat_unsafety(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1, analysis2 = _return_coverage_gap_analyses()
    analysis1.effect_summary = _analysis_with_unsupported_call_effect().effect_summary
    _patch_pairwise_return_coverage_gap_case(monkeypatch, strategy, analysis1, analysis2)
    strategy._solve_query_twostage = Mock(
        return_value=QueryResult(
            is_equivalent=False,
            counterexample_raw={"x_1": 0, "x_2": 0},
        )
    )

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.sat_pairs == 0
    assert result.unknown_pairs == 1
    reason_ids = {reason.reason_id for reason in result.unknown_reasons}
    assert UnknownReasonId.SAT_UNSAFETY.value in reason_ids
    assert UnknownReasonId.RETURN_COVERAGE_GAP.value in reason_ids
    assert result.unknown_reasons[0].reason_id == UnknownReasonId.SAT_UNSAFETY.value
    assert any(
        reason.reason_id == UnknownReasonId.RETURN_COVERAGE_GAP.value
        and reason.action_status == UnknownRecoveryActionStatus.PENDING_PROOF.value
        for reason in result.unknown_reasons
    )


def test_pairwise_sat_unsafety_completed_proof_allows_decisive_sat(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_unsupported_call_effect()
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x2000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=_const(2), conditions=[])],
        return_type="int",
    )
    case1 = ReturnCase(
        index=0,
        conditions=[],
        value_expr=analysis1.returns[0].value,
        return_info=analysis1.returns[0],
        return_type=analysis1.return_type or "int",
        parameters=analysis1.parameters,
    )
    case2 = ReturnCase(
        index=0,
        conditions=[],
        value_expr=analysis2.returns[0].value,
        return_info=analysis2.returns[0],
        return_type=analysis2.return_type or "int",
        parameters=analysis2.parameters,
    )
    monkeypatch.setattr(
        strategy,
        "_extract_return_cases",
        lambda analysis: [case1] if analysis.function_name == analysis1.function_name else [case2],
    )
    monkeypatch.setattr(strategy, "_prune_unreachable_cases", lambda cases, *_args, **_kwargs: cases)
    monkeypatch.setattr(strategy, "_cases_are_contradictory", lambda *_args, **_kwargs: False)
    monkeypatch.setattr(strategy, "_case_contains_unresolved_expression", lambda *_args, **_kwargs: False)
    monkeypatch.setattr(
        "scripts.function_tracer_pcode.equivalence.strategies.pairwise.validate_counterexample_across_cases",
        lambda *_args, **_kwargs: True,
    )
    strategy._solve_query_twostage = Mock(
        return_value=QueryResult(
            is_equivalent=False,
            counterexample_raw={"x_1": 0, "x_2": 0},
        )
    )
    reason = strategy._make_sat_unsafety_unknown_reason(
        ("function1:unsupported_call_effect_summary",),
        analysis1,
        analysis2,
        case1=case1,
        case2=case2,
        pair_id="(0,0)",
        stage="S_PAIRWISE",
    )
    action = build_unknown_recovery_actions([reason])[0]
    analysis1.completed_recovery_proof_evidence = (
        _sat_unsafety_resolution_evidence(action),
    )

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is False
    assert result.sat_pairs == 1
    assert result.unknown_reasons == []


def test_pairwise_same_function_sat_accepts_completed_counterexample_replay(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = FunctionReturnAnalysis(
        function_name="same_func",
        entry_point="0x1000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1000", value=_const(1), conditions=[])],
        return_type="int",
    )
    analysis2 = FunctionReturnAnalysis(
        function_name="same_func",
        entry_point="0x2000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=_const(2), conditions=[])],
        return_type="int",
    )
    case1 = ReturnCase(
        index=0,
        conditions=[],
        value_expr=analysis1.returns[0].value,
        return_info=analysis1.returns[0],
        return_type=analysis1.return_type or "int",
        parameters=analysis1.parameters,
    )
    case2 = ReturnCase(
        index=0,
        conditions=[],
        value_expr=analysis2.returns[0].value,
        return_info=analysis2.returns[0],
        return_type=analysis2.return_type or "int",
        parameters=analysis2.parameters,
    )
    monkeypatch.setattr(
        strategy,
        "_extract_return_cases",
        lambda analysis: [case1] if analysis is analysis1 else [case2],
    )
    monkeypatch.setattr(strategy, "_prune_unreachable_cases", lambda cases, *_args, **_kwargs: cases)
    monkeypatch.setattr(strategy, "_cases_are_contradictory", lambda *_args, **_kwargs: False)
    monkeypatch.setattr(strategy, "_case_contains_unresolved_expression", lambda *_args, **_kwargs: False)
    monkeypatch.setattr(
        "scripts.function_tracer_pcode.equivalence.strategies.pairwise.validate_counterexample_across_cases",
        lambda *_args, **_kwargs: True,
    )
    strategy._solve_query_twostage = Mock(
        return_value=QueryResult(
            is_equivalent=False,
            counterexample_raw={"x_1": 0, "x_2": 0},
        )
    )
    pending_reason = strategy._make_sat_unsafety_unknown_reason(
        ("counterexample_replay_missing",),
        analysis1,
        analysis2,
        case1=case1,
        case2=case2,
        pair_id="(0,0)",
        stage="S_PAIRWISE",
    )
    action = build_unknown_recovery_actions([pending_reason])[0]
    analysis1.completed_recovery_proof_evidence = (
        _sat_unsafety_resolution_evidence(action),
    )

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is False
    assert result.sat_pairs == 1
    assert result.unknown_pairs == 0
    assert result.unknown_reasons == []


def test_pairwise_same_function_sat_with_model_still_requires_prior_counterexample_replay(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = FunctionReturnAnalysis(
        function_name="same_func",
        entry_point="0x1000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1000", value=_const(1), conditions=[])],
        return_type="int",
    )
    analysis2 = FunctionReturnAnalysis(
        function_name="same_func",
        entry_point="0x2000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=_const(2), conditions=[])],
        return_type="int",
    )
    case1 = ReturnCase(
        index=0,
        conditions=[],
        value_expr=analysis1.returns[0].value,
        return_info=analysis1.returns[0],
        return_type=analysis1.return_type or "int",
        parameters=analysis1.parameters,
    )
    case2 = ReturnCase(
        index=0,
        conditions=[],
        value_expr=analysis2.returns[0].value,
        return_info=analysis2.returns[0],
        return_type=analysis2.return_type or "int",
        parameters=analysis2.parameters,
    )
    monkeypatch.setattr(
        strategy,
        "_extract_return_cases",
        lambda analysis: [case1] if analysis is analysis1 else [case2],
    )
    monkeypatch.setattr(strategy, "_prune_unreachable_cases", lambda cases, *_args, **_kwargs: cases)
    monkeypatch.setattr(strategy, "_cases_are_contradictory", lambda *_args, **_kwargs: False)
    monkeypatch.setattr(strategy, "_case_contains_unresolved_expression", lambda *_args, **_kwargs: False)
    monkeypatch.setattr(
        "scripts.function_tracer_pcode.equivalence.strategies.pairwise.validate_counterexample_across_cases",
        lambda *_args, **_kwargs: True,
    )
    strategy._solve_query_twostage = Mock(
        return_value=QueryResult(
            is_equivalent=False,
            counterexample_raw={"x_1": 0, "x_2": 0},
        )
    )

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.sat_pairs == 0
    assert result.unknown_pairs == 1
    reason = result.unknown_reasons[0]
    assert reason.reason_id == UnknownReasonId.SAT_UNSAFETY.value
    assert reason.evidence_refs == ("counterexample_replay_missing",)
    assert not any(
        evidence.get("proof_source") == "pairwise_case_split_counterexample_validation"
        for evidence in analysis1.completed_recovery_proof_evidence
    )


def test_pairwise_same_function_sat_without_model_still_requires_counterexample_replay(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = FunctionReturnAnalysis(
        function_name="same_func",
        entry_point="0x1000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1000", value=_const(1), conditions=[])],
        return_type="int",
    )
    analysis2 = FunctionReturnAnalysis(
        function_name="same_func",
        entry_point="0x2000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=_const(2), conditions=[])],
        return_type="int",
    )
    case1 = ReturnCase(
        index=0,
        conditions=[],
        value_expr=analysis1.returns[0].value,
        return_info=analysis1.returns[0],
        return_type=analysis1.return_type or "int",
        parameters=analysis1.parameters,
    )
    case2 = ReturnCase(
        index=0,
        conditions=[],
        value_expr=analysis2.returns[0].value,
        return_info=analysis2.returns[0],
        return_type=analysis2.return_type or "int",
        parameters=analysis2.parameters,
    )
    monkeypatch.setattr(
        strategy,
        "_extract_return_cases",
        lambda analysis: [case1] if analysis is analysis1 else [case2],
    )
    monkeypatch.setattr(strategy, "_prune_unreachable_cases", lambda cases, *_args, **_kwargs: cases)
    monkeypatch.setattr(strategy, "_cases_are_contradictory", lambda *_args, **_kwargs: False)
    monkeypatch.setattr(strategy, "_case_contains_unresolved_expression", lambda *_args, **_kwargs: False)
    monkeypatch.setattr(
        "scripts.function_tracer_pcode.equivalence.strategies.pairwise.validate_counterexample_across_cases",
        lambda *_args, **_kwargs: True,
    )
    strategy._solve_query_twostage = Mock(
        return_value=QueryResult(
            is_equivalent=False,
            counterexample_raw=None,
        )
    )

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.sat_pairs == 0
    assert result.unknown_pairs == 1
    reason = result.unknown_reasons[0]
    assert reason.reason_id == UnknownReasonId.SAT_UNSAFETY.value
    assert reason.evidence_refs == ("counterexample_replay_missing",)
    assert reason.action_status == UnknownRecoveryActionStatus.PENDING_PROOF.value
    assert reason.proof_obligation_id is not None


def test_pairwise_same_function_sat_with_unfixed_model_still_requires_counterexample_replay(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = FunctionReturnAnalysis(
        function_name="same_func",
        entry_point="0x1000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1000", value=_const(1), conditions=[])],
        return_type="int",
    )
    analysis2 = FunctionReturnAnalysis(
        function_name="same_func",
        entry_point="0x2000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=_const(2), conditions=[])],
        return_type="int",
    )
    case1 = ReturnCase(
        index=0,
        conditions=[],
        value_expr=analysis1.returns[0].value,
        return_info=analysis1.returns[0],
        return_type=analysis1.return_type or "int",
        parameters=analysis1.parameters,
    )
    case2 = ReturnCase(
        index=0,
        conditions=[],
        value_expr=analysis2.returns[0].value,
        return_info=analysis2.returns[0],
        return_type=analysis2.return_type or "int",
        parameters=analysis2.parameters,
    )
    monkeypatch.setattr(
        strategy,
        "_extract_return_cases",
        lambda analysis: [case1] if analysis is analysis1 else [case2],
    )
    monkeypatch.setattr(strategy, "_prune_unreachable_cases", lambda cases, *_args, **_kwargs: cases)
    monkeypatch.setattr(strategy, "_cases_are_contradictory", lambda *_args, **_kwargs: False)
    monkeypatch.setattr(strategy, "_case_contains_unresolved_expression", lambda *_args, **_kwargs: False)
    monkeypatch.setattr(
        "scripts.function_tracer_pcode.equivalence.strategies.pairwise.validate_counterexample_across_cases",
        lambda *_args, **_kwargs: True,
    )
    strategy._solve_query_twostage = Mock(
        return_value=QueryResult(
            is_equivalent=False,
            counterexample_raw={"return_1": 1, "return_2": 2},
        )
    )

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.sat_pairs == 0
    assert result.unknown_pairs == 1
    reason = result.unknown_reasons[0]
    assert reason.reason_id == UnknownReasonId.SAT_UNSAFETY.value
    assert reason.evidence_refs == ("counterexample_replay_missing",)
    assert not any(
        evidence.get("proof_source") == "pairwise_case_split_counterexample_validation"
        for evidence in analysis1.completed_recovery_proof_evidence
    )


def test_sat_unsafety_completed_proof_rejects_active_blocker_fields_on_evidence():
    action = _sat_unsafety_resolution_action()
    blocker_fields = (
        "active_coverage_gap_reasons",
        "unsupported_call_effect_reasons",
        "unsupported_memory_effect_reasons",
    )

    for field_name in blocker_fields:
        evidence = _sat_unsafety_resolution_evidence(action, **{field_name: ("still-active",)})

        assert PairwiseStrategy._sat_unsafety_resolution_proof_id_from_evidence(evidence) is None


def test_sat_unsafety_completed_proof_rejects_active_blocker_fields_inside_proof_content():
    action = _sat_unsafety_resolution_action()
    blocker_fields = (
        "active_coverage_gap_reasons",
        "unsupported_call_effect_reasons",
        "unsupported_memory_effect_reasons",
    )

    for field_name in blocker_fields:
        evidence = deepcopy(_sat_unsafety_resolution_evidence(action))
        evidence["proof_content"]["coverage_effect_safety"][field_name] = ("still-active",)

        assert PairwiseStrategy._sat_unsafety_resolution_proof_id_from_evidence(evidence) is None


def test_sat_unsafety_completed_proof_requires_object_derived_proof_content():
    action = _sat_unsafety_resolution_action()
    evidence = deepcopy(_sat_unsafety_resolution_evidence(action))
    evidence["proof_content"].pop("object_derived", None)

    assert PairwiseStrategy._sat_unsafety_resolution_proof_id_from_evidence(evidence) is None


def test_sat_unsafety_completed_proof_requires_fixed_counterexample_replay_model():
    action = _sat_unsafety_resolution_action()

    missing_hash = deepcopy(_sat_unsafety_resolution_evidence(action))
    missing_hash["proof_content"]["counterexample_replay"].pop(
        "counterexample_model_sha256",
        None,
    )
    assert PairwiseStrategy._sat_unsafety_resolution_proof_id_from_evidence(missing_hash) is None

    malformed_hash = deepcopy(_sat_unsafety_resolution_evidence(action))
    malformed_hash["proof_content"]["counterexample_replay"]["counterexample_model_sha256"] = "a" * 63
    assert PairwiseStrategy._sat_unsafety_resolution_proof_id_from_evidence(malformed_hash) is None

    missing_count = deepcopy(_sat_unsafety_resolution_evidence(action))
    missing_count["proof_content"]["counterexample_replay"].pop(
        "fixed_model_assertion_count",
        None,
    )
    assert PairwiseStrategy._sat_unsafety_resolution_proof_id_from_evidence(missing_count) is None

    zero_count = deepcopy(_sat_unsafety_resolution_evidence(action))
    zero_count["proof_content"]["counterexample_replay"]["fixed_model_assertion_count"] = 0
    assert PairwiseStrategy._sat_unsafety_resolution_proof_id_from_evidence(zero_count) is None

    missing_keys = deepcopy(_sat_unsafety_resolution_evidence(action))
    missing_keys["proof_content"]["counterexample_replay"].pop(
        "counterexample_symbol_keys",
        None,
    )
    assert PairwiseStrategy._sat_unsafety_resolution_proof_id_from_evidence(missing_keys) is None

    empty_keys = deepcopy(_sat_unsafety_resolution_evidence(action))
    empty_keys["proof_content"]["counterexample_replay"]["counterexample_symbol_keys"] = ()
    assert PairwiseStrategy._sat_unsafety_resolution_proof_id_from_evidence(empty_keys) is None


def test_sat_unsafety_completed_proof_requires_current_counterexample_model_match():
    action = _sat_unsafety_resolution_action()
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    analysis1 = FunctionReturnAnalysis(
        function_name="func1",
        entry_point="0x1000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1000", value=_const(1), conditions=[])],
        return_type="int",
    )
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x2000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=_const(2), conditions=[])],
        return_type="int",
    )
    reason = make_unknown_reason(
        UnknownReasonId.SAT_UNSAFETY,
        stage=action.stage,
        pair_or_case=action.pair_or_case,
        evidence_refs=action.evidence_refs,
        recovery_proof_kind=action.proof_kind,
        recovery_proof_obligations=(
            UnknownRecoveryProofObligation.create(
                action.proof_kind,
                action.proof_stage,
                required_evidence=action.required_evidence,
            ),
        ),
        proof_stage=action.proof_stage,
        evidence_kind=action.evidence_kind,
        object_target_key=action.object_target_key,
        proof_obligation_id=action.proof_obligation_id,
        action_status=UnknownRecoveryActionStatus.PENDING_PROOF.value,
    )
    analysis1.completed_recovery_proof_evidence = (
        _sat_unsafety_resolution_evidence(
            action,
            counterexample_raw={"x_1": 0, "x_2": 0},
        ),
    )

    assert strategy._sat_unsafety_resolution_proof_is_complete(
        reason,
        analysis1,
        analysis2,
        current_counterexample_raw={"x_1": 0, "x_2": 0},
    )
    assert not strategy._sat_unsafety_resolution_proof_is_complete(
        reason,
        analysis1,
        analysis2,
        current_counterexample_raw=None,
    )
    assert not strategy._sat_unsafety_resolution_proof_is_complete(
        reason,
        analysis1,
        analysis2,
        current_counterexample_raw={},
    )
    assert not strategy._sat_unsafety_resolution_proof_is_complete(
        reason,
        analysis1,
        analysis2,
        current_counterexample_raw={"x_1": 1, "x_2": 0},
    )


def test_sat_unsafety_completed_proof_rejects_nested_blocker_fields_inside_proof_content():
    action = _sat_unsafety_resolution_action()
    evidence = deepcopy(_sat_unsafety_resolution_evidence(action))
    evidence["proof_content"]["coverage_effect_safety"]["details"] = {
        "unsupported_call_effect_reasons": ("still-active",),
    }

    assert PairwiseStrategy._sat_unsafety_resolution_proof_id_from_evidence(evidence) is None


def test_pairwise_sat_unsafety_metadata_only_completed_proof_does_not_recover(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_unsupported_call_effect()
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x2000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=_const(2), conditions=[])],
        return_type="int",
    )
    _patch_pairwise_single_unsat_case(monkeypatch, strategy, analysis1, analysis2)
    strategy._solve_query_twostage = Mock(
        return_value=QueryResult(
            is_equivalent=False,
            counterexample_raw={"x_1": 0, "x_2": 0},
        )
    )
    pending_reason = strategy._make_sat_unsafety_unknown_reason(
        ("function1:unsupported_call_effect_summary",),
        analysis1,
        analysis2,
        case1=ReturnCase(
            index=0,
            conditions=[],
            value_expr=analysis1.returns[0].value,
            return_info=analysis1.returns[0],
            return_type=analysis1.return_type or "int",
            parameters=analysis1.parameters,
        ),
        case2=ReturnCase(
            index=0,
            conditions=[],
            value_expr=analysis2.returns[0].value,
            return_info=analysis2.returns[0],
            return_type=analysis2.return_type or "int",
            parameters=analysis2.parameters,
        ),
        pair_id="(0,0)",
        stage="S_PAIRWISE",
    )
    action = build_unknown_recovery_actions([pending_reason])[0]
    evidence = _sat_unsafety_resolution_evidence(action)
    evidence.pop("proof_content", None)
    analysis1.completed_recovery_proof_evidence = (evidence,)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.unknown_reasons[0].reason_id == UnknownReasonId.SAT_UNSAFETY.value


def test_pairwise_call_effect_summary_proof_wrong_id_does_not_recover(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_unsupported_call_effect()
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x2000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=_const(1), conditions=[])],
        return_type="int",
    )
    wrong_reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:unsupported_call_effect_summary",
        analysis1,
        analysis2,
        stage="S_PAIRWISE",
    )
    analysis1.completed_recovery_proof_ids = (
        (
            wrong_reason.reason_id,
            wrong_reason.proof_stage,
            wrong_reason.recovery_proof_kind,
            wrong_reason.evidence_kind,
            ("unsupported_call_effect", "different-callsite"),
        ),
    )
    _patch_pairwise_single_unsat_case(monkeypatch, strategy, analysis1, analysis2)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.unknown_reasons
    assert result.unknown_reasons[0].action_status == UnknownRecoveryActionStatus.PENDING_PROOF.value


def test_pairwise_call_effect_summary_bare_completed_proof_id_does_not_recover(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_unsupported_call_effect()
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x2000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=_const(1), conditions=[])],
        return_type="int",
    )
    completed_reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:unsupported_call_effect_summary",
        analysis1,
        analysis2,
        stage="S_PAIRWISE",
    )
    analysis1.completed_recovery_proof_ids = (completed_reason.proof_obligation_id,)
    _patch_pairwise_single_unsat_case(monkeypatch, strategy, analysis1, analysis2)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.unknown_reasons
    assert result.unknown_reasons[0].action_status == UnknownRecoveryActionStatus.PENDING_PROOF.value


def test_pairwise_call_effect_summary_missing_completed_proof_id_does_not_recover(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_unsupported_call_effect()
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x2000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=_const(1), conditions=[])],
        return_type="int",
    )
    completed_reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:unsupported_call_effect_summary",
        analysis1,
        analysis2,
        stage="S_PAIRWISE",
    )
    evidence = _call_effect_summary_proof_evidence(
        object_target_key=completed_reason.object_target_key,
        proof_obligation_id=completed_reason.proof_obligation_id,
    )
    evidence.pop("proof_obligation_id", None)
    analysis1.completed_recovery_proof_evidence = (evidence,)
    _patch_pairwise_single_unsat_case(monkeypatch, strategy, analysis1, analysis2)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.unknown_reasons
    assert result.unknown_reasons[0].action_status == UnknownRecoveryActionStatus.PENDING_PROOF.value


def test_pairwise_call_effect_summary_producer_connects_completed_target_proof(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_unsupported_call_effect()
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x2000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=_const(1), conditions=[])],
        return_type="int",
    )
    completed_reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:unsupported_call_effect_summary",
        analysis1,
        analysis2,
        stage="S_PAIRWISE",
    )
    analysis1.completed_recovery_proof_evidence = (
        _complete_call_effect_summary_proof_evidence(
            completed_reason.object_target_key,
            proof_obligation_id=completed_reason.proof_obligation_id,
        ),
    )
    _patch_pairwise_single_unsat_case(monkeypatch, strategy, analysis1, analysis2)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is True
    assert result.unknown_reasons == []
    assert result.unsat_pairs == 1
    assert result.unknown_pairs == 0


def test_pairwise_self_recursive_no_store_call_effect_proof_recovers(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_self_recursive_unsupported_call_effect()
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x2000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=_const(1), conditions=[])],
        return_type="int",
    )
    _patch_pairwise_single_unsat_case(monkeypatch, strategy, analysis1, analysis2)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is True
    assert result.unknown_reasons == []
    assert result.unsat_pairs == 1
    assert result.unknown_pairs == 0
    evidence = [
        item
        for item in analysis1.completed_recovery_proof_evidence
        if item.get("evidence_kind") == "call_effect_summary"
    ]
    assert len(evidence) == 1
    assert evidence[0]["proof_source"] == "self_recursive_no_store_call_effect_summary"
    assert evidence[0]["proof_content"]["proof_rule"] == "self_recursive_no_store_effect_summary"


def test_pairwise_preproducer_complete_call_argument_evidence_requires_pending_proof(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(
        formula_builder,
        solver_runner,
        debug=False,
        enable_completed_recovery_proofs=False,
    )
    analysis1 = _analysis_with_effect_call_argument_evidence()
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x2000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=_const(1), conditions=[])],
        return_type="int",
    )
    _patch_pairwise_single_unsat_case(monkeypatch, strategy, analysis1, analysis2)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.unknown_reasons
    reason = result.unknown_reasons[0]
    assert reason.reason_id == UnknownReasonId.EQUIVALENCE_BLOCKING_UNSAFETY.value
    assert reason.action_status == UnknownRecoveryActionStatus.PENDING_PROOF.value
    assert reason.detail == "function1:effect_call_argument_evidence"
    assert reason.object_target_key[0] == "call_argument_evidence"
    assert reason.object_evidence is not None
    assert reason.object_evidence["object_derived"] is True
    assert reason.object_evidence["runtime_ref"] == (
        "runtime_ref",
        "call_argument",
        ("pcode_op_ref", reason.object_target_key[3]),
        ("callee_identity", reason.object_target_key[4]),
    )
    assert reason.object_evidence["argument_storage"] == reason.object_target_key[5]
    assert reason.object_evidence["callsite_storage"] == (
        "callsite_storage",
        "call_argument",
        ("argument_keys", reason.object_target_key[5]),
    )


def test_pairwise_complete_call_argument_evidence_requires_explicit_phase15_proof(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_effect_call_argument_evidence()
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x2000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=_const(1), conditions=[])],
        return_type="int",
    )
    _patch_pairwise_single_unsat_case(monkeypatch, strategy, analysis1, analysis2)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.unknown_reasons
    assert result.unknown_reasons[0].detail == "function1:effect_call_argument_evidence"
    evidence = [
        item
        for item in analysis1.completed_recovery_proof_evidence
        if item.get("proof_source") == "call_argument_evidence_complete"
    ]
    assert evidence == []


def test_pairwise_preserves_call_effect_reason_alongside_return_coverage_gap(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1, analysis2 = _return_coverage_gap_analyses()
    analysis1.effect_summary = _analysis_with_effect_call_argument_evidence().effect_summary
    _patch_pairwise_return_coverage_gap_case(monkeypatch, strategy, analysis1, analysis2)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    reason_ids = [reason.reason_id for reason in result.unknown_reasons]
    assert UnknownReasonId.RETURN_COVERAGE_GAP.value in reason_ids
    assert UnknownReasonId.EQUIVALENCE_BLOCKING_UNSAFETY.value in reason_ids
    effect_reasons = [
        reason
        for reason in result.unknown_reasons
        if reason.reason_id == UnknownReasonId.EQUIVALENCE_BLOCKING_UNSAFETY.value
    ]
    assert effect_reasons
    assert effect_reasons[0].detail == "function1:effect_call_argument_evidence"
    assert effect_reasons[0].recovery_proof_kind == (
        UnknownRecoveryProofKind.CALL_EFFECT_SUMMARY_PROOF.value
    )


def test_pairwise_matched_unknown_indirect_no_store_call_effect_recovers(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_unknown_indirect_call_effect(
        function_name="func1",
        binary_id="B10",
        entry=0x1000,
    )
    analysis2 = _analysis_with_unknown_indirect_call_effect(
        function_name="func2",
        binary_id="B11",
        entry=0x2000,
    )
    _patch_pairwise_single_unsat_case(monkeypatch, strategy, analysis1, analysis2)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is True
    assert result.unknown_reasons == []
    for analysis in (analysis1, analysis2):
        evidence = [
            item
            for item in analysis.completed_recovery_proof_evidence
            if item.get("proof_source") == "matched_unknown_indirect_no_store_call_effect"
        ]
        assert len(evidence) == 1
        content = evidence[0]["proof_content"]
        assert content["proof_rule"] == "matched_unknown_indirect_no_store_call_effect"
        assert (
            content["call_effect_summary"]["matching_local_unsupported_call_site_count"]
            == 1
        )
        assert (
            content["call_effect_summary"]["matching_peer_unsupported_call_site_count"]
            == 1
        )
        assert content["call_effect_surface"]["guard_equivalence_mode"] == "path_guard_equivalence"
        assert (
            content["call_effect_surface"]["caller_observed_memory_write"][
                "local_store_effect_count"
            ]
            == 0
        )
        assert (
            content["call_effect_surface"]["call_output_use"]["classification"]
            == "not_exposed_to_return_or_call_effect_surface"
        )
        assert content["runtime_ref"]["matched_target_expression_key"]
        assert content["callsite_storage"]["matched_argument_keys"]


def test_pairwise_unknown_indirect_legacy_return_guard_mismatch_is_not_path_proof(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_unknown_indirect_call_effect(
        function_name="func1",
        binary_id="B10",
        entry=0x1000,
        path_conditions=(_eq(Expression.parameter("a", 1, size=4), _const(0)),),
    )
    analysis2 = _analysis_with_unknown_indirect_call_effect(
        function_name="func2",
        binary_id="B11",
        entry=0x2000,
        path_conditions=(_ne(Expression.parameter("a", 1, size=4), _const(0)),),
    )
    _patch_pairwise_single_unsat_case(monkeypatch, strategy, analysis1, analysis2)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.unknown_reasons
    assert not [
        item
        for analysis in (analysis1, analysis2)
        for item in analysis.completed_recovery_proof_evidence
        if item.get("proof_source") == "matched_unknown_indirect_no_store_call_effect"
    ]


def test_pairwise_unknown_indirect_callsite_path_guard_mismatch_keeps_unknown(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    a = Expression.parameter("a", 1, size=4)
    analysis1 = _analysis_with_unknown_indirect_call_effect(
        function_name="func1",
        binary_id="B10",
        entry=0x1000,
        path_conditions=(_eq(a, _const(0)),),
    )
    analysis2 = _analysis_with_unknown_indirect_call_effect(
        function_name="func2",
        binary_id="B11",
        entry=0x2000,
        path_conditions=(_ne(a, _const(0)),),
    )
    _patch_pairwise_single_unsat_case(monkeypatch, strategy, analysis1, analysis2)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.unknown_reasons
    assert not [
        item
        for analysis in (analysis1, analysis2)
        for item in analysis.completed_recovery_proof_evidence
        if item.get("proof_source") == "matched_unknown_indirect_no_store_call_effect"
    ]


def test_call_effect_summary_proof_rejects_occurrence_index_mismatch():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    analysis1 = _analysis_with_unknown_indirect_call_effect(
        function_name="func1",
        binary_id="B10",
        entry=0x1000,
    )
    analysis2 = _analysis_with_unknown_indirect_call_effect(
        function_name="func2",
        binary_id="B11",
        entry=0x2000,
    )
    reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:unsupported_call_effect_summary",
        analysis1,
        analysis2,
        stage="S_PAIRWISE",
    )
    evidence = _complete_call_effect_summary_proof_evidence(reason.object_target_key)
    evidence["proof_content"]["call_effect_surface"]["peer_call_occurrence"][
        "occurrence_index"
    ] = 1

    assert _completed_proof_ids_for_call_effect_evidence(evidence) == ()


def test_pairwise_unknown_indirect_output_surface_use_keeps_unknown(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_unknown_indirect_call_effect(
        function_name="func1",
        binary_id="B10",
        entry=0x1000,
    )
    analysis2 = _analysis_with_unknown_indirect_call_effect(
        function_name="func2",
        binary_id="B11",
        entry=0x2000,
    )
    site = analysis1.effect_summary.unsupported_call_sites[0]
    analysis1.returns = [
        ReturnInfo(
            address="0x1000",
            value=Expression.unknown("callind_result", runtime_ref=site.pcode_op_ref),
            conditions=[],
        )
    ]
    _patch_pairwise_single_unsat_case(monkeypatch, strategy, analysis1, analysis2)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.unknown_reasons
    assert not [
        item
        for analysis in (analysis1, analysis2)
        for item in analysis.completed_recovery_proof_evidence
        if item.get("proof_source") == "matched_unknown_indirect_no_store_call_effect"
    ]


def test_pairwise_unknown_indirect_output_used_as_later_call_argument_keeps_unknown(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_unknown_indirect_call_effect(
        function_name="func1",
        binary_id="B10",
        entry=0x1000,
    )
    analysis2 = _analysis_with_unknown_indirect_call_effect(
        function_name="func2",
        binary_id="B11",
        entry=0x2000,
    )
    first = analysis1.effect_summary.unsupported_call_sites[0]
    later = UnsupportedCallEffectRef(
        pcode_op_ref=PcodeOpRef(
            address_offset=0x1050,
            seq_time=6,
            seq_order=3,
            block_index=0,
            mnemonic="CALLIND",
            input_sizes=(8, 4),
            binary_id="B10",
            function_entry_space="ram",
            function_entry_offset=0x1000,
            target_space="ram",
            target_offset=0x1050,
            opcode=8,
            local_op_ordinal=2,
        ),
        target_ref=first.target_ref,
        target_expr=Expression.parameter("fp", 0, size=8),
        arguments=(Expression.unknown("first_call_result", runtime_ref=first.pcode_op_ref),),
        path_conditions=first.path_conditions,
        reason=first.reason,
        order_key=11,
    )
    analysis1.effect_summary.unsupported_call_sites = (first, later)
    _patch_pairwise_single_unsat_case(monkeypatch, strategy, analysis1, analysis2)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.unknown_reasons
    assert not [
        item
        for analysis in (analysis1, analysis2)
        for item in analysis.completed_recovery_proof_evidence
        if item.get("proof_source") == "matched_unknown_indirect_no_store_call_effect"
    ]


def test_pairwise_unknown_indirect_observed_store_keeps_unknown(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_unknown_indirect_call_effect(
        function_name="func1",
        binary_id="B10",
        entry=0x1000,
    )
    analysis2 = _analysis_with_unknown_indirect_call_effect(
        function_name="func2",
        binary_id="B11",
        entry=0x2000,
    )
    analysis1.effect_summary.effects = [
        StoreEffect(
            location=CanonicalLocation("global", 0, 4),
            value=_const(1),
            conditions=[],
            order_key=11,
        )
    ]
    _patch_pairwise_single_unsat_case(monkeypatch, strategy, analysis1, analysis2)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.unknown_reasons
    assert not [
        item
        for analysis in (analysis1, analysis2)
        for item in analysis.completed_recovery_proof_evidence
        if item.get("proof_source") == "matched_unknown_indirect_no_store_call_effect"
    ]


def test_pairwise_unknown_indirect_duplicate_call_effect_does_not_auto_proof(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_unknown_indirect_call_effect(
        function_name="func1",
        binary_id="B10",
        entry=0x1000,
    )
    analysis2 = _analysis_with_unknown_indirect_call_effect(
        function_name="func2",
        binary_id="B11",
        entry=0x2000,
    )
    original = analysis1.effect_summary.unsupported_call_sites[0]
    duplicate = UnsupportedCallEffectRef(
        pcode_op_ref=PcodeOpRef(
            address_offset=0x1040,
            seq_time=5,
            seq_order=2,
            block_index=0,
            mnemonic="CALLIND",
            input_sizes=(8, 4, 4),
            binary_id="B10",
            function_entry_space="ram",
            function_entry_offset=0x1000,
            target_space="ram",
            target_offset=0x1040,
            opcode=8,
            local_op_ordinal=1,
        ),
        target_ref=original.target_ref,
        target_expr=original.target_expr,
        arguments=original.arguments,
        reason=original.reason,
        order_key=9,
    )
    analysis1.effect_summary.unsupported_call_sites = (original, duplicate)
    _patch_pairwise_single_unsat_case(monkeypatch, strategy, analysis1, analysis2)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.unknown_reasons
    assert not [
        item
        for analysis in (analysis1, analysis2)
        for item in analysis.completed_recovery_proof_evidence
        if item.get("proof_source") == "matched_unknown_indirect_no_store_call_effect"
    ]


def test_pairwise_unknown_indirect_missing_target_expr_does_not_auto_proof(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_unknown_indirect_call_effect(
        function_name="func1",
        binary_id="B10",
        entry=0x1000,
        target_expr_missing=True,
    )
    analysis2 = _analysis_with_unknown_indirect_call_effect(
        function_name="func2",
        binary_id="B11",
        entry=0x2000,
        target_expr_missing=True,
    )
    _patch_pairwise_single_unsat_case(monkeypatch, strategy, analysis1, analysis2)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert {
        reason.detail for reason in result.unknown_reasons
    } == {
        "function1:unsupported_call_effect_summary",
        "function2:unsupported_call_effect_summary",
    }
    assert not [
        item
        for analysis in (analysis1, analysis2)
        for item in analysis.completed_recovery_proof_evidence
        if item.get("proof_source") == "matched_unknown_indirect_no_store_call_effect"
    ]


def test_pairwise_unknown_indirect_target_mismatch_does_not_auto_proof(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_unknown_indirect_call_effect(
        function_name="func1",
        binary_id="B10",
        entry=0x1000,
        target_param_index=0,
    )
    analysis2 = _analysis_with_unknown_indirect_call_effect(
        function_name="func2",
        binary_id="B11",
        entry=0x2000,
        target_param_index=1,
    )
    _patch_pairwise_single_unsat_case(monkeypatch, strategy, analysis1, analysis2)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert {
        reason.detail for reason in result.unknown_reasons
    } == {
        "function1:unsupported_call_effect_summary",
        "function2:unsupported_call_effect_summary",
    }


def test_pairwise_unknown_indirect_argument_mismatch_does_not_auto_proof(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_unknown_indirect_call_effect(
        function_name="func1",
        binary_id="B10",
        entry=0x1000,
        argument_indices=(1, 2),
    )
    analysis2 = _analysis_with_unknown_indirect_call_effect(
        function_name="func2",
        binary_id="B11",
        entry=0x2000,
        argument_indices=(2, 1),
    )
    _patch_pairwise_single_unsat_case(monkeypatch, strategy, analysis1, analysis2)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert len(result.unknown_reasons) == 2


def test_pairwise_matched_parameter_exposure_unsupported_call_effect_recovers(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_unknown_indirect_call_effect(
        function_name="func1",
        binary_id="B10",
        entry=0x1000,
        reason="callee_unsupported_call_may_expose_parameter_memory",
    )
    analysis2 = _analysis_with_unknown_indirect_call_effect(
        function_name="func2",
        binary_id="B11",
        entry=0x2000,
        reason="callee_unsupported_call_may_expose_parameter_memory",
    )
    _patch_pairwise_single_unsat_case(monkeypatch, strategy, analysis1, analysis2)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is True
    assert result.unknown_reasons == []
    for analysis in (analysis1, analysis2):
        evidence = [
            item
            for item in analysis.completed_recovery_proof_evidence
            if item.get("proof_source")
            == "matched_unsupported_call_parameter_exposure_no_store_call_effect"
        ]
        assert len(evidence) == 1
        content = evidence[0]["proof_content"]
        assert content["proof_rule"] == "matched_unsupported_call_parameter_exposure_no_store_call_effect"
        assert (
            content["call_effect_summary"]["unsupported_reason"]
            == "callee_unsupported_call_may_expose_parameter_memory"
        )


def test_pairwise_mixed_unsupported_call_reason_is_compatible_recovers(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_unknown_indirect_call_effect(
        function_name="func1",
        binary_id="B10",
        entry=0x1000,
        reason="callee_unsupported_call_may_expose_parameter_memory",
    )
    analysis2 = _analysis_with_unknown_indirect_call_effect(
        function_name="func2",
        binary_id="B11",
        entry=0x2000,
        reason="target_identity_unavailable",
    )
    _patch_pairwise_single_unsat_case(monkeypatch, strategy, analysis1, analysis2)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is True
    assert result.unknown_reasons == []
    assert len([
        item
        for analysis in (analysis1, analysis2)
        for item in analysis.completed_recovery_proof_evidence
        if item.get("proof_source") == "matched_unknown_indirect_no_store_call_effect"
    ]) == 2


def test_pairwise_incompatible_unsupported_call_reason_keeps_unknown(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_unknown_indirect_call_effect(
        function_name="func1",
        binary_id="B10",
        entry=0x1000,
        reason="target_identity_unavailable",
    )
    analysis2 = _analysis_with_unknown_indirect_call_effect(
        function_name="func2",
        binary_id="B11",
        entry=0x2000,
        reason="callee_effect_summary_incomplete",
    )
    _patch_pairwise_single_unsat_case(monkeypatch, strategy, analysis1, analysis2)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert len(result.unknown_reasons) == 2
    assert all(
        not [
            item
            for item in analysis.completed_recovery_proof_evidence
            if item.get("proof_source")
            in (
                "matched_unknown_indirect_no_store_call_effect",
                "matched_unsupported_call_parameter_exposure_no_store_call_effect",
            )
        ]
        for analysis in (analysis1, analysis2)
    )


def test_pairwise_matched_deferred_call_argument_evidence_recovers(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_deferred_call_argument_blocker(
        function_name="func1",
        binary_id="B1",
        entry=0x1000,
    )
    analysis2 = _analysis_with_deferred_call_argument_blocker(
        function_name="func2",
        binary_id="B14",
        entry=0x2000,
    )
    _patch_pairwise_single_unsat_case(monkeypatch, strategy, analysis1, analysis2)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is True
    assert result.unknown_reasons == []
    for analysis in (analysis1, analysis2):
        evidence = [
            item
            for item in analysis.completed_recovery_proof_evidence
            if item.get("proof_source") == "matched_deferred_call_argument_evidence"
        ]
        assert len(evidence) == 1
        content = evidence[0]["proof_content"]
        assert content["proof_rule"] == "matched_deferred_call_argument_evidence"
        assert content["runtime_ref"]["matched_target_expression_key"]
        assert content["callsite_storage"]["matched_argument_keys"]
        assert content["call_effect_summary"]["matching_local_deferred_call_count"] == 1
        assert content["call_effect_summary"]["matching_peer_deferred_call_count"] == 1


def test_pairwise_unresolved_deferred_call_return_lowers_with_matched_argument_evidence(monkeypatch):
    base_ctx = _base_context_for_single_int_param()
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = base_ctx
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_deferred_call_argument_blocker(
        function_name="func1",
        binary_id="B1",
        entry=0x1000,
        return_deferred_unknown=True,
    )
    analysis2 = _analysis_with_deferred_call_argument_blocker(
        function_name="func2",
        binary_id="B14",
        entry=0x2000,
        return_deferred_unknown=True,
    )
    _patch_pairwise_single_case(monkeypatch, strategy, analysis1, analysis2)
    solver_runner.run_sequential = Mock(
        side_effect=[
            ParallelResult(
                results=[
                    SolverResult(
                        solver_name="z3",
                        status=SolverStatus.SAT,
                        elapsed_time=0.001,
                    )
                ]
            ),
            ParallelResult(
                results=[
                    SolverResult(
                        solver_name="z3",
                        status=SolverStatus.UNSAT,
                        elapsed_time=0.001,
                    )
                ]
            ),
        ]
    )

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is True
    assert result.unknown_reasons == []
    assert solver_runner.run_sequential.call_count == 2
    assertions = base_ctx["pairwise_extra_assertions_by_pair"]["(0,0)"]
    assert assertions[0].startswith("; unresolved_expression runtime-unknown equality")
    assert any(line.startswith("(assert (= rtunk_") for line in assertions)
    query = solver_runner.run_sequential.call_args_list[1].args[0]
    assert "; Pair-local object-derived assumptions" in query
    assert any(line in query for line in assertions if line.startswith("(assert (= rtunk_"))
    evidence = base_ctx["pairwise_unresolved_deferred_call_lowering_evidence_by_pair"]["(0,0)"]
    assert len(evidence) == 1
    assert evidence[0][0] == "matched_deferred_call_runtime_unknown"
    assert ("lowering_kind", "deferred_call") in evidence[0]


def test_pairwise_unresolved_deferred_call_missing_target_expr_stays_unknown(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_deferred_call_argument_blocker(
        function_name="func1",
        binary_id="B1",
        entry=0x1000,
        target_expr_missing=True,
        return_deferred_unknown=True,
    )
    analysis2 = _analysis_with_deferred_call_argument_blocker(
        function_name="func2",
        binary_id="B14",
        entry=0x2000,
        target_expr_missing=True,
        return_deferred_unknown=True,
    )
    _patch_pairwise_single_case(monkeypatch, strategy, analysis1, analysis2)
    strategy._solve_query_twostage = Mock(return_value=QueryResult(is_equivalent=True))

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert [reason.reason_id for reason in result.unknown_reasons] == [
        UnknownReasonId.EQUIVALENCE_BLOCKING_UNSAFETY.value,
        UnknownReasonId.EQUIVALENCE_BLOCKING_UNSAFETY.value,
    ]
    assert {
        reason.detail for reason in result.unknown_reasons
    } == {
        "function1:effect_call_argument_evidence_incomplete",
        "function2:effect_call_argument_evidence_incomplete",
    }
    assert "pairwise_extra_assertions_by_pair" not in formula_builder.build_base_context.return_value
    strategy._solve_query_twostage.assert_not_called()


def test_pairwise_unresolved_deferred_call_width_mismatch_stays_unknown(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_deferred_call_argument_blocker(
        function_name="func1",
        binary_id="B1",
        entry=0x1000,
        return_deferred_unknown=True,
        unknown_size=4,
    )
    analysis2 = _analysis_with_deferred_call_argument_blocker(
        function_name="func2",
        binary_id="B14",
        entry=0x2000,
        return_deferred_unknown=True,
        unknown_size=8,
    )
    _patch_pairwise_single_case(monkeypatch, strategy, analysis1, analysis2)
    strategy._solve_query_twostage = Mock(return_value=QueryResult(is_equivalent=True))

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert [reason.reason_id for reason in result.unknown_reasons] == [
        UnknownReasonId.UNRESOLVED_EXPRESSION.value
    ]
    strategy._solve_query_twostage.assert_not_called()


def test_pairwise_opaque_unresolved_return_stays_unknown(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = FunctionReturnAnalysis(
        function_name="func1",
        entry_point="0x1000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1000", value=Expression.unknown("opaque").clone_with(size=4), conditions=[])],
        return_type="int",
        binary_id="B1",
    )
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x2000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=Expression.unknown("opaque").clone_with(size=4), conditions=[])],
        return_type="int",
        binary_id="B14",
    )
    _patch_pairwise_single_case(monkeypatch, strategy, analysis1, analysis2)
    strategy._solve_query_twostage = Mock(return_value=QueryResult(is_equivalent=True))

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert [reason.reason_id for reason in result.unknown_reasons] == [
        UnknownReasonId.UNRESOLVED_EXPRESSION.value
    ]
    strategy._solve_query_twostage.assert_not_called()


def test_pairwise_deferred_call_missing_target_expr_does_not_auto_proof(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_deferred_call_argument_blocker(
        function_name="func1",
        binary_id="B1",
        entry=0x1000,
        target_expr_missing=True,
    )
    analysis2 = _analysis_with_deferred_call_argument_blocker(
        function_name="func2",
        binary_id="B14",
        entry=0x2000,
        target_expr_missing=True,
    )
    _patch_pairwise_single_unsat_case(monkeypatch, strategy, analysis1, analysis2)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert {
        reason.detail for reason in result.unknown_reasons
    } == {
        "function1:effect_call_argument_evidence_incomplete",
        "function2:effect_call_argument_evidence_incomplete",
    }
    assert not [
        item
        for analysis in (analysis1, analysis2)
        for item in analysis.completed_recovery_proof_evidence
        if item.get("proof_source") == "matched_deferred_call_argument_evidence"
    ]


def test_pairwise_deferred_call_argument_mismatch_does_not_auto_proof(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_deferred_call_argument_blocker(
        function_name="func1",
        binary_id="B1",
        entry=0x1000,
        argument_indices=(1, 2),
    )
    analysis2 = _analysis_with_deferred_call_argument_blocker(
        function_name="func2",
        binary_id="B14",
        entry=0x2000,
        argument_indices=(2, 1),
    )
    _patch_pairwise_single_unsat_case(monkeypatch, strategy, analysis1, analysis2)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert len(result.unknown_reasons) == 2
    assert not [
        item
        for analysis in (analysis1, analysis2)
        for item in analysis.completed_recovery_proof_evidence
        if item.get("proof_source") == "matched_deferred_call_argument_evidence"
    ]


def test_pairwise_deferred_call_empty_arguments_does_not_auto_proof(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_deferred_call_argument_blocker(
        function_name="func1",
        binary_id="B1",
        entry=0x1000,
        argument_indices=(),
    )
    analysis2 = _analysis_with_deferred_call_argument_blocker(
        function_name="func2",
        binary_id="B14",
        entry=0x2000,
        argument_indices=(),
    )
    _patch_pairwise_single_unsat_case(monkeypatch, strategy, analysis1, analysis2)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert {
        reason.detail for reason in result.unknown_reasons
    } == {
        "function1:effect_call_argument_evidence_incomplete",
        "function2:effect_call_argument_evidence_incomplete",
    }
    assert not [
        item
        for analysis in (analysis1, analysis2)
        for item in analysis.completed_recovery_proof_evidence
        if item.get("proof_source") == "matched_deferred_call_argument_evidence"
    ]


def test_pairwise_unresolved_deferred_call_empty_arguments_stays_unknown(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_deferred_call_argument_blocker(
        function_name="func1",
        binary_id="B1",
        entry=0x1000,
        argument_indices=(),
        return_deferred_unknown=True,
        call_argument_recovery_status=CallArgumentEvidence.RECOVERY_COMPLETE,
    )
    analysis2 = _analysis_with_deferred_call_argument_blocker(
        function_name="func2",
        binary_id="B14",
        entry=0x2000,
        argument_indices=(),
        return_deferred_unknown=True,
        call_argument_recovery_status=CallArgumentEvidence.RECOVERY_COMPLETE,
    )
    _patch_pairwise_single_case(monkeypatch, strategy, analysis1, analysis2)
    strategy._solve_query_twostage = Mock(return_value=QueryResult(is_equivalent=True))

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert [reason.reason_id for reason in result.unknown_reasons] == [
        UnknownReasonId.UNRESOLVED_EXPRESSION.value
    ]
    strategy._solve_query_twostage.assert_not_called()


def test_pairwise_unresolved_deferred_call_store_effect_stays_unknown(monkeypatch):
    base_ctx = _base_context_for_single_int_param()
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = base_ctx
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_deferred_call_argument_blocker(
        function_name="func1",
        binary_id="B1",
        entry=0x1000,
        return_deferred_unknown=True,
    )
    analysis2 = _analysis_with_deferred_call_argument_blocker(
        function_name="func2",
        binary_id="B14",
        entry=0x2000,
        return_deferred_unknown=True,
    )
    analysis1.effect_summary.effects = [
        StoreEffect(
            location=CanonicalLocation("fp", 0, 4),
            value=_const(1),
            conditions=[],
            order_key=1,
        )
    ]
    _patch_pairwise_single_case(monkeypatch, strategy, analysis1, analysis2)
    strategy._solve_query_twostage = Mock(return_value=QueryResult(is_equivalent=True))

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert "pairwise_extra_assertions_by_pair" not in base_ctx
    strategy._solve_query_twostage.assert_not_called()


def _phi_circular_unknown(binary_id: str, entry: int, *, seq_time: int = 98) -> Expression:
    pcode_ref = PcodeOpRef(
        address_offset=entry + 0x1c,
        seq_time=seq_time,
        seq_order=0,
        block_index=0,
        mnemonic="MULTIEQUAL",
        input_sizes=(4, 4),
        output_size=4,
        binary_id=binary_id,
        function_entry_space="ram",
        function_entry_offset=entry,
        target_space="ram",
        target_offset=entry + 0x1c,
        opcode=60,
        local_op_ordinal=0,
    )
    return Expression.unknown(
        "phi_circular",
        runtime_ref=UnknownValueRef.phi_circular(pcode_op_ref=pcode_ref),
    ).clone_with(size=4)


def _analysis_with_phi_circular_guard(
    *,
    function_name: str,
    binary_id: str,
    entry: int,
    seq_time: int = 98,
    guard_negated: bool = False,
) -> FunctionReturnAnalysis:
    param = Expression.parameter("x", 0, size=4)
    phi_unknown = _phi_circular_unknown(binary_id, entry, seq_time=seq_time)
    guard = Condition(
        Expression.binary_op(
            "INT_SLESS",
            Expression.unary_op("INT_2COMP", phi_unknown),
            _const(0),
        ),
        guard_negated,
    )
    return FunctionReturnAnalysis(
        function_name=function_name,
        entry_point=hex(entry),
        function_ref=CallTargetRef.from_name(function_name, program_id=entry, entry_offset=entry),
        binary_id=binary_id,
        parameters=[_param("x")],
        returns=[ReturnInfo(address=hex(entry), value=param, conditions=[guard])],
        return_type="int",
        effect_summary=EffectSummary(parameter_names=["x"], effects=[]),
    )


def _patch_pairwise_return_cases_from_returns(monkeypatch, strategy, analysis1, analysis2):
    def cases_for(analysis):
        return [
            ReturnCase(
                index=index,
                conditions=list(ret.conditions or []),
                value_expr=ret.value,
                return_info=ret,
                return_type=analysis.return_type or "int",
                parameters=analysis.parameters,
            )
            for index, ret in enumerate(analysis.returns or [])
        ]

    monkeypatch.setattr(
        strategy,
        "_extract_return_cases",
        lambda analysis: cases_for(analysis1) if analysis.function_name == analysis1.function_name else cases_for(analysis2),
    )
    monkeypatch.setattr(strategy, "_prune_unreachable_cases", lambda cases, *_args, **_kwargs: cases)
    monkeypatch.setattr(strategy, "_cases_are_contradictory", lambda *_args, **_kwargs: False)
    monkeypatch.setattr(strategy, "_unresolved_return_coverage_unknown_reasons", lambda *_args, **_kwargs: [])


def test_unresolved_expression_action_status_marks_planned_without_stage_evidence():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    target = (
        "unresolved_expression",
        ("pair", "(0,1)"),
        (
            "unresolved_expression_side",
            "left",
            ("opaque_unknown", "phi_circular", "expr", "runtime", "multiequal_pcode_op", ("pcode_op", "B1")),
        ),
        (
            "unresolved_expression_side",
            "right",
            ("opaque_unknown", "phi_circular", "expr", "runtime", "multiequal_pcode_op", ("pcode_op", "B2")),
        ),
    )

    assert strategy._unresolved_expression_recovery_proof_obligations(target)
    assert (
        strategy._unresolved_expression_action_status(target, object_evidence=None)
        == UnknownRecoveryActionStatus.PLANNED
    )
    assert (
        strategy._unresolved_expression_action_status(
            target,
            object_evidence=("unresolved_expression_diagnostic_evidence",),
        )
        == UnknownRecoveryActionStatus.PENDING_PROOF
    )
    assert strategy._unresolved_expression_action_status(None, object_evidence=None) is None


def test_pairwise_phi_circular_guard_same_origin_stays_unknown_with_diagnostic_proof(monkeypatch):
    base_ctx = _base_context_for_single_int_param()
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = base_ctx
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_phi_circular_guard(
        function_name="func1",
        binary_id="B11",
        entry=0x1000,
    )
    analysis2 = _analysis_with_phi_circular_guard(
        function_name="func2",
        binary_id="B12",
        entry=0x1000,
    )
    _patch_pairwise_return_cases_from_returns(monkeypatch, strategy, analysis1, analysis2)
    strategy._solve_query_twostage = Mock(return_value=QueryResult(is_equivalent=True))
    strategy._solve_query_internal = Mock(return_value=QueryResult(is_equivalent=None))

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert [reason.reason_id for reason in result.unknown_reasons] == [
        UnknownReasonId.UNRESOLVED_EXPRESSION.value
    ]
    assert "pairwise_extra_assertions_by_pair" not in base_ctx
    assert "pairwise_unresolved_lowered_unknown_keys_by_pair" not in base_ctx
    reason = result.unknown_reasons[0]
    assert reason.object_evidence is not None
    assert reason.object_evidence[0] == "unresolved_expression_diagnostic_evidence"
    assert _nested_contains(reason.object_target_key, ("unresolved_location", "return_guard_unresolved"))
    assert _nested_contains(reason.object_target_key, ("unresolved_cause", "phi_circular_integer"))
    assert _nested_contains(reason.object_target_key, ("unresolved_substage", "integer_phi_circular_guard_pending"))
    assert any(
        isinstance(item, tuple) and item and item[0] == "stage_evidence"
        for item in reason.object_evidence
    )
    assert _nested_contains(reason.object_evidence, "semantic_recurrence_query")
    assert _nested_contains(reason.object_evidence, "object_derived_query_plan")
    actions = build_unknown_recovery_actions(result.unknown_reasons)
    assert {
        action.proof_stage
        for action in actions
        if action.reason_id == UnknownReasonId.UNRESOLVED_EXPRESSION.value
    } == {
        "phi_circular_guard_condition_lowering",
        "recursive_summary_guard_equivalence",
    }
    assert {
        action.status
        for action in actions
        if action.reason_id == UnknownReasonId.UNRESOLVED_EXPRESSION.value
    } == {UnknownRecoveryActionStatus.PENDING_PROOF.value}
    strategy._solve_query_twostage.assert_not_called()
    strategy._solve_query_internal.assert_not_called()


def test_pairwise_mixed_float_phi_unresolved_uses_generic_pending_lane():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    target = (
        "unresolved_expression",
        ("pair", "case0"),
        (
            "unresolved_expression_side",
            "left",
            ("function", "left"),
            ("return_storage", "reg", "v0"),
            ("return_case", 0),
            (
                "unresolved_locations",
                (
                    (
                        "unresolved_location",
                        "return_value",
                        (
                            "unresolved_classification",
                            ("location_scope", "return_value"),
                            ("unresolved_location", "return_value_unresolved"),
                            ("unresolved_cause", "mixed_float_call_read_recurrence"),
                            ("unresolved_substage", "mixed_float_call_read_recurrence_deferred"),
                            (
                                "unknown_refs",
                                (
                                    (
                                        "opaque_unknown",
                                        "phi_circular",
                                        "expr",
                                        "runtime",
                                        "multiequal_pcode_op",
                                        ("pcode_op", "B1"),
                                    ),
                                    (
                                        "unknown_runtime_ref",
                                        (
                                            "deferred_call",
                                            "call_out_of_scope",
                                            ("callee", "unknown"),
                                            ("callsite", "left"),
                                        ),
                                    ),
                                ),
                            ),
                        ),
                    ),
                ),
            ),
        ),
        (
            "unresolved_expression_side",
            "right",
            ("function", "right"),
            ("return_storage", "reg", "v0"),
            ("return_case", 0),
            (
                "unresolved_locations",
                (
                    (
                        "unresolved_location",
                        "return_value",
                        (
                            "unresolved_classification",
                            ("location_scope", "return_value"),
                            ("unresolved_location", "return_value_unresolved"),
                            ("unresolved_cause", "mixed_float_call_read_recurrence"),
                            ("unresolved_substage", "mixed_float_call_read_recurrence_deferred"),
                            (
                                "unknown_refs",
                                (
                                    (
                                        "opaque_unknown",
                                        "phi_circular",
                                        "expr",
                                        "runtime",
                                        "multiequal_pcode_op",
                                        ("pcode_op", "B2"),
                                    ),
                                    (
                                        "unknown_runtime_ref",
                                        (
                                            "deferred_call",
                                            "call_out_of_scope",
                                            ("callee", "unknown"),
                                            ("callsite", "right"),
                                        ),
                                    ),
                                ),
                            ),
                        ),
                    ),
                ),
            ),
        ),
    )

    obligations = strategy._unresolved_expression_recovery_proof_obligations(target)

    assert strategy._unresolved_expression_target_uses_generic_pending_census(target)
    assert obligations is not None
    assert {obligation.proof_stage for obligation in obligations} == {
        "typed_expression_lowering",
        "type_normalization",
    }
    evidence = strategy._unresolved_expression_generic_diagnostic_evidence(target)
    assert evidence is not None
    assert _nested_contains(evidence, ("diagnostic_rule", "mixed_float_call_read_recurrence_pending_census"))
    assert _nested_contains(evidence, ("completed_proof_allowed", False))


def test_pairwise_phi_circular_guard_solver_replay_does_not_recover_from_assumed_unknown_equality(monkeypatch):
    base_ctx = _base_context_for_single_int_param()
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = base_ctx
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_phi_circular_guard(
        function_name="func1",
        binary_id="B11",
        entry=0x1000,
    )
    analysis2 = _analysis_with_phi_circular_guard(
        function_name="func2",
        binary_id="B12",
        entry=0x1000,
    )
    _patch_pairwise_return_cases_from_returns(monkeypatch, strategy, analysis1, analysis2)
    strategy._solve_query_internal = Mock(
        side_effect=[
            QueryResult(is_equivalent=True),
            QueryResult(is_equivalent=True),
        ]
    )
    strategy._solve_query_twostage = Mock(return_value=QueryResult(is_equivalent=True))

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert [reason.reason_id for reason in result.unknown_reasons] == [
        UnknownReasonId.UNRESOLVED_EXPRESSION.value
    ]
    assert "pairwise_extra_assertions_by_pair" not in base_ctx
    assert "pairwise_unresolved_phi_circular_lowering_evidence_by_pair" not in base_ctx
    assert not _nested_contains(result.unknown_reasons[0].object_evidence, "completed_unresolved_expression_proof")
    assert _nested_contains(result.unknown_reasons[0].object_evidence, "object_derived_query_plan")
    assert analysis1.completed_recovery_proof_evidence == ()
    strategy._solve_query_internal.assert_not_called()
    strategy._solve_query_twostage.assert_not_called()


def test_pairwise_phi_circular_guard_solver_replay_sat_stays_unknown(monkeypatch):
    base_ctx = _base_context_for_single_int_param()
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = base_ctx
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_phi_circular_guard(
        function_name="func1",
        binary_id="B11",
        entry=0x1000,
    )
    analysis2 = _analysis_with_phi_circular_guard(
        function_name="func2",
        binary_id="B12",
        entry=0x1000,
    )
    _patch_pairwise_return_cases_from_returns(monkeypatch, strategy, analysis1, analysis2)
    strategy._solve_query_internal = Mock(
        side_effect=[
            QueryResult(is_equivalent=True),
            QueryResult(is_equivalent=False),
        ]
    )
    strategy._solve_query_twostage = Mock(return_value=QueryResult(is_equivalent=True))

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert [reason.reason_id for reason in result.unknown_reasons] == [
        UnknownReasonId.UNRESOLVED_EXPRESSION.value
    ]
    assert "pairwise_extra_assertions_by_pair" not in base_ctx
    assert analysis1.completed_recovery_proof_evidence == ()
    strategy._solve_query_twostage.assert_not_called()
    strategy._solve_query_internal.assert_not_called()


def test_pairwise_phi_circular_guard_polarity_mismatch_stays_unknown(monkeypatch):
    base_ctx = _base_context_for_single_int_param()
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = base_ctx
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_phi_circular_guard(
        function_name="func1",
        binary_id="B11",
        entry=0x1000,
        guard_negated=False,
    )
    analysis2 = _analysis_with_phi_circular_guard(
        function_name="func2",
        binary_id="B12",
        entry=0x1000,
        guard_negated=True,
    )
    _patch_pairwise_return_cases_from_returns(monkeypatch, strategy, analysis1, analysis2)
    strategy._solve_query_twostage = Mock(return_value=QueryResult(is_equivalent=True))
    strategy._solve_query_internal = Mock(return_value=QueryResult(is_equivalent=None))

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert [reason.reason_id for reason in result.unknown_reasons] == [
        UnknownReasonId.UNRESOLVED_EXPRESSION.value
    ]
    assert "pairwise_extra_assertions_by_pair" not in base_ctx
    strategy._solve_query_twostage.assert_not_called()


def test_pairwise_phi_circular_guard_overlap_does_not_prune_without_semantic_proof(monkeypatch):
    base_ctx = _base_context_for_single_int_param()
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = base_ctx
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_phi_circular_guard(
        function_name="func1",
        binary_id="B11",
        entry=0x1000,
        guard_negated=False,
    )
    analysis2 = _analysis_with_phi_circular_guard(
        function_name="func2",
        binary_id="B12",
        entry=0x1000,
        guard_negated=True,
    )
    _patch_pairwise_return_cases_from_returns(monkeypatch, strategy, analysis1, analysis2)
    strategy._solve_query_internal = Mock(return_value=QueryResult(is_equivalent=True))
    strategy._solve_query_twostage = Mock(return_value=QueryResult(is_equivalent=False))

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert [reason.reason_id for reason in result.unknown_reasons] == [
        UnknownReasonId.UNRESOLVED_EXPRESSION.value
    ]
    assert strategy._solve_query_internal.call_count == 0
    assert analysis1.completed_recovery_proof_evidence == ()
    strategy._solve_query_twostage.assert_not_called()


def test_pairwise_phi_circular_guard_origin_mismatch_stays_unknown(monkeypatch):
    base_ctx = _base_context_for_single_int_param()
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = base_ctx
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_phi_circular_guard(
        function_name="func1",
        binary_id="B11",
        entry=0x1000,
        seq_time=98,
    )
    analysis2 = _analysis_with_phi_circular_guard(
        function_name="func2",
        binary_id="B12",
        entry=0x1000,
        seq_time=99,
    )
    _patch_pairwise_return_cases_from_returns(monkeypatch, strategy, analysis1, analysis2)
    strategy._solve_query_twostage = Mock(return_value=QueryResult(is_equivalent=True))

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert [reason.reason_id for reason in result.unknown_reasons] == [
        UnknownReasonId.UNRESOLVED_EXPRESSION.value
    ]
    assert "pairwise_extra_assertions_by_pair" not in base_ctx
    strategy._solve_query_twostage.assert_not_called()


def test_pairwise_unresolved_deferred_call_incomplete_summary_stays_unknown(monkeypatch):
    base_ctx = _base_context_for_single_int_param()
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = base_ctx
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_deferred_call_argument_blocker(
        function_name="func1",
        binary_id="B1",
        entry=0x1000,
        return_deferred_unknown=True,
    )
    analysis2 = _analysis_with_deferred_call_argument_blocker(
        function_name="func2",
        binary_id="B14",
        entry=0x2000,
        return_deferred_unknown=True,
    )
    analysis2.effect_summary.incomplete_reasons = ("effect_summary_path_coverage_incomplete",)
    _patch_pairwise_single_case(monkeypatch, strategy, analysis1, analysis2)
    strategy._solve_query_twostage = Mock(return_value=QueryResult(is_equivalent=True))

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert "pairwise_extra_assertions_by_pair" not in base_ctx
    strategy._solve_query_twostage.assert_not_called()


def test_pairwise_deferred_call_duplicate_candidate_does_not_auto_proof(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_deferred_call_argument_blocker(
        function_name="func1",
        binary_id="B1",
        entry=0x1000,
        duplicate=True,
    )
    analysis2 = _analysis_with_deferred_call_argument_blocker(
        function_name="func2",
        binary_id="B14",
        entry=0x2000,
    )
    _patch_pairwise_single_unsat_case(monkeypatch, strategy, analysis1, analysis2)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.unknown_reasons
    assert not [
        item
        for analysis in (analysis1, analysis2)
        for item in analysis.completed_recovery_proof_evidence
        if item.get("proof_source") == "matched_deferred_call_argument_evidence"
    ]


def test_pairwise_deferred_call_weak_completed_evidence_does_not_recover(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_deferred_call_argument_blocker(
        function_name="func1",
        binary_id="B1",
        entry=0x1000,
    )
    analysis2 = _analysis_with_deferred_call_argument_blocker(
        function_name="func2",
        binary_id="B14",
        entry=0x2000,
    )
    reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:effect_call_argument_evidence_incomplete",
        analysis1,
        analysis2,
        stage="S_PAIRWISE",
    )
    analysis1.completed_recovery_proof_evidence = (
        _call_effect_summary_proof_evidence(
            object_target_key=reason.object_target_key,
            proof_obligation_id=reason.proof_obligation_id,
            proof_source="matched_deferred_call_argument_evidence",
            proof_content={
                "object_derived": True,
                "status": "complete",
                "proof_rule": "matched_deferred_call_argument_evidence",
                "object_target_key": reason.object_target_key,
                "call_effect_summary": {
                    "status": "complete",
                    "summary_source": ("effect_summary", "deferred_call"),
                    "evidence_kind": "call_effect_summary",
                    "object_target_key": reason.object_target_key,
                },
                "runtime_ref": {
                    "status": "complete",
                    "runtime_ref": PairwiseStrategy._expected_deferred_call_proof_content_refs(
                        reason.object_target_key
                    )[0],
                },
                "callsite_storage": {
                    "status": "complete",
                    "callsite_storage": PairwiseStrategy._expected_deferred_call_proof_content_refs(
                        reason.object_target_key
                    )[1],
                },
            },
        ),
    )
    _patch_pairwise_single_unsat_case(monkeypatch, strategy, analysis1, analysis2)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.unknown_reasons


def test_pairwise_deferred_call_empty_argument_completed_evidence_does_not_recover(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_deferred_call_argument_blocker(
        function_name="func1",
        binary_id="B1",
        entry=0x1000,
        argument_indices=(),
    )
    analysis2 = _analysis_with_deferred_call_argument_blocker(
        function_name="func2",
        binary_id="B14",
        entry=0x2000,
        argument_indices=(),
    )
    reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:effect_call_argument_evidence_incomplete",
        analysis1,
        analysis2,
        stage="S_PAIRWISE",
    )
    peer_reason = strategy._make_blocking_unsafety_unknown_reason(
        "function2:effect_call_argument_evidence_incomplete",
        analysis1,
        analysis2,
        stage="S_PAIRWISE",
    )
    runtime_ref, callsite_storage = PairwiseStrategy._expected_deferred_call_proof_content_refs(
        reason.object_target_key
    )
    peer_runtime_ref, peer_callsite_storage = PairwiseStrategy._expected_deferred_call_proof_content_refs(
        peer_reason.object_target_key
    )
    target_key = PairwiseStrategy._cross_binary_call_effect_component_key(
        PairwiseStrategy._deferred_call_target_expression_key(reason.object_target_key)
    )
    analysis1.completed_recovery_proof_evidence = (
        _call_effect_summary_proof_evidence(
            object_target_key=reason.object_target_key,
            proof_obligation_id=reason.proof_obligation_id,
            proof_source="matched_deferred_call_argument_evidence",
            proof_content={
                "object_derived": True,
                "status": "complete",
                "proof_rule": "matched_deferred_call_argument_evidence",
                "object_target_key": reason.object_target_key,
                "peer_object_target_key": peer_reason.object_target_key,
                "call_effect_summary": {
                    "status": "complete",
                    "summary_source": ("effect_summary", "deferred_call"),
                    "evidence_kind": "call_effect_summary",
                    "object_target_key": reason.object_target_key,
                    "peer_object_target_key": peer_reason.object_target_key,
                    "local_store_effect_count": 0,
                    "matching_local_deferred_call_count": 1,
                    "matching_peer_deferred_call_count": 1,
                },
                "runtime_ref": {
                    "status": "complete",
                    "runtime_ref": runtime_ref,
                    "peer_runtime_ref": peer_runtime_ref,
                    "matched_target_expression_key": target_key,
                },
                "callsite_storage": {
                    "status": "complete",
                    "callsite_storage": callsite_storage,
                    "peer_callsite_storage": peer_callsite_storage,
                    "matched_argument_keys": (),
                },
            },
        ),
    )
    _patch_pairwise_single_unsat_case(monkeypatch, strategy, analysis1, analysis2)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.unknown_reasons


def test_pairwise_incomplete_call_argument_evidence_does_not_auto_proof(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_effect_call_argument_evidence()
    complete_evidence = next(iter(analysis1.effect_summary.call_argument_evidence.values()))
    incomplete_evidence = CallArgumentEvidence(
        pcode_op_ref=complete_evidence.pcode_op_ref,
        target_ref=complete_evidence.target_ref,
        callee_param_identities=complete_evidence.callee_param_identities,
        arguments=(),
        sources=(),
        path_conditions=complete_evidence.path_conditions,
        coverage_complete=False,
        recovery_status=CallArgumentEvidence.RECOVERY_INCONCLUSIVE,
        reason="argument_recovery_inconclusive",
    )
    analysis1.effect_summary.call_argument_evidence = {
        complete_evidence.pcode_op_ref.stable_key(): incomplete_evidence,
    }
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x2000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=_const(1), conditions=[])],
        return_type="int",
    )
    _patch_pairwise_single_unsat_case(monkeypatch, strategy, analysis1, analysis2)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.unknown_reasons
    assert result.unknown_reasons[0].detail == "function1:effect_call_argument_evidence"
    assert not [
        item
        for item in analysis1.completed_recovery_proof_evidence
        if item.get("recovery_proof_kind") == UnknownRecoveryProofKind.CALL_EFFECT_SUMMARY_PROOF.value
    ]


def test_pairwise_bounded_call_argument_evidence_auto_records_phase15_proof(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_effect_call_argument_evidence()
    analysis1.analysis_notes.append("bounded_call_refinement_deferred_expanded")
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x2000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=_const(1), conditions=[])],
        return_type="int",
    )
    object_target_key = _blocking_unsafety_object_target_key(
        "function1:effect_call_argument_evidence",
        analysis1,
    )
    _attach_bounded_call_refinement_expansion_evidence(analysis1, object_target_key)
    _patch_pairwise_single_unsat_case(monkeypatch, strategy, analysis1, analysis2)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is True
    assert result.unknown_reasons == []
    evidence = [
        item
        for item in analysis1.completed_recovery_proof_evidence
        if item.get("proof_source") == "call_argument_evidence_phase15_complete"
    ]
    assert len(evidence) == 1
    content = evidence[0]["proof_content"]
    assert content["proof_rule"] == "call_argument_evidence_phase15_complete"
    assert content["callee_summary_completion"]["return_coverage_status"] == "complete"
    assert content["callee_precondition"]["abi_coercion"]["callee_parameter_interpretation"]
    assert content["argument_value_provenance"]["value_provenance_equivalent"] is True
    assert content["bounded_refinement"]["evidence_kind"] == "bounded_call_refinement_expansion"


def test_pairwise_bounded_call_argument_note_without_evidence_does_not_auto_proof(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_effect_call_argument_evidence()
    analysis1.analysis_notes.append("bounded_call_refinement_deferred_expanded")
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x2000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=_const(1), conditions=[])],
        return_type="int",
    )
    _patch_pairwise_single_unsat_case(monkeypatch, strategy, analysis1, analysis2)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.unknown_reasons
    assert not [
        item
        for item in analysis1.completed_recovery_proof_evidence
        if item.get("proof_source") == "call_argument_evidence_phase15_complete"
    ]


def test_call_argument_evidence_ignores_metadata_only_completed_proof():
    object_target_key = _blocking_unsafety_object_target_key(
        "function1:effect_call_argument_evidence",
        _analysis_with_effect_call_argument_evidence(),
    )
    evidence = _call_effect_summary_proof_evidence(object_target_key=object_target_key)

    assert _completed_proof_ids_for_call_effect_evidence(evidence) == ()


def test_call_argument_proof_rejects_unrelated_proof_content_sections():
    object_target_key = _blocking_unsafety_object_target_key(
        "function1:effect_call_argument_evidence",
        _analysis_with_effect_call_argument_evidence(),
    )
    evidence = _call_effect_summary_proof_evidence(object_target_key=object_target_key)
    evidence["proof_content"] = {
        "object_derived": True,
        "status": "complete",
        "proof_rule": "call_effect_object_evidence_complete",
        "object_target_key": object_target_key,
        "call_effect_summary": {"status": "complete", "foo": "bar"},
        "runtime_ref": {"status": "complete", "foo": "bar"},
        "callsite_storage": {"status": "complete", "foo": "bar"},
    }

    assert _completed_proof_ids_for_call_effect_evidence(evidence) == ()


def test_call_argument_proof_rejects_mismatched_runtime_ref_payload():
    object_target_key = _blocking_unsafety_object_target_key(
        "function1:effect_call_argument_evidence",
        _analysis_with_effect_call_argument_evidence(),
    )
    evidence = _complete_call_effect_summary_proof_evidence(object_target_key)
    evidence["proof_content"]["runtime_ref"]["runtime_ref"] = ("runtime_ref", "different-callsite")

    assert _completed_proof_ids_for_call_effect_evidence(evidence) == ()


def test_call_argument_proof_rejects_summary_without_target_kind_and_evidence_kind():
    object_target_key = _blocking_unsafety_object_target_key(
        "function1:effect_call_argument_evidence",
        _analysis_with_effect_call_argument_evidence(),
    )
    evidence = _complete_call_effect_summary_proof_evidence(object_target_key)
    evidence["proof_content"]["call_effect_summary"]["summary_source"] = (
        "effect_summary",
        "different_target",
    )
    evidence["proof_content"]["call_effect_summary"].pop("evidence_kind")

    assert _completed_proof_ids_for_call_effect_evidence(evidence) == ()


def test_call_argument_proof_rejects_missing_phase15_sections():
    object_target_key = _blocking_unsafety_object_target_key(
        "function1:effect_call_argument_evidence",
        _analysis_with_effect_call_argument_evidence(),
    )
    evidence = _complete_call_effect_summary_proof_evidence(object_target_key)
    evidence["proof_content"].pop("callee_summary_completion")

    assert _completed_proof_ids_for_call_effect_evidence(evidence) == ()


def test_call_argument_proof_rejects_abi_coercion_mismatch():
    object_target_key = _blocking_unsafety_object_target_key(
        "function1:effect_call_argument_evidence",
        _analysis_with_effect_call_argument_evidence(),
    )
    evidence = _complete_call_effect_summary_proof_evidence(object_target_key)
    evidence["proof_content"]["callee_precondition"]["abi_coercion"].pop(
        "callee_parameter_interpretation"
    )

    assert _completed_proof_ids_for_call_effect_evidence(evidence) == ()


def test_call_argument_proof_rejects_bounded_refinement_dependency_cycle():
    object_target_key = _blocking_unsafety_object_target_key(
        "function1:effect_call_argument_evidence",
        _analysis_with_effect_call_argument_evidence(),
    )
    evidence = _complete_call_effect_summary_proof_evidence(object_target_key)
    evidence["proof_content"]["bounded_refinement"]["dependency_cycle"] = True

    assert _completed_proof_ids_for_call_effect_evidence(evidence) == ()


def test_call_argument_proof_rejects_truncated_bounded_refinement():
    object_target_key = _blocking_unsafety_object_target_key(
        "function1:effect_call_argument_evidence",
        _analysis_with_effect_call_argument_evidence(),
    )
    evidence = _complete_call_effect_summary_proof_evidence(object_target_key)
    evidence["proof_content"]["bounded_refinement"]["truncated"] = True

    assert _completed_proof_ids_for_call_effect_evidence(evidence) == ()


def test_call_argument_proof_rejects_bounded_refinement_ref_mismatch():
    object_target_key = _blocking_unsafety_object_target_key(
        "function1:effect_call_argument_evidence",
        _analysis_with_effect_call_argument_evidence(),
    )
    evidence = _complete_call_effect_summary_proof_evidence(object_target_key)
    evidence["proof_content"]["callee_summary_completion"][
        "bounded_refinement_evidence_ref"
    ] = ("bounded_call_refinement_expansion", "different")

    assert _completed_proof_ids_for_call_effect_evidence(evidence) == ()


def test_call_argument_proof_rejects_bounded_refinement_partition_mismatch():
    object_target_key = _blocking_unsafety_object_target_key(
        "function1:effect_call_argument_evidence",
        _analysis_with_effect_call_argument_evidence(),
    )
    evidence = _complete_call_effect_summary_proof_evidence(object_target_key)
    evidence["proof_content"]["callee_summary_completion"][
        "callee_return_partition_key"
    ] = (("return", "different"),)

    assert _completed_proof_ids_for_call_effect_evidence(evidence) == ()


def test_call_argument_proof_rejects_summary_callee_without_completed_proof_ids():
    object_target_key = _blocking_unsafety_object_target_key(
        "function1:effect_call_argument_evidence",
        _analysis_with_effect_call_argument_evidence(),
    )
    evidence = _complete_call_effect_summary_proof_evidence(object_target_key)
    evidence["proof_content"]["bounded_refinement"][
        "callee_summary_requires_completed_proof"
    ] = True
    evidence["proof_content"]["bounded_refinement"]["callee_completed_proof_ids"] = ()
    evidence["proof_content"]["bounded_refinement"][
        "callee_completed_proof_evidence_ids"
    ] = ()

    assert _completed_proof_ids_for_call_effect_evidence(evidence) == ()


def test_pairwise_call_argument_evidence_recovers_with_matching_completed_proof(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_effect_call_argument_evidence()
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x2000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=_const(1), conditions=[])],
        return_type="int",
    )
    reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:effect_call_argument_evidence",
        analysis1,
        analysis2,
        stage="S_PAIRWISE",
    )
    analysis1.completed_recovery_proof_evidence = (
        _complete_call_effect_summary_proof_evidence(object_target_key=reason.object_target_key),
    )
    _patch_pairwise_single_unsat_case(monkeypatch, strategy, analysis1, analysis2)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is True
    assert result.unknown_reasons == []


def test_pairwise_preproducer_call_target_resolution_requires_pending_proof(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(
        formula_builder,
        solver_runner,
        debug=False,
        enable_completed_recovery_proofs=False,
    )
    analysis1 = _analysis_with_effect_call_target_resolution_evidence()
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x2000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=_const(1), conditions=[])],
        return_type="int",
    )
    _patch_pairwise_single_unsat_case(monkeypatch, strategy, analysis1, analysis2)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.unknown_reasons
    reason = result.unknown_reasons[0]
    assert reason.reason_id == UnknownReasonId.EQUIVALENCE_BLOCKING_UNSAFETY.value
    assert reason.action_status == UnknownRecoveryActionStatus.PENDING_PROOF.value
    assert reason.detail == "function1:effect_call_target_resolution_evidence"
    assert reason.object_target_key[0] == "call_target_resolution_evidence"
    assert _object_target_key_is_specific(reason.object_target_key) is True
    assert reason.proof_obligation_id == build_proof_obligation_id(
        reason.reason_id,
        reason.proof_stage,
        reason.recovery_proof_kind,
        reason.evidence_kind,
        reason.object_target_key,
    )
    assert reason.object_evidence == {
        "object_derived": True,
        "evidence_version": 1,
        "evidence_kind": "call_effect_summary",
        "blocker_reason": "function1:effect_call_target_resolution_evidence",
        "blocker_reason_kind": "effect_call_target_resolution_evidence",
        "object_target_kind": "call_target_resolution_evidence",
        "left_function": "func1",
        "right_function": "func2",
        "side": "function1",
        "analysis_key": reason.object_target_key[2],
        "runtime_ref": reason.object_target_key[3],
        "callsite_storage": reason.object_target_key[4],
        "resolution_kind": reason.object_target_key[5],
        "path_conditions": reason.object_target_key[6],
        "target_conditions": reason.object_target_key[7],
        "effect_ordinal": reason.object_target_key[8],
        "call_effect_summary_status": "target_resolution_pending_proof",
    }


def test_pairwise_call_target_resolution_requires_matching_completed_proof_by_default(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_effect_call_target_resolution_evidence()
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x2000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=_const(1), conditions=[])],
        return_type="int",
    )
    _patch_pairwise_single_unsat_case(monkeypatch, strategy, analysis1, analysis2)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.unknown_reasons
    assert result.unknown_reasons[0].detail == "function1:effect_call_target_resolution_evidence"


def test_pairwise_call_target_resolution_rejects_incomplete_completed_proof_content(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_effect_call_target_resolution_evidence()
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x2000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=_const(1), conditions=[])],
        return_type="int",
    )
    reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:effect_call_target_resolution_evidence",
        analysis1,
        analysis2,
        stage="S_PAIRWISE",
    )
    evidence = _complete_call_effect_summary_proof_evidence(
        object_target_key=reason.object_target_key,
    )
    evidence["proof_content"].pop("runtime_ref")
    analysis1.completed_recovery_proof_evidence = (evidence,)
    _patch_pairwise_single_unsat_case(monkeypatch, strategy, analysis1, analysis2)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.unknown_reasons
    assert result.unknown_reasons[0].detail == "function1:effect_call_target_resolution_evidence"


def test_call_target_resolution_proof_rejects_mismatched_callsite_storage_payload():
    object_target_key = _blocking_unsafety_object_target_key(
        "function1:effect_call_target_resolution_evidence",
        _analysis_with_effect_call_target_resolution_evidence(),
    )
    evidence = _complete_call_effect_summary_proof_evidence(object_target_key)
    evidence["proof_content"]["callsite_storage"]["callsite_storage"] = (
        "callsite_storage",
        "different-callsite",
    )

    assert _completed_proof_ids_for_call_effect_evidence(evidence) == ()


def test_pairwise_call_target_resolution_recovers_with_matching_completed_proof(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_effect_call_target_resolution_evidence()
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x2000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=_const(1), conditions=[])],
        return_type="int",
    )
    reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:effect_call_target_resolution_evidence",
        analysis1,
        analysis2,
        stage="S_PAIRWISE",
    )
    analysis1.completed_recovery_proof_evidence = (
        _complete_call_effect_summary_proof_evidence(object_target_key=reason.object_target_key),
    )
    _patch_pairwise_single_unsat_case(monkeypatch, strategy, analysis1, analysis2)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is True
    assert result.unknown_reasons == []


def test_pairwise_self_recursive_call_effect_proof_rejects_non_self_target(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_self_recursive_unsupported_call_effect(
        target_entry=0x2000,
        target_name="callee",
    )
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x3000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x3000", value=_const(1), conditions=[])],
        return_type="int",
    )
    _patch_pairwise_single_unsat_case(monkeypatch, strategy, analysis1, analysis2)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.unknown_reasons
    assert [
        item
        for item in analysis1.completed_recovery_proof_evidence
        if item.get("evidence_kind") == "call_effect_summary"
    ] == []


def test_pairwise_unknown_indirect_call_effect_proof_is_not_auto_completed(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_unsupported_call_effect()
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x2000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=_const(1), conditions=[])],
        return_type="int",
    )
    _patch_pairwise_single_unsat_case(monkeypatch, strategy, analysis1, analysis2)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.unknown_reasons
    assert [
        item
        for item in analysis1.completed_recovery_proof_evidence
        if item.get("evidence_kind") == "call_effect_summary"
    ] == []


def test_call_effect_summary_producer_emits_only_object_derived_full_ids():
    bare = _call_effect_summary_proof_evidence()
    evidence = _complete_call_effect_summary_proof_evidence(
        bare["object_target_key"],
        proof_obligation_id=bare["proof_obligation_id"],
    )
    analysis = FunctionReturnAnalysis(
        function_name="func1",
        entry_point="0x1000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1000", value=_const(1), conditions=[])],
        return_type="int",
        completed_recovery_proof_evidence=(evidence,),
    )

    proof_ids = PairwiseStrategy._completed_recovery_proof_ids(analysis)

    assert proof_ids == (_expected_call_effect_summary_proof_id(evidence),)


def test_call_effect_summary_producer_rejects_missing_unknown_indirect_target_expression():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    analysis1 = _analysis_with_unknown_indirect_call_effect(
        function_name="func1",
        binary_id="B10",
        entry=0x1000,
        target_expr_missing=True,
    )
    analysis2 = _analysis_with_unknown_indirect_call_effect(
        function_name="func2",
        binary_id="B11",
        entry=0x2000,
        target_expr_missing=True,
    )
    reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:unsupported_call_effect_summary",
        analysis1,
        analysis2,
        stage="S_PAIRWISE",
    )
    evidence = _complete_call_effect_summary_proof_evidence(
        reason.object_target_key,
        proof_obligation_id=reason.proof_obligation_id,
    )
    analysis1.completed_recovery_proof_evidence = (evidence,)

    assert PairwiseStrategy._completed_call_effect_summary_proof_ids(analysis1, analysis2) == ()
    assert strategy._call_effect_summary_proof_is_complete(reason, analysis1, analysis2) is False


def test_call_effect_summary_producer_rejects_missing_full_proof_id():
    evidence = _call_effect_summary_proof_evidence()
    evidence.pop("proof_obligation_id", None)
    analysis = FunctionReturnAnalysis(
        function_name="func1",
        entry_point="0x1000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1000", value=_const(1), conditions=[])],
        return_type="int",
        completed_recovery_proof_evidence=(evidence,),
    )

    assert PairwiseStrategy._completed_recovery_proof_ids(analysis) == ()


def test_call_effect_summary_producer_rejects_non_object_derived_evidence():
    analysis = _analysis_with_call_effect_summary_proof_evidence(object_derived=False)

    assert PairwiseStrategy._completed_recovery_proof_ids(analysis) == ()


def test_call_effect_summary_producer_rejects_mismatched_full_proof_id():
    evidence = _call_effect_summary_proof_evidence()
    wrong_id = build_proof_obligation_id(
        UnknownReasonId.EQUIVALENCE_BLOCKING_UNSAFETY.value,
        evidence["proof_stage"],
        evidence["recovery_proof_kind"],
        evidence["evidence_kind"],
        ("unsupported_call_effect", "different-callsite"),
    )
    analysis = _analysis_with_call_effect_summary_proof_evidence(
        proof_obligation_id=wrong_id,
    )

    assert PairwiseStrategy._completed_recovery_proof_ids(analysis) == ()


def test_call_effect_summary_producer_rejects_active_safety_blockers():
    coverage_blocked = _analysis_with_call_effect_summary_proof_evidence()
    coverage_blocked.analysis_notes.append("return_case_coverage_gap")
    sat_blocked = _analysis_with_call_effect_summary_proof_evidence()
    sat_blocked.analysis_notes.append("indirect_control_flow_unresolved")
    unsupported_blocked = _analysis_with_call_effect_summary_proof_evidence(
        unsupported_effect_reasons=("target_identity_unavailable",),
    )

    assert PairwiseStrategy._completed_recovery_proof_ids(coverage_blocked) == ()
    assert PairwiseStrategy._completed_recovery_proof_ids(sat_blocked) == ()
    assert PairwiseStrategy._completed_recovery_proof_ids(unsupported_blocked) == ()


def test_call_effect_summary_reason_accepts_targeted_clean_proof_with_analysis_blocker():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    analysis1 = _analysis_with_unsupported_call_effect()
    analysis2 = _analysis_with_unsupported_call_effect()
    analysis1.analysis_notes.append("indirect_control_flow_unresolved")
    reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:unsupported_call_effect_summary",
        analysis1,
        analysis2,
        stage="S_PAIRWISE",
    )
    evidence = _complete_call_effect_summary_proof_evidence(
        reason.object_target_key,
        proof_obligation_id=reason.proof_obligation_id,
    )
    analysis1.completed_recovery_proof_evidence = (evidence,)

    assert PairwiseStrategy._completed_recovery_proof_ids(analysis1, analysis2) == ()
    assert strategy._call_effect_summary_proof_is_complete(reason, analysis1, analysis2) is True


def _readonly_identity_target():
    return (
        "readonly_identity",
        ("pair", "(0,0)"),
        (
            "readonly_identity_side",
            "left",
            ("function_ref", ("function", "B10", 0x1000)),
            ("readonly_return_case_partition_member", 0, (0,), ("return_case", 0, "0x1000", ("pcode_op",), "0x1000:return", 1), ("comparison_surface", "return_value", 32, None), ("value", ("readonly_value", "left")), ("guards", ())),
            ("readonly_reduction_ref", "memory_sum"),
            ("guards", ()),
            ("value", ("readonly_value", "left")),
        ),
        (
            "readonly_identity_side",
            "right",
            ("function_ref", ("function", "B13", 0x2000)),
            ("readonly_return_case_partition_member", 0, (0,), ("return_case", 0, "0x2000", ("pcode_op",), "0x2000:return", 1), ("comparison_surface", "return_value", 32, None), ("value", ("readonly_value", "right")), ("guards", ())),
            ("readonly_reduction_ref", "memory_sum"),
            ("guards", ()),
            ("value", ("readonly_value", "right")),
        ),
        (
            "readonly_identity_relation",
            ("shared_count_identities", (("parameter", 1),)),
            (
                "count_storage_relation",
                (
                    "same_register_base_projection",
                    ("base", (-1, 12756, 64)),
                    ("left_bits", 0, 64),
                    ("right_bits", 32, 32),
                    ("projection", "left_contains_right"),
                ),
            ),
        ),
    )


def _method_b_closure_target():
    method_b_term_contract = (
        "readonly_reduction_term_sequence_contract",
        "memory_sum",
        ("parameter", 0),
        ("parameter_storage", ("register_storage", -1, 12756, 64, 32, 32)),
        ("loop_limit_parameter", 1),
        4,
        0,
        2,
        0,
        4,
        True,
        (),
        (32, 0),
        ("loop_side_effect_profile", "pure_memory_read", True, False),
    )
    method_b_summary_profile = (
        "method_b_summary_profile",
        (
            "runtime_ref",
            (
                "readonly_reduction_proof_semantic",
                "memory_sum",
                ("parameter", 0),
                ("parameter_storage", ("register_storage", -1, 12756, 64, 32, 32)),
                4,
                (32, 0),
                method_b_term_contract,
            ),
        ),
        (
            "loop_summary",
            (
                "loop_summary_method_b",
                "scalar_element_index",
                0,
                ("loop_limit_parameter", 1),
                2,
                ("scalar_memory_term_sequence", "sum", ("parameter", 0), 0, 4, 4, 4),
                (),
                (32, 0),
                ("loop_side_effect_profile", "pure_memory_read", True, False),
            ),
        ),
        ("term_contract", method_b_term_contract),
        (
            "count_identities",
            (
                ("parameter", 1),
                ("parameter_storage", ("register_storage", -1, 12756, 64, 32, 32)),
            ),
        ),
    )
    return (
        "method_b_closure",
        ("pair", "(0,0)"),
        (
            "method_b_closure_side",
            "left",
            ("function_ref", ("function", "B10", 0x1000)),
            ("readonly_return_case_partition_member", 0, (0,), ("return_case", 0, "0x1000", ("pcode_op",), "0x1000:return", 1), ("comparison_surface", "return_value", 32, None), ("value", ("expression", "sum")), ("guards", ())),
            ("loop_value", ("method_b_loop_value", None, None, ("expression", "sum"))),
            ("guards", ()),
        ),
        (
            "method_b_closure_side",
            "right",
            ("function_ref", ("function", "B13", 0x2000)),
            ("readonly_return_case_partition_member", 0, (0,), ("return_case", 0, "0x2000", ("pcode_op",), "0x2000:return", 1), ("comparison_surface", "return_value", 32, None), ("value", ("runtime_ref", "summary")), ("guards", ())),
            ("loop_value", ("method_b_loop_value", ("runtime_ref", "summary"), ("loop_summary", "summary"), ("runtime_ref", "summary"))),
            ("guards", ()),
        ),
        (
            "method_b_closure_relation",
            ("kind", "one_sided_summary"),
            ("summary_side", "right"),
            ("exact_side", "left"),
            ("summary", method_b_summary_profile),
            ("exact_terms", (("readonly_reduction_term", 0, 4), ("readonly_reduction_term", 8, 4))),
            ("exact_constant_bias", 0),
        ),
    )


def _analysis_with_completed_evidence(*evidence_items):
    return FunctionReturnAnalysis(
        function_name="func1",
        entry_point="0x1000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1000", value=_const(1), conditions=[])],
        return_type="int",
        completed_recovery_proof_evidence=tuple(evidence_items),
    )


def _readonly_identity_reason(target=None):
    return make_unknown_reason(
        UnknownReasonId.READONLY_IDENTITY_MISSING,
        stage="S_PAIRWISE",
        pair_or_case="(0,0)",
        evidence_refs=("loop_summary_shape_mismatch",),
        evidence_kind="object_storage_identity",
        object_target_key=target or _readonly_identity_target(),
    )


def _readonly_identity_evidence(action, **overrides):
    storage_relation = None
    if len(action.object_target_key) == 5:
        relation = action.object_target_key[4]
        if (
            isinstance(relation, tuple)
            and len(relation) == 3
            and isinstance(relation[2], tuple)
            and len(relation[2]) == 2
            and relation[2][0] == "count_storage_relation"
        ):
            storage_relation = relation[2][1]
    proof_content = {
        "object_derived": True,
        "object_target_key": action.object_target_key,
        "left_side": action.object_target_key[2],
        "right_side": action.object_target_key[3],
        "object_storage_identity": "matched",
        "count_identity": "matched",
        "guard_implication": "proven",
        "finite_witness": "checked",
    }
    if (
        isinstance(storage_relation, tuple)
        and storage_relation
        and storage_relation[0] == "same_register_base_projection"
    ):
        proof_content.update(
            {
                "storage_relation": storage_relation,
                "parameter_extension": {
                    "object_derived": True,
                    "status": "proven",
                    "relation": "same_register_base_projection_semantic_extension",
                    "projection_relation": storage_relation,
                    "wide_side": "left",
                    "narrow_side": "right",
                    "parameter_index": 1,
                    "signedness": "signed",
                    "narrow_bits": 32,
                    "wide_bits": 64,
                    "extension": "sign_extend",
                    "proof_source": "param_semantic_hint",
                },
            }
        )
    evidence = {
        "object_derived": True,
        "status": "complete",
        "reason_id": UnknownReasonId.READONLY_IDENTITY_MISSING.value,
        "proof_kind": action.proof_kind,
        "recovery_proof_kind": action.proof_kind,
        "proof_stage": action.proof_stage,
        "evidence_kind": action.evidence_kind,
        "required_evidence": tuple(action.required_evidence),
        "object_target_key": action.object_target_key,
        "proof_obligation_id": action.proof_obligation_id,
        "proof_content": proof_content,
    }
    evidence.update(overrides)
    return evidence


def _method_b_reason(target=None):
    return make_unknown_reason(
        UnknownReasonId.METHOD_B_CLOSURE_BLOCKED,
        stage="S_PAIRWISE",
        pair_or_case="(0,0)",
        evidence_refs=("loop_summary_guard_mismatch",),
        object_target_key=target or _method_b_closure_target(),
    )


def _method_b_relation_field(target, field_name, default=None):
    try:
        relation = target[4]
        for item in relation[1:]:
            if isinstance(item, tuple) and len(item) >= 2 and item[0] == field_name:
                return item[1]
    except (IndexError, TypeError):
        return default
    return default


def _method_b_evidence(action, **overrides):
    proof_content = {
        "object_derived": True,
        "object_target_key": action.object_target_key,
    }
    exact_side = _method_b_relation_field(action.object_target_key, "exact_side", "left")
    summary_side = _method_b_relation_field(action.object_target_key, "summary_side", "right")
    exact_terms = _method_b_relation_field(action.object_target_key, "exact_terms", ())
    constant_bias = _method_b_relation_field(action.object_target_key, "exact_constant_bias", 0)
    if action.proof_stage == "method_b_covering_case":
        proof_content.update(
            {
                "seed_compensation": "proven",
                "term_sequence": "matched",
                "pure_side_effect_profile": "proven",
                "exact_side": exact_side,
                "summary_side": summary_side,
                "count_value": 2,
                "exact_terms": exact_terms,
                "expected_terms": exact_terms,
                "constant_bias": constant_bias,
                "result_size": 4,
                "covering_evidence": "method_b_covering_materialized_terms",
            }
        )
    elif action.proof_stage == "method_b_guard_partition":
        proof_content.update(
            {
                "guard_partition": "proven",
                "partition_coverage_proof": "covered",
                "exact_side": exact_side,
                "summary_side": summary_side,
                "count_value": 2,
                "count_values": (2,),
                "guard_evidence": "reduction_count_implication",
            }
        )
    evidence = {
        "object_derived": True,
        "status": "complete",
        "reason_id": UnknownReasonId.METHOD_B_CLOSURE_BLOCKED.value,
        "proof_kind": action.proof_kind,
        "recovery_proof_kind": action.proof_kind,
        "proof_stage": action.proof_stage,
        "evidence_kind": action.evidence_kind,
        "required_evidence": tuple(action.required_evidence),
        "object_target_key": action.object_target_key,
        "proof_obligation_id": action.proof_obligation_id,
        "proof_content": proof_content,
    }
    evidence.update(overrides)
    return evidence


def test_readonly_identity_completed_evidence_connects_to_recovery_gate():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    reason = _readonly_identity_reason()
    action = build_unknown_recovery_actions([reason])[0]
    evidence = _readonly_identity_evidence(action)
    analysis1 = _analysis_with_completed_evidence(evidence)
    analysis2 = _analysis_with_completed_evidence()

    assert PairwiseStrategy._completed_recovery_proof_ids(analysis1) == (reason.proof_obligation_id,)
    assert strategy._readonly_identity_proof_is_complete(reason, analysis1, analysis2) is True


def test_readonly_identity_completed_evidence_rejects_relationless_target():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    relationless_target = _readonly_identity_target()[:4]
    reason = _readonly_identity_reason(target=relationless_target)
    action = build_unknown_recovery_actions([reason])[0]
    evidence = _readonly_identity_evidence(action)
    analysis1 = _analysis_with_completed_evidence(evidence)
    analysis2 = _analysis_with_completed_evidence()

    assert PairwiseStrategy._completed_recovery_proof_ids(analysis1) == ()
    assert strategy._readonly_identity_proof_is_complete(reason, analysis1, analysis2) is False


def test_readonly_identity_completed_evidence_rejects_missing_relation_marker():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    weak_target = (*_readonly_identity_target()[:4], ("readonly_identity_relation", ("kind", "missing_readonly_ref")))
    reason = _readonly_identity_reason(target=weak_target)
    action = build_unknown_recovery_actions([reason])[0]
    evidence = _readonly_identity_evidence(action)
    analysis1 = _analysis_with_completed_evidence(evidence)
    analysis2 = _analysis_with_completed_evidence()

    assert PairwiseStrategy._completed_recovery_proof_ids(analysis1) == ()
    assert strategy._readonly_identity_proof_is_complete(reason, analysis1, analysis2) is False


def test_readonly_identity_completed_evidence_rejects_malformed_storage_relation():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    malformed_target = (
        *_readonly_identity_target()[:4],
        (
            "readonly_identity_relation",
            ("shared_count_identities", (("parameter", 1),)),
            (
                "count_storage_relation",
                (
                    "same_register_base_projection",
                    ("base", (-1, 12756, 64)),
                    ("left_bits", 0, 64),
                ),
            ),
        ),
    )
    reason = _readonly_identity_reason(target=malformed_target)
    action = build_unknown_recovery_actions([reason])[0]
    evidence = _readonly_identity_evidence(action)
    analysis1 = _analysis_with_completed_evidence(evidence)
    analysis2 = _analysis_with_completed_evidence()

    assert PairwiseStrategy._completed_recovery_proof_ids(analysis1) == ()
    assert strategy._readonly_identity_proof_is_complete(reason, analysis1, analysis2) is False


def test_readonly_identity_completed_evidence_rejects_missing_side_payload():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    reason = _readonly_identity_reason()
    action = build_unknown_recovery_actions([reason])[0]
    evidence = _readonly_identity_evidence(action)
    evidence["proof_content"].pop("left_side")
    analysis1 = _analysis_with_completed_evidence(evidence)
    analysis2 = _analysis_with_completed_evidence()

    assert PairwiseStrategy._completed_recovery_proof_ids(analysis1) == ()
    assert strategy._readonly_identity_proof_is_complete(reason, analysis1, analysis2) is False


def test_readonly_identity_completed_evidence_rejects_projection_without_extension_payload():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    reason = _readonly_identity_reason()
    action = build_unknown_recovery_actions([reason])[0]
    evidence = _readonly_identity_evidence(action)
    evidence["proof_content"].pop("parameter_extension")
    analysis1 = _analysis_with_completed_evidence(evidence)
    analysis2 = _analysis_with_completed_evidence()

    assert PairwiseStrategy._completed_recovery_proof_ids(analysis1) == ()
    assert strategy._readonly_identity_proof_is_complete(reason, analysis1, analysis2) is False


def test_method_b_closure_requires_both_completed_actions_for_recovery_gate():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    reason = _method_b_reason()
    actions = build_unknown_recovery_actions([reason])
    covering_evidence = _method_b_evidence(actions[0])
    guard_evidence = _method_b_evidence(actions[1])
    analysis2 = _analysis_with_completed_evidence()

    partial = _analysis_with_completed_evidence(covering_evidence)
    assert strategy._method_b_closure_proof_is_complete(reason, partial, analysis2) is False

    complete = _analysis_with_completed_evidence(covering_evidence, guard_evidence)
    assert PairwiseStrategy._completed_recovery_proof_ids(complete) == tuple(
        action.proof_obligation_id for action in actions
    )
    assert strategy._method_b_closure_proof_is_complete(reason, complete, analysis2) is True


def test_method_b_closure_completed_evidence_rejects_status_only_payload():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    reason = _method_b_reason()
    actions = build_unknown_recovery_actions([reason])
    evidence = [_method_b_evidence(action) for action in actions]
    for item in evidence:
        content = item["proof_content"]
        item["proof_content"] = {
            key: content[key]
            for key in (
                "object_derived",
                "object_target_key",
                "seed_compensation",
                "term_sequence",
                "pure_side_effect_profile",
                "guard_partition",
                "partition_coverage_proof",
            )
            if key in content
        }
    analysis1 = _analysis_with_completed_evidence(*evidence)
    analysis2 = _analysis_with_completed_evidence()

    assert PairwiseStrategy._completed_recovery_proof_ids(analysis1) == ()
    assert strategy._method_b_closure_proof_is_complete(reason, analysis1, analysis2) is False


def test_method_b_closure_completed_evidence_rejects_term_payload_mismatch():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    reason = _method_b_reason()
    actions = build_unknown_recovery_actions([reason])
    covering_evidence = _method_b_evidence(actions[0])
    guard_evidence = _method_b_evidence(actions[1])
    covering_evidence["proof_content"]["exact_terms"] = (("readonly_reduction_term", 0, 4),)
    analysis1 = _analysis_with_completed_evidence(covering_evidence, guard_evidence)
    analysis2 = _analysis_with_completed_evidence()

    assert PairwiseStrategy._completed_recovery_proof_ids(analysis1) == (actions[1].proof_obligation_id,)
    assert strategy._method_b_closure_proof_is_complete(reason, analysis1, analysis2) is False


def test_method_b_closure_completed_evidence_rejects_side_payload_mismatch():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    reason = _method_b_reason()
    actions = build_unknown_recovery_actions([reason])
    covering_evidence = _method_b_evidence(actions[0])
    guard_evidence = _method_b_evidence(actions[1])
    covering_evidence["proof_content"]["summary_side"] = "left"
    analysis1 = _analysis_with_completed_evidence(covering_evidence, guard_evidence)
    analysis2 = _analysis_with_completed_evidence()

    assert PairwiseStrategy._completed_recovery_proof_ids(analysis1) == (actions[1].proof_obligation_id,)
    assert strategy._method_b_closure_proof_is_complete(reason, analysis1, analysis2) is False


def test_method_b_closure_completed_evidence_accepts_count_membership_payload():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    reason = _method_b_reason()
    actions = build_unknown_recovery_actions([reason])
    covering_evidence = _method_b_evidence(actions[0])
    guard_evidence = _method_b_evidence(actions[1])
    guard_evidence["proof_content"]["count_value"] = 3
    guard_evidence["proof_content"]["count_values"] = (3, 4)
    guard_evidence["proof_content"]["guard_evidence"] = "reduction_count_membership_implication"
    analysis1 = _analysis_with_completed_evidence(covering_evidence, guard_evidence)
    analysis2 = _analysis_with_completed_evidence()

    assert PairwiseStrategy._completed_recovery_proof_ids(analysis1) == tuple(
        action.proof_obligation_id for action in actions
    )
    assert strategy._method_b_closure_proof_is_complete(reason, analysis1, analysis2) is True


def test_method_b_closure_completed_evidence_rejects_count_value_outside_membership_payload():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    reason = _method_b_reason()
    actions = build_unknown_recovery_actions([reason])
    covering_evidence = _method_b_evidence(actions[0])
    guard_evidence = _method_b_evidence(actions[1])
    guard_evidence["proof_content"]["count_value"] = 2
    guard_evidence["proof_content"]["count_values"] = (3, 4)
    guard_evidence["proof_content"]["guard_evidence"] = "reduction_count_membership_implication"
    analysis1 = _analysis_with_completed_evidence(covering_evidence, guard_evidence)
    analysis2 = _analysis_with_completed_evidence()

    assert PairwiseStrategy._completed_recovery_proof_ids(analysis1) == (actions[0].proof_obligation_id,)
    assert strategy._method_b_closure_proof_is_complete(reason, analysis1, analysis2) is False


def test_method_b_closure_completed_evidence_rejects_relationless_target():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    relationless_target = _method_b_closure_target()[:4]
    reason = _method_b_reason(target=relationless_target)
    actions = build_unknown_recovery_actions([reason])
    evidence = tuple(_method_b_evidence(action) for action in actions)
    analysis1 = _analysis_with_completed_evidence(*evidence)
    analysis2 = _analysis_with_completed_evidence()

    assert PairwiseStrategy._completed_recovery_proof_ids(analysis1) == ()
    assert strategy._method_b_closure_proof_is_complete(reason, analysis1, analysis2) is False


def test_method_b_closure_completed_evidence_rejects_missing_summary_relation():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    weak_target = (*_method_b_closure_target()[:4], ("method_b_closure_relation", ("kind", "missing_method_b_summary")))
    reason = _method_b_reason(target=weak_target)
    actions = build_unknown_recovery_actions([reason])
    evidence = tuple(_method_b_evidence(action) for action in actions)
    analysis1 = _analysis_with_completed_evidence(*evidence)
    analysis2 = _analysis_with_completed_evidence()

    assert PairwiseStrategy._completed_recovery_proof_ids(analysis1) == ()
    assert strategy._method_b_closure_proof_is_complete(reason, analysis1, analysis2) is False


def test_method_b_closure_completed_evidence_rejects_weak_summary_profile():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    weak_target = (
        *_method_b_closure_target()[:4],
        (
            "method_b_closure_relation",
            ("kind", "one_sided_summary"),
            ("summary_side", "right"),
            ("exact_side", "left"),
            ("summary", ("method_b_summary_profile", ("runtime_ref", "summary"))),
            ("exact_terms", (("readonly_reduction_term", 0, 4), ("readonly_reduction_term", 8, 4))),
            ("exact_constant_bias", 0),
        ),
    )
    reason = _method_b_reason(target=weak_target)
    actions = build_unknown_recovery_actions([reason])
    evidence = tuple(_method_b_evidence(action) for action in actions)
    analysis1 = _analysis_with_completed_evidence(*evidence)
    analysis2 = _analysis_with_completed_evidence()

    assert PairwiseStrategy._completed_recovery_proof_ids(analysis1) == ()
    assert strategy._method_b_closure_proof_is_complete(reason, analysis1, analysis2) is False


def test_monolithic_strategy_downgrades_sat_when_return_cases_leave_coverage_gap():
    class _CoverageGapSolverRunner:
        def __init__(self):
            self.timeout = 5

        def run_parallel(self, _query: str):
            return ParallelResult(
                results=[SolverResult("fake", SolverStatus.SAT, model={"x_1": 7, "x_2": 7})]
            )

        def run_sequential(self, query: str):
            if "Return coverage gap query: function1" in query:
                return ParallelResult(
                    results=[SolverResult("fake", SolverStatus.SAT, model={"x_1": 7, "x_2": 7})]
                )
            return ParallelResult(results=[SolverResult("fake", SolverStatus.UNSAT)])

    x1 = Expression.parameter("x", 0, size=4)
    x2 = Expression.parameter("x", 0, size=4)
    analysis1 = FunctionReturnAnalysis(
        function_name="func1",
        entry_point="0x1",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1", value=_const(1), conditions=[_eq(x1, _const(0))])],
        return_type="int",
    )
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x2",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2", value=x2, conditions=[])],
        return_type="int",
    )

    params1 = [ParameterInfo(original_name="x", smt_name="x_1", bit_width=32, index=0)]
    params2 = [ParameterInfo(original_name="x", smt_name="x_2", bit_width=32, index=0)]
    formula_builder = Mock()
    formula_builder.build_equivalence_formula_extended.return_value = FormulaBuilderResult(
        formula="(set-logic QF_BV)\n(check-sat)",
        return_var1="return_1",
        return_var2="return_2",
        constrained_fragments=[],
        extra_vars1=[],
        extra_vars2=[],
        param_fragment_constrained=[],
    )
    formula_builder.build_base_context.return_value = {
        "header_lines": [
            "(declare-const x_1 (_ BitVec 32))",
            "(declare-const x_2 (_ BitVec 32))",
            "(assert (= x_1 x_2))",
        ],
        "params1": params1,
        "params2": params2,
        "extra_vars1": [],
        "extra_vars2": [],
        "constrained_fragments": [],
        "return_size1": 32,
        "return_size2": 32,
    }

    strategy = MonolithicStrategy(formula_builder, _CoverageGapSolverRunner(), debug=False)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.counterexample_raw is None


def test_monolithic_strategy_does_not_accept_unsat_with_return_coverage_gap():
    class _CoverageGapUnsatSolverRunner:
        def __init__(self):
            self.timeout = 5

        def run_parallel(self, _query: str):
            return ParallelResult(results=[SolverResult("fake", SolverStatus.UNSAT)])

        def run_sequential(self, query: str):
            if "Return coverage gap query: function1" in query:
                return ParallelResult(
                    results=[SolverResult("fake", SolverStatus.SAT, model={"x_1": 7, "x_2": 7})]
                )
            return ParallelResult(results=[SolverResult("fake", SolverStatus.UNSAT)])

    x1 = Expression.parameter("x", 0, size=4)
    x2 = Expression.parameter("x", 0, size=4)
    analysis1 = FunctionReturnAnalysis(
        function_name="func1",
        entry_point="0x1",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1", value=_const(1), conditions=[_eq(x1, _const(0))])],
        return_type="int",
    )
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x2",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2", value=x2, conditions=[])],
        return_type="int",
    )

    params1 = [ParameterInfo(original_name="x", smt_name="x_1", bit_width=32, index=0)]
    params2 = [ParameterInfo(original_name="x", smt_name="x_2", bit_width=32, index=0)]
    formula_builder = Mock()
    formula_builder.build_equivalence_formula_extended.return_value = FormulaBuilderResult(
        formula="(set-logic QF_BV)\n(check-sat)",
        return_var1="return_1",
        return_var2="return_2",
        constrained_fragments=[],
        extra_vars1=[],
        extra_vars2=[],
        param_fragment_constrained=[],
    )
    formula_builder.build_base_context.return_value = {
        "header_lines": [
            "(declare-const x_1 (_ BitVec 32))",
            "(declare-const x_2 (_ BitVec 32))",
            "(assert (= x_1 x_2))",
        ],
        "params1": params1,
        "params2": params2,
        "extra_vars1": [],
        "extra_vars2": [],
        "constrained_fragments": [],
        "return_size1": 32,
        "return_size2": 32,
    }

    strategy = MonolithicStrategy(formula_builder, _CoverageGapUnsatSolverRunner(), debug=False)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.counterexample_raw is None
    assert "return_case_coverage_gap" in analysis1.analysis_notes
    assert result.unknown_reasons[0].reason_id == UnknownReasonId.RETURN_COVERAGE_GAP.value
    assert result.unknown_reasons[0].stage == "S_MONOLITHIC_FALLBACK"
    assert result.unknown_reasons[0].action_status == UnknownRecoveryActionStatus.PENDING_PROOF.value
    assert result.unknown_reasons[0].recovery_action == "return_coverage_proof_required"
    assert result.unknown_reasons[0].object_target_key[0] == "return_coverage"
    actions = build_unknown_recovery_actions(result.unknown_reasons)
    assert {action.status for action in actions} == {UnknownRecoveryActionStatus.PENDING_PROOF.value}
    assert all(action.proof_obligation_id is not None for action in actions)


def test_monolithic_return_coverage_gap_completed_proofs_allow_equivalent():
    strategy, analysis1, analysis2 = _monolithic_return_coverage_gap_setup()
    completed_reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:return_coverage_gap",
        analysis1,
        analysis2,
        stage="S_MONOLITHIC_FALLBACK",
    )
    actions = build_unknown_recovery_actions([completed_reason])
    analysis1.completed_recovery_proof_evidence = tuple(
        _return_coverage_completion_evidence(action)
        for action in actions
    )

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is True
    assert result.unknown_reasons == []
    assert result.counterexample_raw is None


def test_monolithic_return_coverage_gap_missing_completed_proof_id_does_not_recover():
    strategy, analysis1, analysis2 = _monolithic_return_coverage_gap_setup()
    completed_reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:return_coverage_gap",
        analysis1,
        analysis2,
        stage="S_MONOLITHIC_FALLBACK",
    )
    actions = build_unknown_recovery_actions([completed_reason])
    analysis1.completed_recovery_proof_evidence = tuple(
        _return_coverage_completion_evidence_without_proof_id(action)
        for action in actions
    )

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.unknown_reasons
    assert result.unknown_reasons[0].reason_id == UnknownReasonId.RETURN_COVERAGE_GAP.value
    assert result.unknown_reasons[0].action_status == UnknownRecoveryActionStatus.PENDING_PROOF.value
    assert result.counterexample_raw is None


def test_monolithic_strategy_does_not_accept_unsat_with_incomplete_effect_summary():
    class _UnsatSolverRunner:
        def __init__(self):
            self.timeout = 5

        def run_parallel(self, _query: str):
            return ParallelResult(results=[SolverResult("fake", SolverStatus.UNSAT)])

        def run_sequential(self, _query: str):
            return ParallelResult(results=[SolverResult("fake", SolverStatus.UNSAT)])

    analysis1 = FunctionReturnAnalysis(
        function_name="func1",
        entry_point="0x1",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1", value=_const(1), conditions=[])],
        return_type="int",
        effect_summary=EffectSummary(
            parameter_names=["x"],
            effects=[],
            has_unsupported_call=True,
            incomplete_reasons=("effect_summary_path_coverage_incomplete",),
        ),
    )
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x2",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2", value=_const(1), conditions=[])],
        return_type="int",
    )

    formula_builder = Mock()
    formula_builder.build_equivalence_formula_extended.return_value = FormulaBuilderResult(
        formula="(set-logic QF_BV)\n(check-sat)",
        return_var1="return_1",
        return_var2="return_2",
        constrained_fragments=[],
        extra_vars1=[],
        extra_vars2=[],
        param_fragment_constrained=[],
    )
    formula_builder.build_base_context.return_value = {
        "header_lines": [
            "(declare-const x_1 (_ BitVec 32))",
            "(declare-const x_2 (_ BitVec 32))",
            "(assert (= x_1 x_2))",
        ],
        "params1": [ParameterInfo(original_name="x", smt_name="x_1", bit_width=32, index=0)],
        "params2": [ParameterInfo(original_name="x", smt_name="x_2", bit_width=32, index=0)],
        "extra_vars1": [],
        "extra_vars2": [],
        "constrained_fragments": [],
        "return_size1": 32,
        "return_size2": 32,
    }

    strategy = MonolithicStrategy(formula_builder, _UnsatSolverRunner(), debug=False)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.counterexample_raw is None


def test_monolithic_strategy_does_not_accept_unsat_with_unsupported_effect_summary():
    class _UnsatSolverRunner:
        def __init__(self):
            self.timeout = 5

        def run_parallel(self, _query: str):
            return ParallelResult(results=[SolverResult("fake", SolverStatus.UNSAT)])

        def run_sequential(self, _query: str):
            return ParallelResult(results=[SolverResult("fake", SolverStatus.UNSAT)])

    analysis1 = FunctionReturnAnalysis(
        function_name="func1",
        entry_point="0x1",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1", value=_const(1), conditions=[])],
        return_type="int",
        effect_summary=EffectSummary(
            parameter_names=["x"],
            effects=[],
            has_unsupported_call=True,
            incomplete_reasons=(),
        ),
    )
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x2",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2", value=_const(1), conditions=[])],
        return_type="int",
    )

    formula_builder = Mock()
    formula_builder.build_equivalence_formula_extended.return_value = FormulaBuilderResult(
        formula="(set-logic QF_BV)\n(check-sat)",
        return_var1="return_1",
        return_var2="return_2",
        constrained_fragments=[],
        extra_vars1=[],
        extra_vars2=[],
        param_fragment_constrained=[],
    )
    formula_builder.build_base_context.return_value = {
        "header_lines": [
            "(declare-const x_1 (_ BitVec 32))",
            "(declare-const x_2 (_ BitVec 32))",
            "(assert (= x_1 x_2))",
        ],
        "params1": [ParameterInfo(original_name="x", smt_name="x_1", bit_width=32, index=0)],
        "params2": [ParameterInfo(original_name="x", smt_name="x_2", bit_width=32, index=0)],
        "extra_vars1": [],
        "extra_vars2": [],
        "constrained_fragments": [],
        "return_size1": 32,
        "return_size2": 32,
    }

    strategy = MonolithicStrategy(formula_builder, _UnsatSolverRunner(), debug=False)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.counterexample_raw is None


def test_monolithic_call_effect_summary_proof_complete_allows_recovery():
    class _UnsatSolverRunner:
        def __init__(self):
            self.timeout = 5

        def run_parallel(self, _query: str):
            return ParallelResult(results=[SolverResult("fake", SolverStatus.UNSAT)])

        def run_sequential(self, _query: str):
            return ParallelResult(results=[SolverResult("fake", SolverStatus.UNSAT)])

    analysis1 = _analysis_with_unsupported_call_effect()
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x2000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=_const(1), conditions=[])],
        return_type="int",
    )
    formula_builder = Mock()
    formula_builder.build_equivalence_formula_extended.return_value = FormulaBuilderResult(
        formula="(set-logic QF_BV)\n(check-sat)",
        return_var1="return_1",
        return_var2="return_2",
        constrained_fragments=[],
        extra_vars1=[],
        extra_vars2=[],
        param_fragment_constrained=[],
    )
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    strategy = MonolithicStrategy(formula_builder, _UnsatSolverRunner(), debug=False)
    completed_reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:unsupported_call_effect_summary",
        analysis1,
        analysis2,
        stage="S_MONOLITHIC_FALLBACK",
    )
    analysis1.completed_recovery_proof_evidence = (
        _complete_call_effect_summary_proof_evidence(
            completed_reason.object_target_key,
            proof_obligation_id=completed_reason.proof_obligation_id,
        ),
    )

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is True
    assert result.unknown_reasons == []
    assert result.counterexample_raw is None


def test_monolithic_call_effect_summary_bare_completed_proof_id_does_not_recover():
    class _UnsatSolverRunner:
        def __init__(self):
            self.timeout = 5

        def run_parallel(self, _query: str):
            return ParallelResult(results=[SolverResult("fake", SolverStatus.UNSAT)])

        def run_sequential(self, _query: str):
            return ParallelResult(results=[SolverResult("fake", SolverStatus.UNSAT)])

    analysis1 = _analysis_with_unsupported_call_effect()
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x2000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=_const(1), conditions=[])],
        return_type="int",
    )
    formula_builder = Mock()
    formula_builder.build_equivalence_formula_extended.return_value = FormulaBuilderResult(
        formula="(set-logic QF_BV)\n(check-sat)",
        return_var1="return_1",
        return_var2="return_2",
        constrained_fragments=[],
        extra_vars1=[],
        extra_vars2=[],
        param_fragment_constrained=[],
    )
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    strategy = MonolithicStrategy(formula_builder, _UnsatSolverRunner(), debug=False)
    completed_reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:unsupported_call_effect_summary",
        analysis1,
        analysis2,
        stage="S_MONOLITHIC_FALLBACK",
    )
    analysis1.completed_recovery_proof_ids = (completed_reason.proof_obligation_id,)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.unknown_reasons
    assert result.counterexample_raw is None


def test_monolithic_call_effect_summary_missing_completed_proof_id_does_not_recover():
    class _UnsatSolverRunner:
        def __init__(self):
            self.timeout = 5

        def run_parallel(self, _query: str):
            return ParallelResult(results=[SolverResult("fake", SolverStatus.UNSAT)])

        def run_sequential(self, _query: str):
            return ParallelResult(results=[SolverResult("fake", SolverStatus.UNSAT)])

    analysis1 = _analysis_with_unsupported_call_effect()
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x2000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=_const(1), conditions=[])],
        return_type="int",
    )
    formula_builder = Mock()
    formula_builder.build_equivalence_formula_extended.return_value = FormulaBuilderResult(
        formula="(set-logic QF_BV)\n(check-sat)",
        return_var1="return_1",
        return_var2="return_2",
        constrained_fragments=[],
        extra_vars1=[],
        extra_vars2=[],
        param_fragment_constrained=[],
    )
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    strategy = MonolithicStrategy(formula_builder, _UnsatSolverRunner(), debug=False)
    completed_reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:unsupported_call_effect_summary",
        analysis1,
        analysis2,
        stage="S_MONOLITHIC_FALLBACK",
    )
    evidence = _call_effect_summary_proof_evidence(
        object_target_key=completed_reason.object_target_key,
        proof_obligation_id=completed_reason.proof_obligation_id,
    )
    evidence.pop("proof_obligation_id", None)
    analysis1.completed_recovery_proof_evidence = (evidence,)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.unknown_reasons
    assert result.counterexample_raw is None


def test_function_return_analysis_skips_monolithic_fallback_when_coverage_gap_note_is_present():
    analysis = FunctionReturnAnalysis(
        function_name="func1",
        entry_point="0x1",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1", value=_const(1), conditions=[_eq(Expression.parameter("x", 0, size=4), _const(0))])],
        return_type="int",
        analysis_notes=["return_case_coverage_gap"],
    )

    assert analysis.should_skip_monolithic_fallback() is True
    assert "return_case_coverage_gap" in analysis.get_decisive_sat_unsafety_reasons()


def test_pairwise_strategy_downgrades_unsat_when_deferred_call_recovery_is_inconclusive(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = {
        "header_lines": [
            "(declare-const x_1 (_ BitVec 32))",
            "(declare-const x_2 (_ BitVec 32))",
            "(assert (= x_1 x_2))",
        ],
        "params1": [ParameterInfo(original_name="x", smt_name="x_1", bit_width=32, index=0)],
        "params2": [ParameterInfo(original_name="x", smt_name="x_2", bit_width=32, index=0)],
        "extra_vars1": [],
        "extra_vars2": [],
        "constrained_fragments": [],
        "return_size1": 32,
        "return_size2": 32,
    }
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)

    x = Expression.parameter("x", 0, size=4)
    pcode_ref = PcodeOpRef(address_offset=0x3000, seq_time=1, seq_order=0, mnemonic="CALL")
    deferred = DeferredCallInfo(
        placeholder_name="call_out_of_scope:callee#0",
        target_ref=CallTargetRef.from_name("callee"),
        arguments=[Expression.parameter("param_1", 0, size=4)],
        deferred_call_ref=DeferredCallRef(
            pcode_op_ref=pcode_ref,
            target_ref=CallTargetRef.from_name("callee"),
            sequence=0,
        ),
        call_argument_recovery_status=CallArgumentEvidence.RECOVERY_INCONCLUSIVE,
        call_argument_recovery_reason="argument_recovery_inconclusive",
    )
    analysis1 = FunctionReturnAnalysis(
        function_name="func1",
        entry_point="0x1",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1", value=x, conditions=[])],
        return_type="int",
    )
    analysis1.deferred_calls = {deferred.deferred_call_ref.stable_key(): deferred}
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x2",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2", value=x, conditions=[])],
        return_type="int",
    )
    case1 = ReturnCase(
        index=0,
        conditions=[],
        value_expr=x,
        return_info=analysis1.returns[0],
        return_type="int",
        parameters=analysis1.parameters,
    )
    case2 = ReturnCase(
        index=0,
        conditions=[],
        value_expr=x,
        return_info=analysis2.returns[0],
        return_type="int",
        parameters=analysis2.parameters,
    )

    monkeypatch.setattr(
        strategy,
        "_extract_return_cases",
        lambda analysis: [case1] if analysis.function_name == "func1" else [case2],
    )
    monkeypatch.setattr(strategy, "_prune_unreachable_cases", lambda cases, *_args, **_kwargs: cases)
    monkeypatch.setattr(strategy, "_cases_are_contradictory", lambda *_args, **_kwargs: False)
    monkeypatch.setattr(
        strategy,
        "_case_contains_unresolved_expression",
        lambda *_args, **_kwargs: False,
    )
    strategy._solve_query_twostage = Mock(
        return_value=QueryResult(is_equivalent=True)
    )

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.unsat_pairs == 1
    assert result.unknown_pairs == 0


def test_pairwise_strategy_records_call_effect_blocker_as_pending_object_proof(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = {
        "header_lines": [
            "(declare-const x_1 (_ BitVec 32))",
            "(declare-const x_2 (_ BitVec 32))",
            "(assert (= x_1 x_2))",
        ],
        "params1": [ParameterInfo(original_name="x", smt_name="x_1", bit_width=32, index=0)],
        "params2": [ParameterInfo(original_name="x", smt_name="x_2", bit_width=32, index=0)],
        "extra_vars1": [],
        "extra_vars2": [],
        "constrained_fragments": [],
        "return_size1": 32,
        "return_size2": 32,
    }
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)

    x = Expression.parameter("x", 0, size=4)
    pcode_ref = PcodeOpRef(address_offset=0x3000, seq_time=1, seq_order=0, mnemonic="CALL")
    deferred = DeferredCallInfo(
        placeholder_name="call_out_of_scope:callee#0",
        target_ref=CallTargetRef.from_name("callee", program_id=1, entry_offset=0x401000),
        arguments=[Expression.parameter("param_1", 0, size=4)],
        deferred_call_ref=DeferredCallRef(
            caller_program_id=1,
            caller_entry_offset=0x400000,
            pcode_op_ref=pcode_ref,
            target_ref=CallTargetRef.from_name("callee", program_id=1, entry_offset=0x401000),
            sequence=0,
        ),
        call_argument_recovery_status=CallArgumentEvidence.RECOVERY_INCONCLUSIVE,
        call_argument_recovery_reason="argument_recovery_inconclusive",
    )
    analysis1 = FunctionReturnAnalysis(
        function_name="func1",
        entry_point="0x1",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1", value=x, conditions=[])],
        return_type="int",
    )
    analysis1.deferred_calls = {deferred.deferred_call_ref.stable_key(): deferred}
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x2",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2", value=x, conditions=[])],
        return_type="int",
    )
    case1 = ReturnCase(
        index=0,
        conditions=[],
        value_expr=x,
        return_info=analysis1.returns[0],
        return_type="int",
        parameters=analysis1.parameters,
    )
    case2 = ReturnCase(
        index=0,
        conditions=[],
        value_expr=x,
        return_info=analysis2.returns[0],
        return_type="int",
        parameters=analysis2.parameters,
    )

    monkeypatch.setattr(
        strategy,
        "_extract_return_cases",
        lambda analysis: [case1] if analysis.function_name == "func1" else [case2],
    )
    monkeypatch.setattr(strategy, "_prune_unreachable_cases", lambda cases, *_args, **_kwargs: cases)
    monkeypatch.setattr(strategy, "_cases_are_contradictory", lambda *_args, **_kwargs: False)
    monkeypatch.setattr(strategy, "_case_contains_unresolved_expression", lambda *_args, **_kwargs: False)
    strategy._solve_query_twostage = Mock(return_value=QueryResult(is_equivalent=True))

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert len(result.unknown_reasons) == 1
    reason = result.unknown_reasons[0]
    assert reason.reason_id == UnknownReasonId.EQUIVALENCE_BLOCKING_UNSAFETY.value
    assert reason.recovery_proof_kind == UnknownRecoveryProofKind.CALL_EFFECT_SUMMARY_PROOF.value
    assert reason.proof_stage == "object_evidence_collected"
    assert reason.evidence_kind == "call_effect_summary"
    assert reason.recovery_action == "call_effect_summary_proof_required"
    assert reason.action_status == UnknownRecoveryActionStatus.PENDING_PROOF.value
    assert reason.object_target_key[0] == "deferred_call"
    assert _nested_contains(reason.object_target_key, pcode_ref.stable_key())


def test_pairwise_strategy_records_recoverable_candidate_for_call_effect_blocker():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    analysis1, incomplete_pcode_ref, complete_pcode_ref = (
        _analysis_with_two_effect_call_argument_evidences()
    )
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x2000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=_const(1), conditions=[])],
        return_type="int",
    )

    reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:effect_call_argument_evidence_incomplete",
        analysis1,
        analysis2,
        stage="S_PAIRWISE",
    )

    assert reason.object_target_key[0] == "call_effect_blocker"
    assert _nested_contains(reason.object_target_key, incomplete_pcode_ref.stable_key())
    assert _nested_contains(reason.object_target_key, complete_pcode_ref.stable_key())

    strategy._record_completed_call_effect_summary_proof_if_safe(reason, analysis1, analysis2)

    proofs = [
        item
        for item in getattr(analysis1, "completed_recovery_proof_evidence", ())
        if item.get("proof_obligation_id") == reason.proof_obligation_id
    ]
    assert proofs == []


def test_pairwise_strategy_uses_unsupported_call_site_object_ref_for_blocking_proof():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    pcode_ref = PcodeOpRef(address_offset=0x3020, seq_time=4, seq_order=1, mnemonic="CALLIND")
    site = UnsupportedCallEffectRef(
        pcode_op_ref=pcode_ref,
        target_ref=None,
        reason="target_identity_unavailable",
        order_key=9,
    )
    analysis1 = FunctionReturnAnalysis(
        function_name="func1",
        entry_point="0x1",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1", value=Expression.parameter("x", 0, size=4), conditions=[])],
        return_type="int",
        effect_summary=EffectSummary(
            parameter_names=["x"],
            effects=[],
            has_unsupported_call=True,
            unsupported_call_sites=(site,),
        ),
    )
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x2",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2", value=Expression.parameter("x", 0, size=4), conditions=[])],
        return_type="int",
    )

    reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:unsupported_call_effect_summary",
        analysis1,
        analysis2,
        stage="S_PAIRWISE",
    )

    assert reason.recovery_proof_kind == UnknownRecoveryProofKind.CALL_EFFECT_SUMMARY_PROOF.value
    assert reason.action_status == UnknownRecoveryActionStatus.PENDING_PROOF.value
    assert reason.object_target_key[0] == "unsupported_call_effect"
    assert _nested_contains(reason.object_target_key, pcode_ref.stable_key())


def test_pairwise_unsupported_call_effect_uses_phase2_specific_object_key():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    pcode_ref = PcodeOpRef(
        address_offset=0x401020,
        seq_time=31,
        seq_order=7,
        mnemonic="CALLIND",
        binary_id="B10",
        program_uid=12345,
        function_entry_space="ram",
        function_entry_offset=0x401000,
        target_space="ram",
        target_offset=0x401020,
        opcode=8,
        local_op_ordinal=0,
    )
    site = UnsupportedCallEffectRef(
        pcode_op_ref=pcode_ref,
        target_ref=CallTargetRef.from_code_address(0x401234, program_id=12345),
        target_expr=Expression.parameter("fp", 0, size=8),
        reason="target_identity_unavailable",
        order_key=9,
    )
    analysis1 = FunctionReturnAnalysis(
        function_name="func1",
        entry_point="0x401000",
        function_ref=CallTargetRef.from_name("func1", program_id=12345, entry_offset=0x401000),
        binary_id="B10",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x401000", value=Expression.parameter("x", 0, size=4), conditions=[])],
        return_type="int",
        effect_summary=EffectSummary(
            parameter_names=["x"],
            effects=[],
            has_unsupported_call=True,
            unsupported_call_sites=(site,),
        ),
    )
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x402000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x402000", value=Expression.parameter("x", 0, size=4), conditions=[])],
        return_type="int",
    )

    reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:unsupported_call_effect_summary",
        analysis1,
        analysis2,
        stage="S_PAIRWISE",
    )

    assert reason.object_target_key[0] == "unsupported_call_effect"
    assert reason.object_target_key[2] == ("function_ref", ("function", "B10", 0x401000))
    assert reason.object_target_key[3][0] == "runtime_ref"
    assert ("pcode_op_ref", pcode_ref.stable_key()) in reason.object_target_key[3]
    assert ("callee_identity", ("code_address", "B10", 0x401234)) in reason.object_target_key[3]
    assert reason.object_target_key[4][0] == "callsite_storage"
    assert ("pcode_op_ref", pcode_ref.stable_key()) in reason.object_target_key[4]
    assert ("callee_identity", ("code_address", "B10", 0x401234)) in reason.object_target_key[4]
    assert reason.object_target_key[5] == ("effect_ordinal", 9)
    assert _object_target_key_is_specific(reason.object_target_key) is True
    assert reason.proof_obligation_id == build_proof_obligation_id(
        UnknownReasonId.EQUIVALENCE_BLOCKING_UNSAFETY.value,
        "object_evidence_collected",
        UnknownRecoveryProofKind.CALL_EFFECT_SUMMARY_PROOF.value,
        "call_effect_summary",
        reason.object_target_key,
    )
    assert reason.object_evidence == {
        "object_derived": True,
        "evidence_version": 1,
        "evidence_kind": "call_effect_summary",
        "blocker_reason": "function1:unsupported_call_effect_summary",
        "blocker_reason_kind": "unsupported_call_effect_summary",
        "object_target_kind": "unsupported_call_effect",
        "left_function": "func1",
        "right_function": "func2",
        "side": "function1",
        "analysis_key": ("function_ref", ("function", "B10", 0x401000)),
        "runtime_ref": reason.object_target_key[3],
        "callsite_storage": reason.object_target_key[4],
        "argument_storage": (),
        "effect_ordinal": ("effect_ordinal", 9),
        "unsupported_reason": "target_identity_unavailable",
        "call_effect_summary_status": "target_identity_unavailable",
    }
    assert UnknownReasonRecord.from_dict(reason.to_dict()).object_evidence == reason.object_evidence


def test_unsupported_call_site_object_key_keeps_caller_identity_distinct():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    pcode_ref = PcodeOpRef(address_offset=0x3020, seq_time=4, seq_order=1, mnemonic="CALLIND")
    site = UnsupportedCallEffectRef(
        pcode_op_ref=pcode_ref,
        target_ref=None,
        reason="target_identity_unavailable",
        order_key=9,
    )
    left = FunctionReturnAnalysis(
        function_name="func",
        entry_point="0x1000",
        function_ref=CallTargetRef.from_name("func", program_id=1, entry_offset=0x1000),
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1000", value=Expression.parameter("x", 0, size=4), conditions=[])],
        return_type="int",
        effect_summary=EffectSummary(
            parameter_names=["x"],
            effects=[],
            has_unsupported_call=True,
            unsupported_call_sites=(site,),
        ),
    )
    right = FunctionReturnAnalysis(
        function_name="func",
        entry_point="0x1000",
        function_ref=CallTargetRef.from_name("func", program_id=2, entry_offset=0x1000),
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1000", value=Expression.parameter("x", 0, size=4), conditions=[])],
        return_type="int",
        effect_summary=EffectSummary(
            parameter_names=["x"],
            effects=[],
            has_unsupported_call=True,
            unsupported_call_sites=(site,),
        ),
    )

    left_reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:unsupported_call_effect_summary",
        left,
        right,
        stage="S_PAIRWISE",
    )
    right_reason = strategy._make_blocking_unsafety_unknown_reason(
        "function2:unsupported_call_effect_summary",
        left,
        right,
        stage="S_PAIRWISE",
    )

    assert left_reason.object_target_key != right_reason.object_target_key
    assert left_reason.proof_obligation_id != right_reason.proof_obligation_id
    assert ("function_ref", ("function", 1, 0x1000)) in left_reason.object_target_key
    assert ("function_ref", ("function", 2, 0x1000)) in right_reason.object_target_key


def test_unsupported_call_effect_blocker_prefers_unsupported_site_over_deferred_call():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    unsupported_pcode = PcodeOpRef(address_offset=0x3020, seq_time=4, seq_order=1, mnemonic="CALLIND")
    deferred_pcode = PcodeOpRef(address_offset=0x4000, seq_time=7, seq_order=2, mnemonic="CALL")
    site = UnsupportedCallEffectRef(
        pcode_op_ref=unsupported_pcode,
        target_ref=None,
        reason="target_identity_unavailable",
        order_key=9,
    )
    deferred = DeferredCallInfo(
        placeholder_name="call_out_of_scope:callee#0",
        target_ref=CallTargetRef.from_name("callee", program_id=1, entry_offset=0x401000),
        arguments=[Expression.parameter("x", 0, size=4)],
        deferred_call_ref=DeferredCallRef(
            caller_program_id=1,
            caller_entry_offset=0x1000,
            pcode_op_ref=deferred_pcode,
            target_ref=CallTargetRef.from_name("callee", program_id=1, entry_offset=0x401000),
            sequence=0,
        ),
        call_argument_recovery_status=CallArgumentEvidence.RECOVERY_INCONCLUSIVE,
    )
    analysis = FunctionReturnAnalysis(
        function_name="func",
        entry_point="0x1000",
        function_ref=CallTargetRef.from_name("func", program_id=1, entry_offset=0x1000),
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1000", value=Expression.parameter("x", 0, size=4), conditions=[])],
        return_type="int",
        effect_summary=EffectSummary(
            parameter_names=["x"],
            effects=[],
            has_unsupported_call=True,
            unsupported_call_sites=(site,),
        ),
    )
    analysis.deferred_calls = {deferred.deferred_call_ref.stable_key(): deferred}
    other = FunctionReturnAnalysis(
        function_name="other",
        entry_point="0x2000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=Expression.parameter("x", 0, size=4), conditions=[])],
        return_type="int",
    )

    reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:unsupported_call_effect_summary",
        analysis,
        other,
        stage="S_PAIRWISE",
    )

    assert reason.object_target_key[0] == "unsupported_call_effect"
    assert _nested_contains(reason.object_target_key, unsupported_pcode.stable_key())
    assert not _nested_contains(reason.object_target_key, deferred_pcode.stable_key())


def test_bounded_deferred_target_blocker_uses_concrete_callsite_fallback():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    unsupported_pcode = PcodeOpRef(address_offset=0x3020, seq_time=4, seq_order=1, mnemonic="CALLIND")
    deferred_pcode = PcodeOpRef(address_offset=0x4000, seq_time=7, seq_order=2, mnemonic="CALL")
    site = UnsupportedCallEffectRef(
        pcode_op_ref=unsupported_pcode,
        target_ref=None,
        reason="target_identity_unavailable",
        order_key=9,
    )
    deferred = DeferredCallInfo(
        placeholder_name="call_out_of_scope:callee#0",
        target_ref=CallTargetRef.from_name("callee", program_id=1, entry_offset=0x401000),
        arguments=[Expression.parameter("x", 0, size=4)],
        deferred_call_ref=DeferredCallRef(
            caller_program_id=1,
            caller_entry_offset=0x1000,
            pcode_op_ref=deferred_pcode,
            target_ref=CallTargetRef.from_name("callee", program_id=1, entry_offset=0x401000),
            sequence=0,
        ),
        call_argument_recovery_status=CallArgumentEvidence.RECOVERY_COMPLETE,
    )
    analysis = FunctionReturnAnalysis(
        function_name="func",
        entry_point="0x1000",
        function_ref=CallTargetRef.from_name("func", program_id=1, entry_offset=0x1000),
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1000", value=Expression.parameter("x", 0, size=4), conditions=[])],
        return_type="int",
        effect_summary=EffectSummary(
            parameter_names=["x"],
            effects=[],
            has_unsupported_call=True,
            unsupported_call_sites=(site,),
        ),
    )
    analysis.deferred_calls = {deferred.deferred_call_ref.stable_key(): deferred}
    other = FunctionReturnAnalysis(
        function_name="other",
        entry_point="0x2000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=Expression.parameter("x", 0, size=4), conditions=[])],
        return_type="int",
    )

    reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:bounded_call_refinement_deferred_target_unresolved",
        analysis,
        other,
        stage="S_PAIRWISE",
    )

    assert reason.object_target_key[0] == "deferred_call"
    assert _nested_contains(reason.object_target_key, deferred_pcode.stable_key())
    assert not _nested_contains(reason.object_target_key, unsupported_pcode.stable_key())
    assert not _nested_contains(reason.object_target_key, "call_effect_blocker")


def test_deferred_call_object_key_distinguishes_unknown_target_expression_provenance():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    pcode_ref = PcodeOpRef(address_offset=0x3020, seq_time=4, seq_order=1, mnemonic="CALLIND")
    deferred_ref = DeferredCallRef(
        caller_program_id=1,
        caller_entry_offset=0x1000,
        pcode_op_ref=pcode_ref,
        target_ref=CallTargetRef.unknown(),
        sequence=0,
    )

    def _analysis_with_target_expr(target_expr: Expression) -> FunctionReturnAnalysis:
        deferred = DeferredCallInfo(
            placeholder_name="indirect",
            target_ref=CallTargetRef.unknown(),
            arguments=[Expression.parameter("x", 0, size=4)],
            call_target_expr=target_expr,
            deferred_call_ref=deferred_ref,
            call_argument_recovery_status=CallArgumentEvidence.RECOVERY_INCONCLUSIVE,
        )
        analysis = FunctionReturnAnalysis(
            function_name="func",
            entry_point="0x1000",
            function_ref=CallTargetRef.from_name("func", program_id=1, entry_offset=0x1000),
            parameters=[_param("x")],
            returns=[ReturnInfo(address="0x1000", value=Expression.parameter("x", 0, size=4), conditions=[])],
            return_type="int",
        )
        analysis.deferred_calls = {deferred.deferred_call_ref.stable_key(): deferred}
        return analysis

    left = _analysis_with_target_expr(Expression.parameter("fp", 0, size=8))
    right = _analysis_with_target_expr(Expression.parameter("gp", 1, size=8))
    other = FunctionReturnAnalysis(
        function_name="other",
        entry_point="0x2000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=Expression.parameter("x", 0, size=4), conditions=[])],
        return_type="int",
    )

    left_reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:effect_call_argument_evidence_incomplete",
        left,
        other,
        stage="S_PAIRWISE",
    )
    right_reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:effect_call_argument_evidence_incomplete",
        right,
        other,
        stage="S_PAIRWISE",
    )

    assert left_reason.object_target_key != right_reason.object_target_key
    assert left_reason.proof_obligation_id != right_reason.proof_obligation_id
    assert _nested_contains(
        left_reason.object_target_key,
        ("typed_target_expression", ("expression", ("parameter", "fp", ("int", 0), 8))),
    )
    assert _nested_contains(
        right_reason.object_target_key,
        ("typed_target_expression", ("expression", ("parameter", "gp", ("int", 1), 8))),
    )


def test_deferred_call_object_key_distinguishes_truncated_target_expression_provenance():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    pcode_ref = PcodeOpRef(address_offset=0x3020, seq_time=4, seq_order=1, mnemonic="CALLIND")
    deferred_ref = DeferredCallRef(
        caller_program_id=1,
        caller_entry_offset=0x1000,
        pcode_op_ref=pcode_ref,
        target_ref=CallTargetRef.unknown(),
        sequence=0,
    )

    def _analysis_with_target_expr(target_expr: Expression) -> FunctionReturnAnalysis:
        deferred = DeferredCallInfo(
            placeholder_name="indirect",
            target_ref=CallTargetRef.unknown(),
            arguments=[Expression.parameter("x", 0, size=4)],
            call_target_expr=target_expr,
            deferred_call_ref=deferred_ref,
            call_argument_recovery_status=CallArgumentEvidence.RECOVERY_INCONCLUSIVE,
        )
        analysis = FunctionReturnAnalysis(
            function_name="func",
            entry_point="0x1000",
            function_ref=CallTargetRef.from_name("func", program_id=1, entry_offset=0x1000),
            parameters=[_param("x")],
            returns=[ReturnInfo(address="0x1000", value=Expression.parameter("x", 0, size=4), conditions=[])],
            return_type="int",
        )
        analysis.deferred_calls = {deferred.deferred_call_ref.stable_key(): deferred}
        return analysis

    left = _analysis_with_target_expr(_deep_zext_target("fp", 0))
    right = _analysis_with_target_expr(_deep_zext_target("gp", 1))
    other = FunctionReturnAnalysis(
        function_name="other",
        entry_point="0x2000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=Expression.parameter("x", 0, size=4), conditions=[])],
        return_type="int",
    )

    left_reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:effect_call_argument_evidence_incomplete",
        left,
        other,
        stage="S_PAIRWISE",
    )
    right_reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:effect_call_argument_evidence_incomplete",
        right,
        other,
        stage="S_PAIRWISE",
    )

    assert left_reason.object_target_key != right_reason.object_target_key
    assert left_reason.proof_obligation_id != right_reason.proof_obligation_id


def test_expression_provenance_key_handles_very_deep_target_expression_without_recursion_error():
    left_key = expression_provenance_key(_deep_zext_target("fp", 0, depth=900))
    right_key = expression_provenance_key(_deep_zext_target("gp", 1, depth=900))

    assert left_key != right_key


def test_expression_provenance_key_distinguishes_sources_beyond_digest_node_limit():
    left_key = expression_provenance_key(_deep_zext_target("fp", 0, depth=8200))
    right_key = expression_provenance_key(_deep_zext_target("gp", 1, depth=8200))

    assert left_key != right_key


def test_expression_provenance_key_distinguishes_deep_tail_structure_beyond_digest_node_limit():
    zext_key = expression_provenance_key(
        _deep_target_with_tail_op("fp", 0, "INT_ZEXT", depth=8200)
    )
    sext_key = expression_provenance_key(
        _deep_target_with_tail_op("fp", 0, "INT_SEXT", depth=8200)
    )

    assert zext_key != sext_key


def test_expression_provenance_key_prefers_parameter_runtime_ref_over_storage():
    storage = StorageInfo(
        is_register=True,
        space_name="register",
        offset=32,
        size=8,
        register_name="a0",
        base_register_name="a0",
        base_register_size_bits=64,
    )
    parameter_ref = LocationBaseRef.parameter(
        "op",
        index=0,
        owner_program_id=1234,
        owner_entry_offset=0x401000,
    )
    expr = Expression.parameter(
        "op",
        0,
        "int (*)(int, int)",
        size=8,
        storage_info=storage,
        runtime_ref=parameter_ref,
    )

    key = expression_provenance_key(expr)

    assert key == ("runtime_ref", ("parameter", 1234, 0x401000, 0))
    assert key[0] != "storage"


def test_artifact_stable_key_rewrites_parameter_runtime_ref_program_ids():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    program_id = 3734980569294953568
    analysis = FunctionReturnAnalysis(
        function_name="fc_apply_indirect",
        entry_point="0x101000",
        parameters=[],
        returns=[],
        return_type="int",
    )
    analysis.binary_id = "B10"
    key = (
        "typed_target_expression",
        ("runtime_ref", ("parameter", program_id, 0x101000, 0)),
    )

    normalized = strategy._artifact_stable_key_for_analysis(key, analysis)

    assert not _nested_contains(normalized, program_id)
    assert _nested_contains(normalized, "B10")
    assert _nested_contains(normalized, 0x101000)


def test_unsupported_call_effect_object_key_distinguishes_target_expression_provenance():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    pcode_ref = PcodeOpRef(address_offset=0x3020, seq_time=4, seq_order=1, mnemonic="CALLIND")

    def _analysis_with_site(target_expr: Expression) -> FunctionReturnAnalysis:
        site = UnsupportedCallEffectRef(
            pcode_op_ref=pcode_ref,
            target_ref=None,
            target_expr=target_expr,
            reason="target_identity_unavailable",
            order_key=9,
        )
        return FunctionReturnAnalysis(
            function_name="func",
            entry_point="0x1000",
            function_ref=CallTargetRef.from_name("func", program_id=1, entry_offset=0x1000),
            binary_id="B10",
            parameters=[_param("x")],
            returns=[ReturnInfo(address="0x1000", value=Expression.parameter("x", 0, size=4), conditions=[])],
            return_type="int",
            effect_summary=EffectSummary(
                parameter_names=["x"],
                effects=[],
                has_unsupported_call=True,
                unsupported_call_sites=(site,),
            ),
        )

    left = _analysis_with_site(Expression.parameter("fp", 0, size=8))
    right = _analysis_with_site(Expression.parameter("gp", 1, size=8))
    other = FunctionReturnAnalysis(
        function_name="other",
        entry_point="0x2000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=Expression.parameter("x", 0, size=4), conditions=[])],
        return_type="int",
    )

    left_reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:unsupported_call_effect_summary",
        left,
        other,
        stage="S_PAIRWISE",
    )
    right_reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:unsupported_call_effect_summary",
        right,
        other,
        stage="S_PAIRWISE",
    )

    assert left_reason.object_target_key != right_reason.object_target_key
    assert left_reason.proof_obligation_id != right_reason.proof_obligation_id
    assert _nested_contains(
        left_reason.object_target_key,
        ("typed_target_expression", ("expression", ("parameter", "fp", ("int", 0), 8))),
    )
    assert _nested_contains(
        left_reason.object_target_key,
        (
            "callee_identity",
            (
                "unknown",
                "B10",
                (
                    "target_expression",
                    ("typed_target_expression", ("expression", ("parameter", "fp", ("int", 0), 8))),
                ),
            ),
        ),
    )
    assert _nested_contains(
        right_reason.object_target_key,
        ("typed_target_expression", ("expression", ("parameter", "gp", ("int", 1), 8))),
    )


def test_unsupported_call_effect_object_key_does_not_embed_process_local_target_expression_id():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    pcode_ref = PcodeOpRef(address_offset=0x3030, seq_time=5, seq_order=1, mnemonic="CALLIND")
    target_expr = _deep_zext_target("fp", 0)

    site = UnsupportedCallEffectRef(
        pcode_op_ref=pcode_ref,
        target_ref=None,
        target_expr=target_expr,
        reason="target_identity_unavailable",
        order_key=10,
    )
    analysis = FunctionReturnAnalysis(
        function_name="func",
        entry_point="0x1000",
        function_ref=CallTargetRef.from_name("func", program_id=1, entry_offset=0x1000),
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1000", value=Expression.parameter("x", 0, size=4), conditions=[])],
        return_type="int",
        effect_summary=EffectSummary(
            parameter_names=["x"],
            effects=[],
            has_unsupported_call=True,
            unsupported_call_sites=(site,),
        ),
    )
    other = FunctionReturnAnalysis(
        function_name="other",
        entry_point="0x2000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=Expression.parameter("x", 0, size=4), conditions=[])],
        return_type="int",
    )

    reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:unsupported_call_effect_summary",
        analysis,
        other,
        stage="S_PAIRWISE",
    )

    target_identity = id(target_expr)
    assert not _nested_contains(site.stable_key(), target_identity)
    assert not _nested_contains(reason.object_target_key, target_identity)
    assert not _nested_contains(reason.proof_obligation_id, target_identity)


def test_unsupported_call_effect_object_key_distinguishes_truncated_target_expression_provenance():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    pcode_ref = PcodeOpRef(address_offset=0x3030, seq_time=5, seq_order=1, mnemonic="CALLIND")

    def _reason_for(target_expr: Expression):
        site = UnsupportedCallEffectRef(
            pcode_op_ref=pcode_ref,
            target_ref=None,
            target_expr=target_expr,
            reason="target_identity_unavailable",
            order_key=10,
        )
        analysis = FunctionReturnAnalysis(
            function_name="func",
            entry_point="0x1000",
            function_ref=CallTargetRef.from_name("func", program_id=1, entry_offset=0x1000),
            parameters=[_param("x")],
            returns=[ReturnInfo(address="0x1000", value=Expression.parameter("x", 0, size=4), conditions=[])],
            return_type="int",
            effect_summary=EffectSummary(
                parameter_names=["x"],
                effects=[],
                has_unsupported_call=True,
                unsupported_call_sites=(site,),
            ),
        )
        other = FunctionReturnAnalysis(
            function_name="other",
            entry_point="0x2000",
            parameters=[_param("x")],
            returns=[ReturnInfo(address="0x2000", value=Expression.parameter("x", 0, size=4), conditions=[])],
            return_type="int",
        )
        return site, strategy._make_blocking_unsafety_unknown_reason(
            "function1:unsupported_call_effect_summary",
            analysis,
            other,
            stage="S_PAIRWISE",
        )

    left_site, left_reason = _reason_for(_deep_zext_target("fp", 0))
    right_site, right_reason = _reason_for(_deep_zext_target("gp", 1))

    assert left_site.stable_key() != right_site.stable_key()
    assert left_reason.object_target_key != right_reason.object_target_key
    assert left_reason.proof_obligation_id != right_reason.proof_obligation_id


def test_unsupported_call_effect_object_key_handles_very_deep_target_expression_without_recursion_error():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    pcode_ref = PcodeOpRef(address_offset=0x3030, seq_time=5, seq_order=1, mnemonic="CALLIND")

    def _reason_for(target_expr: Expression):
        site = UnsupportedCallEffectRef(
            pcode_op_ref=pcode_ref,
            target_ref=None,
            target_expr=target_expr,
            reason="target_identity_unavailable",
            order_key=10,
        )
        analysis = FunctionReturnAnalysis(
            function_name="func",
            entry_point="0x1000",
            function_ref=CallTargetRef.from_name("func", program_id=1, entry_offset=0x1000),
            parameters=[_param("x")],
            returns=[ReturnInfo(address="0x1000", value=Expression.parameter("x", 0, size=4), conditions=[])],
            return_type="int",
            effect_summary=EffectSummary(
                parameter_names=["x"],
                effects=[],
                has_unsupported_call=True,
                unsupported_call_sites=(site,),
            ),
        )
        other = FunctionReturnAnalysis(
            function_name="other",
            entry_point="0x2000",
            parameters=[_param("x")],
            returns=[ReturnInfo(address="0x2000", value=Expression.parameter("x", 0, size=4), conditions=[])],
            return_type="int",
        )
        return strategy._make_blocking_unsafety_unknown_reason(
            "function1:unsupported_call_effect_summary",
            analysis,
            other,
            stage="S_PAIRWISE",
        )

    left_reason = _reason_for(_deep_zext_target("fp", 0, depth=900))
    right_reason = _reason_for(_deep_zext_target("gp", 1, depth=900))

    assert left_reason.object_target_key != right_reason.object_target_key
    assert left_reason.proof_obligation_id != right_reason.proof_obligation_id


def test_unsupported_call_effect_object_key_distinguishes_sources_beyond_digest_node_limit():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    pcode_ref = PcodeOpRef(address_offset=0x3030, seq_time=5, seq_order=1, mnemonic="CALLIND")

    def _reason_for(target_expr: Expression):
        site = UnsupportedCallEffectRef(
            pcode_op_ref=pcode_ref,
            target_ref=None,
            target_expr=target_expr,
            reason="target_identity_unavailable",
            order_key=10,
        )
        analysis = FunctionReturnAnalysis(
            function_name="func",
            entry_point="0x1000",
            function_ref=CallTargetRef.from_name("func", program_id=1, entry_offset=0x1000),
            parameters=[_param("x")],
            returns=[ReturnInfo(address="0x1000", value=Expression.parameter("x", 0, size=4), conditions=[])],
            return_type="int",
            effect_summary=EffectSummary(
                parameter_names=["x"],
                effects=[],
                has_unsupported_call=True,
                unsupported_call_sites=(site,),
            ),
        )
        other = FunctionReturnAnalysis(
            function_name="other",
            entry_point="0x2000",
            parameters=[_param("x")],
            returns=[ReturnInfo(address="0x2000", value=Expression.parameter("x", 0, size=4), conditions=[])],
            return_type="int",
        )
        return strategy._make_blocking_unsafety_unknown_reason(
            "function1:unsupported_call_effect_summary",
            analysis,
            other,
            stage="S_PAIRWISE",
        )

    left_reason = _reason_for(_deep_zext_target("fp", 0, depth=8200))
    right_reason = _reason_for(_deep_zext_target("gp", 1, depth=8200))

    assert left_reason.object_target_key != right_reason.object_target_key
    assert left_reason.proof_obligation_id != right_reason.proof_obligation_id


def test_unsupported_call_effect_object_key_distinguishes_deep_tail_structure_beyond_digest_node_limit():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    pcode_ref = PcodeOpRef(address_offset=0x3030, seq_time=5, seq_order=1, mnemonic="CALLIND")

    def _reason_for(target_expr: Expression):
        site = UnsupportedCallEffectRef(
            pcode_op_ref=pcode_ref,
            target_ref=None,
            target_expr=target_expr,
            reason="target_identity_unavailable",
            order_key=10,
        )
        analysis = FunctionReturnAnalysis(
            function_name="func",
            entry_point="0x1000",
            function_ref=CallTargetRef.from_name("func", program_id=1, entry_offset=0x1000),
            parameters=[_param("x")],
            returns=[ReturnInfo(address="0x1000", value=Expression.parameter("x", 0, size=4), conditions=[])],
            return_type="int",
            effect_summary=EffectSummary(
                parameter_names=["x"],
                effects=[],
                has_unsupported_call=True,
                unsupported_call_sites=(site,),
            ),
        )
        other = FunctionReturnAnalysis(
            function_name="other",
            entry_point="0x2000",
            parameters=[_param("x")],
            returns=[ReturnInfo(address="0x2000", value=Expression.parameter("x", 0, size=4), conditions=[])],
            return_type="int",
        )
        return strategy._make_blocking_unsafety_unknown_reason(
            "function1:unsupported_call_effect_summary",
            analysis,
            other,
            stage="S_PAIRWISE",
        )

    zext_reason = _reason_for(_deep_target_with_tail_op("fp", 0, "INT_ZEXT", depth=8200))
    sext_reason = _reason_for(_deep_target_with_tail_op("fp", 0, "INT_SEXT", depth=8200))

    assert zext_reason.object_target_key != sext_reason.object_target_key
    assert zext_reason.proof_obligation_id != sext_reason.proof_obligation_id


def _nested_contains(value, needle) -> bool:
    if value == needle:
        return True
    if isinstance(value, (tuple, list)):
        return any(_nested_contains(item, needle) for item in value)
    if isinstance(value, dict):
        return any(
            _nested_contains(key, needle) or _nested_contains(item, needle)
            for key, item in value.items()
        )
    return False


def test_blocking_unsafety_reason_mapping_accepts_detail_suffix_for_return_coverage():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)

    assert (
        strategy._unknown_reason_id_for_blocking_unsafety("function1:return_coverage_gap:case=3")
        == UnknownReasonId.RETURN_COVERAGE_GAP
    )
    assert (
        strategy._unknown_reason_id_for_blocking_unsafety("function2:return_coverage_inconclusive:branch=exit")
        == UnknownReasonId.RETURN_COVERAGE_INCONCLUSIVE
    )


def test_call_effect_blocker_candidate_score_prefers_complete_call_argument_evidence():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    incomplete = (
        "call_argument_evidence",
        "function1",
        "a",
        "b",
        "c",
        "d",
        False,
        "incomplete",
    )
    complete = (
        "call_argument_evidence",
        "function1",
        "a",
        "b",
        "c",
        "d",
        True,
        "complete",
    )
    unsupported = (
        "unsupported_call_effect",
        "function1",
        "a",
        "b",
        "c",
        "d",
        ("foo",),
    )

    assert strategy._call_effect_blocker_candidate_score(complete) > strategy._call_effect_blocker_candidate_score(incomplete)
    assert strategy._call_effect_blocker_candidate_score(complete) > strategy._call_effect_blocker_candidate_score(unsupported)


def test_analysis_requires_completed_return_coverage_proof_uses_reason_kind_for_suffixes():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)

    class _Analysis:
        def get_decisive_sat_unsafety_reasons(self):
            return (
                "return_case_coverage_inconclusive:branch=exit",
                "effect_summary_path_coverage_incomplete",
            )

    analysis = _Analysis()
    assert (
        strategy._analysis_requires_completed_return_coverage_proof(
            analysis,
            ignored_reason_ids=(),
        )
        is not None
    )
    assert (
        strategy._analysis_requires_completed_return_coverage_proof(
            analysis,
            ignored_reason_ids=(UnknownReasonId.RETURN_COVERAGE_INCONCLUSIVE,),
        )
        == UnknownReasonId.EQUIVALENCE_BLOCKING_UNSAFETY
    )
    assert (
        strategy._unknown_reason_id_for_blocking_unsafety(
            "function1:effect_summary_path_coverage_incomplete"
        )
        == UnknownReasonId.EQUIVALENCE_BLOCKING_UNSAFETY
    )


def test_return_coverage_gap_emits_object_derived_pending_proof_backlog():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    x = Expression.parameter("x", 0, size=4)
    return_ref = PcodeOpRef(
        address_offset=0x401020,
        seq_time=0x401020,
        seq_order=3,
        block_index=1,
        mnemonic="RETURN",
        input_sizes=(8, 4),
    )
    analysis1 = FunctionReturnAnalysis(
        function_name="left",
        entry_point="0x401000",
        parameters=[_param("x")],
        returns=[
            ReturnInfo(
                address="0x401020",
                value=_const(1),
                conditions=[_eq(x, _const(0))],
                pcode_op_ref=return_ref,
            )
        ],
        return_type="int",
    )
    analysis2 = FunctionReturnAnalysis(
        function_name="right",
        entry_point="0x402000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x402020", value=_const(1), conditions=[])],
        return_type="int",
    )

    reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:return_coverage_gap",
        analysis1,
        analysis2,
        stage="S_PAIRWISE",
    )
    actions = build_unknown_recovery_actions([reason])

    assert reason.reason_id == UnknownReasonId.RETURN_COVERAGE_GAP.value
    assert reason.action_status == UnknownRecoveryActionStatus.PENDING_PROOF.value
    assert reason.recovery_action == "return_coverage_proof_required"
    assert reason.object_target_key[0] == "return_coverage"
    assert _nested_contains(reason.object_target_key, return_ref.stable_key())
    assert ("return_storage", "return_value", 32, None, "int") in reason.object_target_key
    assert [action.proof_stage for action in actions] == [
        "return_partition_extraction",
        "return_guard_coverage",
    ]
    assert {action.status for action in actions} == {
        UnknownRecoveryActionStatus.PENDING_PROOF.value
    }
    assert actions[0].proof_obligation_id == build_proof_obligation_id(
        UnknownReasonId.RETURN_COVERAGE_GAP,
        "return_partition_extraction",
        UnknownRecoveryProofKind.RETURN_COVERAGE_COMPLETION,
        "missing_return_guard",
        reason.object_target_key,
    )


def test_return_coverage_inconclusive_emits_smt_disambiguation_pending_proof_backlog():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    x = Expression.parameter("x", 0, size=4)
    return_ref = PcodeOpRef(
        address_offset=0x401020,
        seq_time=0x401020,
        seq_order=3,
        block_index=1,
        mnemonic="RETURN",
        input_sizes=(8, 4),
    )
    analysis1 = FunctionReturnAnalysis(
        function_name="left",
        entry_point="0x401000",
        parameters=[_param("x")],
        returns=[
            ReturnInfo(
                address="0x401020",
                value=_const(1),
                conditions=[_eq(x, _const(0))],
                pcode_op_ref=return_ref,
            )
        ],
        return_type="int",
    )
    analysis2 = FunctionReturnAnalysis(
        function_name="right",
        entry_point="0x402000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x402020", value=_const(1), conditions=[])],
        return_type="int",
    )

    reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:return_coverage_inconclusive",
        analysis1,
        analysis2,
        stage="S_PAIRWISE",
    )
    actions = build_unknown_recovery_actions([reason])

    assert reason.reason_id == UnknownReasonId.RETURN_COVERAGE_INCONCLUSIVE.value
    assert reason.recovery_action == "return_coverage_proof_required"
    assert [action.proof_stage for action in actions] == [
        "return_coverage_smt_disambiguation",
    ]
    assert actions[0].evidence_kind == "case_guard_disjunction"
    assert actions[0].proof_obligation_id == build_proof_obligation_id(
        UnknownReasonId.RETURN_COVERAGE_INCONCLUSIVE,
        "return_coverage_smt_disambiguation",
        UnknownRecoveryProofKind.RETURN_COVERAGE_COMPLETION,
        "case_guard_disjunction",
        reason.object_target_key,
    )


def _coverage_identity_analysis(
    *,
    binary_id: str = "B1",
    returns_order: Tuple[int, ...] = (0, 1),
) -> FunctionReturnAnalysis:
    x0 = Expression.parameter("x", 0, size=4)
    returns = [
        ReturnInfo(
            address="0x401020",
            value=_const(1),
            conditions=[_eq(x0, _const(0))],
            pcode_op_ref=PcodeOpRef(
                address_offset=0x401020,
                seq_time=0x401020,
                seq_order=3,
                block_index=1,
                mnemonic="RETURN",
                input_sizes=(8, 4),
                binary_id=binary_id,
                function_entry_space="ram",
                function_entry_offset=0x401000,
                target_space="ram",
                target_offset=0x401020,
                opcode=61,
                local_op_ordinal=0,
            ),
        ),
        ReturnInfo(
            address="0x401030",
            value=_const(2),
            conditions=[_ne(Expression.parameter("x", 0, size=4), _const(0))],
            pcode_op_ref=PcodeOpRef(
                address_offset=0x401030,
                seq_time=0x401030,
                seq_order=4,
                block_index=2,
                mnemonic="RETURN",
                input_sizes=(8, 4),
                binary_id=binary_id,
                function_entry_space="ram",
                function_entry_offset=0x401000,
                target_space="ram",
                target_offset=0x401030,
                opcode=61,
                local_op_ordinal=0,
            ),
        ),
    ]
    return FunctionReturnAnalysis(
        function_name="f",
        entry_point="0x401000",
        function_ref=CallTargetRef.from_name("f", program_id=12345, entry_offset=0x401000),
        parameters=[_param("x")],
        returns=[returns[index] for index in returns_order],
        return_type="int",
        binary_id=binary_id,
    )


def test_return_coverage_target_identity_is_deterministic_for_rebuilt_ast_and_case_order():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    other = _coverage_identity_analysis(binary_id="B2")
    first = strategy._return_coverage_object_target_key(
        "function1:return_coverage_gap",
        _coverage_identity_analysis(binary_id="B1", returns_order=(0, 1)),
        other,
    )
    rebuilt = strategy._return_coverage_object_target_key(
        "function1:return_coverage_gap",
        _coverage_identity_analysis(binary_id="B1", returns_order=(0, 1)),
        other,
    )
    reordered = strategy._return_coverage_object_target_key(
        "function1:return_coverage_gap",
        _coverage_identity_analysis(binary_id="B1", returns_order=(1, 0)),
        other,
    )

    assert first == rebuilt
    assert first == reordered
    assert strategy._return_coverage_object_target_key_is_valid(first)


def test_return_coverage_target_identity_distinguishes_binary_identity():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    other = _coverage_identity_analysis(binary_id="B9")
    target_b1 = strategy._return_coverage_object_target_key(
        "function1:return_coverage_gap",
        _coverage_identity_analysis(binary_id="B1"),
        other,
    )
    target_b2 = strategy._return_coverage_object_target_key(
        "function1:return_coverage_gap",
        _coverage_identity_analysis(binary_id="B2"),
        other,
    )

    assert target_b1 != target_b2


def test_return_coverage_completed_evidence_rejects_exact_target_and_schema_mismatch():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    analysis1 = _coverage_identity_analysis(binary_id="B1")
    analysis2 = _coverage_identity_analysis(binary_id="B2")
    reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:return_coverage_gap",
        analysis1,
        analysis2,
        stage="S_PAIRWISE",
    )
    action = build_unknown_recovery_actions([reason])[0]
    valid = _return_coverage_completion_evidence(action)
    assert strategy._return_coverage_proof_id_from_evidence(valid) == action.proof_obligation_id

    side_mismatch = deepcopy(valid)
    side_target = list(side_mismatch["object_target_key"])
    side_target[2] = "function2"
    side_mismatch["object_target_key"] = tuple(side_target)
    assert strategy._return_coverage_proof_id_from_evidence(side_mismatch) is None

    schema_mismatch = deepcopy(valid)
    schema_mismatch["target_schema_version"] = -1
    assert strategy._return_coverage_proof_id_from_evidence(schema_mismatch) is None

    target_content_mismatch = deepcopy(valid)
    target_content_mismatch["proof_content"] = dict(target_content_mismatch["proof_content"])
    target_content_mismatch["proof_content"]["proof_target_identity"] = ("return_coverage", "different")
    assert strategy._return_coverage_proof_id_from_evidence(target_content_mismatch) is None

    solver_unknown = deepcopy(valid)
    solver_unknown["proof_content"] = deepcopy(solver_unknown["proof_content"])
    solver_unknown["proof_content"]["coverage_solver_evidence"] = {"status": "unknown"}
    assert strategy._return_coverage_proof_id_from_evidence(solver_unknown) is None


def test_return_coverage_completed_evidence_rejects_structural_content_mismatch():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    analysis1 = _coverage_identity_analysis(binary_id="B1")
    analysis2 = _coverage_identity_analysis(binary_id="B2")
    reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:return_coverage_gap",
        analysis1,
        analysis2,
        stage="S_PAIRWISE",
    )
    action = build_unknown_recovery_actions([reason])[0]
    valid = _return_coverage_completion_evidence(action)
    assert strategy._return_coverage_proof_id_from_evidence(valid) == action.proof_obligation_id

    guard_mismatch = deepcopy(valid)
    guard_mismatch["proof_content"] = deepcopy(guard_mismatch["proof_content"])
    guard_keys = list(guard_mismatch["proof_content"]["structural_guard_keys"]["keys"])
    first_guard = list(guard_keys[0])
    first_guard[2] = ("guard_structural_keys", (("return_guard", False, ("wrong",), ("wrong",)),))
    guard_keys[0] = tuple(first_guard)
    guard_mismatch["proof_content"]["structural_guard_keys"]["keys"] = tuple(guard_keys)
    assert strategy._return_coverage_proof_id_from_evidence(guard_mismatch) is None

    return_value_mismatch = deepcopy(valid)
    return_value_mismatch["proof_content"] = deepcopy(return_value_mismatch["proof_content"])
    value_keys = list(return_value_mismatch["proof_content"]["structural_guard_keys"]["keys"])
    first_value = list(value_keys[0])
    first_value[3] = ("return_value_structural_key", ("expression", "wrong_return_value"))
    value_keys[0] = tuple(first_value)
    return_value_mismatch["proof_content"]["structural_guard_keys"]["keys"] = tuple(value_keys)
    assert strategy._return_coverage_proof_id_from_evidence(return_value_mismatch) is None

    miss_mismatch = deepcopy(valid)
    miss_mismatch["proof_content"] = deepcopy(miss_mismatch["proof_content"])
    miss_keys = list(miss_mismatch["proof_content"]["structural_miss_formula_keys"]["keys"])
    miss_keys[0] = ("case_miss_formula", 0, ("expression", "wrong_miss_formula"))
    miss_mismatch["proof_content"]["structural_miss_formula_keys"]["keys"] = tuple(miss_keys)
    assert strategy._return_coverage_proof_id_from_evidence(miss_mismatch) is None


def test_return_coverage_normalization_required_uses_normalization_aware_schema():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    analysis1 = _coverage_identity_analysis(binary_id="B1")
    analysis2 = _coverage_identity_analysis(binary_id="B2")
    reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:return_coverage_gap",
        analysis1,
        analysis2,
        stage="S_PAIRWISE",
    )
    action = build_unknown_recovery_actions([reason])[0]
    strict_evidence = _return_coverage_completion_evidence(action)
    strict_evidence["normalization_required"] = True
    strict_evidence["proof_content"] = deepcopy(strict_evidence["proof_content"])
    strict_evidence["proof_content"]["normalization_required"] = True
    assert strategy._return_coverage_proof_id_from_evidence(strict_evidence) is None

    normalization_aware = _normalization_aware_return_coverage_evidence(action)
    assert strategy._return_coverage_proof_id_from_evidence(normalization_aware) == action.proof_obligation_id


def test_return_coverage_normalization_required_by_target_digest_rejects_strict_schema():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    analysis1 = _coverage_identity_analysis(binary_id="B1")
    analysis2 = _coverage_identity_analysis(binary_id="B2")
    reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:return_coverage_gap",
        analysis1,
        analysis2,
        stage="S_PAIRWISE",
    )
    action = build_unknown_recovery_actions([reason])[0]
    normalization_aware = _normalization_aware_return_coverage_evidence(action)
    digest = normalization_aware["proof_content"]["normalization_policy_digest"]
    target_with_digest = action.object_target_key + (("normalization_policy_digest", digest),)

    strict_evidence = _retarget_return_coverage_evidence(
        _return_coverage_completion_evidence(action),
        target_with_digest,
    )
    assert strategy._return_coverage_proof_id_from_evidence(strict_evidence) is None

    retargeted_normalized = _retarget_return_coverage_evidence(
        normalization_aware,
        target_with_digest,
    )
    assert strategy._return_coverage_proof_id_from_evidence(
        retargeted_normalized
    ) == retargeted_normalized["proof_obligation_id"]

    digest_mismatch = deepcopy(retargeted_normalized)
    digest_mismatch["proof_content"]["normalization_policy_digest"] = "0" * 64
    assert strategy._return_coverage_proof_id_from_evidence(digest_mismatch) is None


def test_return_coverage_normalization_policy_digest_is_canonical():
    policy_a = PairwiseStrategy._return_coverage_normalization_policy(
        rules=(
            {"rule_id": "z_rule", "width": 64},
            {"width": 32, "rule_id": "a_rule"},
        )
    )
    policy_b = {
        "rules": (
            {"rule_id": "a_rule", "width": 32},
            {"width": 64, "rule_id": "z_rule"},
        ),
        "canonical_encoding_version": PairwiseStrategy._RETURN_COVERAGE_NORMALIZATION_CANONICAL_ENCODING_VERSION,
        "rule_set_version": PairwiseStrategy._RETURN_COVERAGE_NORMALIZATION_RULESET_VERSION,
        "normalization_schema_version": PairwiseStrategy._RETURN_COVERAGE_NORMALIZATION_SCHEMA_VERSION,
        "normalization_policy_id": PairwiseStrategy._RETURN_COVERAGE_NORMALIZATION_POLICY_ID,
    }

    assert PairwiseStrategy._return_coverage_normalization_policy_digest(policy_a) == (
        PairwiseStrategy._return_coverage_normalization_policy_digest(policy_b)
    )


def test_return_coverage_normalization_policy_rejects_unsupported_ruleset_version():
    policy = PairwiseStrategy._return_coverage_normalization_policy(
        rules=({"rule_id": "a_rule", "width": 32},)
    )
    unsupported = dict(policy)
    unsupported["rule_set_version"] = 999

    assert PairwiseStrategy._return_coverage_normalization_policy_digest(unsupported) is None


def test_return_coverage_normalization_aware_rejects_payload_mismatch():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    analysis1 = _coverage_identity_analysis(binary_id="B1")
    analysis2 = _coverage_identity_analysis(binary_id="B2")
    reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:return_coverage_gap",
        analysis1,
        analysis2,
        stage="S_PAIRWISE",
    )
    action = build_unknown_recovery_actions([reason])[0]
    valid = _normalization_aware_return_coverage_evidence(action)
    assert strategy._return_coverage_proof_id_from_evidence(valid) == action.proof_obligation_id

    digest_mismatch = deepcopy(valid)
    digest_mismatch["proof_content"]["normalization_policy_digest"] = "0" * 64
    assert strategy._return_coverage_proof_id_from_evidence(digest_mismatch) is None

    correspondence_mismatch = deepcopy(valid)
    correspondence_mismatch["proof_content"]["raw_normalized_correspondence"][
        "normalized_guard_identity"
    ] = ("normalized_guard_identity", ("guard", "different"))
    assert strategy._return_coverage_proof_id_from_evidence(correspondence_mismatch) is None

    hash_mismatch = deepcopy(valid)
    hash_mismatch["proof_content"]["normalized_guard_payload"]["final_query_sha256"] = "1" * 64
    assert strategy._return_coverage_proof_id_from_evidence(hash_mismatch) is None

    missing_hash = deepcopy(valid)
    missing_hash["proof_content"]["normalized_guard_payload"].pop("final_query_sha256")
    assert strategy._return_coverage_proof_id_from_evidence(missing_hash) is None

    broken_value_payload = deepcopy(valid)
    query = broken_value_payload["proof_content"]["normalized_guard_formula"]["query"]
    digest = broken_value_payload["proof_content"]["normalization_policy_digest"]
    broken_value_payload["proof_content"]["raw_normalized_correspondence"][
        "raw_value_identity"
    ] = ("raw_value_identity", ("value", "raw"))
    broken_value_payload["proof_content"]["raw_normalized_correspondence"][
        "normalized_value_identity"
    ] = ("normalized_value_identity", ("value", "normalized"))
    broken_value_payload["proof_content"]["normalized_value_payload"] = {
        "normalization_policy_digest": digest,
        "raw_identity": ("raw_value_identity", ("value", "raw")),
        "normalized_identity": ("normalized_value_identity", ("value", "different")),
        "final_query_sha256": hashlib.sha256(query.encode("utf-8")).hexdigest(),
    }
    assert strategy._return_coverage_proof_id_from_evidence(broken_value_payload) is None

    value_without_correspondence = deepcopy(valid)
    value_without_correspondence["proof_content"]["normalized_value_payload"] = {
        "normalization_policy_digest": value_without_correspondence["proof_content"][
            "normalization_policy_digest"
        ],
        "raw_identity": ("raw_value_identity", ("value", "raw")),
        "normalized_identity": ("normalized_value_identity", ("value", "normalized")),
        "final_query_sha256": hashlib.sha256(
            value_without_correspondence["proof_content"]["normalized_guard_formula"]["query"].encode(
                "utf-8"
            )
        ).hexdigest(),
    }
    assert strategy._return_coverage_proof_id_from_evidence(value_without_correspondence) is None

    address_without_correspondence = deepcopy(valid)
    address_without_correspondence["proof_content"]["normalized_address_payload"] = {
        "normalization_policy_digest": address_without_correspondence["proof_content"][
            "normalization_policy_digest"
        ],
        "raw_identity": ("raw_address_identity", ("address", "raw")),
        "normalized_identity": ("normalized_address_identity", ("address", "normalized")),
        "final_query_sha256": hashlib.sha256(
            address_without_correspondence["proof_content"]["normalized_guard_formula"][
                "query"
            ].encode("utf-8")
        ).hexdigest(),
    }
    assert strategy._return_coverage_proof_id_from_evidence(address_without_correspondence) is None


def test_return_coverage_common_proof_reason_scope_is_enforced():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    analysis1 = _coverage_identity_analysis(binary_id="B1")
    analysis2 = _coverage_identity_analysis(binary_id="B2")
    reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:return_coverage_gap",
        analysis1,
        analysis2,
        stage="S_PAIRWISE",
    )
    action = build_unknown_recovery_actions([reason])[0]
    evidence = _return_coverage_completion_evidence(action)
    evidence["proof_content"] = deepcopy(evidence["proof_content"])
    evidence["proof_content"]["applicable_reason_ids"] = (UnknownReasonId.RETURN_COVERAGE_INCONCLUSIVE.value,)

    assert strategy._return_coverage_proof_id_from_evidence(evidence) is None


def test_return_coverage_target_identity_validator_rejects_raw_object_leaf():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    target = strategy._return_coverage_object_target_key(
        "function1:return_coverage_gap",
        _coverage_identity_analysis(binary_id="B1"),
        _coverage_identity_analysis(binary_id="B2"),
    )
    poisoned = list(target)
    function_identity = list(poisoned[3])
    function_identity.append(("raw_object", object()))
    poisoned[3] = tuple(function_identity)

    assert not strategy._return_coverage_object_target_key_is_valid(tuple(poisoned))


def test_return_coverage_target_identity_rejects_opaque_return_address():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    analysis1 = _coverage_identity_analysis(binary_id="B1")
    analysis2 = _coverage_identity_analysis(binary_id="B2")
    analysis1.returns[0].address = object()

    target = strategy._return_coverage_object_target_key(
        "function1:return_coverage_gap",
        analysis1,
        analysis2,
    )

    assert _nested_contains(target, "opaque")
    assert not strategy._return_coverage_object_target_key_is_valid(target)

    reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:return_coverage_gap",
        analysis1,
        analysis2,
        stage="S_PAIRWISE",
    )
    action = build_unknown_recovery_actions([reason])[0]
    evidence = _return_coverage_completion_evidence(action)
    assert strategy._return_coverage_proof_id_from_evidence(evidence) is None


def test_return_coverage_target_identity_rejects_opaque_parameter_storage():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    analysis1 = _coverage_identity_analysis(binary_id="B1")
    analysis2 = _coverage_identity_analysis(binary_id="B2")
    analysis1.parameters[0]["storage"] = object()

    target = strategy._return_coverage_object_target_key(
        "function1:return_coverage_gap",
        analysis1,
        analysis2,
    )

    assert _nested_contains(target, "opaque")
    assert not strategy._return_coverage_object_target_key_is_valid(target)

    reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:return_coverage_gap",
        analysis1,
        analysis2,
        stage="S_PAIRWISE",
    )
    action = build_unknown_recovery_actions([reason])[0]
    evidence = _return_coverage_completion_evidence(action)
    assert strategy._return_coverage_proof_id_from_evidence(evidence) is None


def test_return_coverage_object_target_ignores_diagnostic_suffix():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    x = Expression.parameter("x", 0, size=4)
    analysis1 = FunctionReturnAnalysis(
        function_name="left",
        entry_point="0x401000",
        parameters=[_param("x")],
        returns=[
            ReturnInfo(address="0x401020", value=_const(1), conditions=[_eq(x, _const(0))])
        ],
        return_type="int",
    )
    analysis2 = FunctionReturnAnalysis(
        function_name="right",
        entry_point="0x402000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x402020", value=_const(1), conditions=[])],
        return_type="int",
    )

    plain_reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:return_coverage_gap",
        analysis1,
        analysis2,
        stage="S_PAIRWISE",
    )
    suffixed_reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:return_coverage_gap:case=3",
        analysis1,
        analysis2,
        stage="S_PAIRWISE",
    )

    assert plain_reason.object_target_key == suffixed_reason.object_target_key
    assert build_unknown_recovery_actions([plain_reason])[0].proof_obligation_id == (
        build_unknown_recovery_actions([suffixed_reason])[0].proof_obligation_id
    )


def test_return_coverage_object_target_distinguishes_guard_partitions():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    x = Expression.parameter("x", 0, size=4)
    left_zero = FunctionReturnAnalysis(
        function_name="left",
        entry_point="0x401000",
        parameters=[_param("x")],
        returns=[
            ReturnInfo(address="0x401020", value=_const(1), conditions=[_eq(x, _const(0))])
        ],
        return_type="int",
    )
    left_one = FunctionReturnAnalysis(
        function_name="left",
        entry_point="0x401000",
        parameters=[_param("x")],
        returns=[
            ReturnInfo(address="0x401020", value=_const(1), conditions=[_eq(x, _const(1))])
        ],
        return_type="int",
    )
    right = FunctionReturnAnalysis(
        function_name="right",
        entry_point="0x402000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x402020", value=_const(1), conditions=[])],
        return_type="int",
    )

    zero_reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:return_coverage_gap",
        left_zero,
        right,
        stage="S_PAIRWISE",
    )
    one_reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:return_coverage_gap",
        left_one,
        right,
        stage="S_PAIRWISE",
    )

    assert zero_reason.object_target_key != one_reason.object_target_key
    assert build_unknown_recovery_actions([zero_reason])[0].proof_obligation_id != (
        build_unknown_recovery_actions([one_reason])[0].proof_obligation_id
    )


def test_monolithic_strategy_does_not_accept_unsat_with_deferred_call_argument_inconclusive():
    class _UnsatSolverRunner:
        def __init__(self):
            self.timeout = 5

        def run_parallel(self, _query: str):
            return ParallelResult(results=[SolverResult("fake", SolverStatus.UNSAT)])

        def run_sequential(self, _query: str):
            return ParallelResult(results=[SolverResult("fake", SolverStatus.UNSAT)])

    x = Expression.parameter("x", 0, size=4)
    pcode_ref = PcodeOpRef(address_offset=0x3010, seq_time=1, seq_order=0, mnemonic="CALL")
    deferred = DeferredCallInfo(
        placeholder_name="call_out_of_scope:callee#0",
        target_ref=CallTargetRef.from_name("callee"),
        arguments=[Expression.parameter("param_1", 0, size=4)],
        deferred_call_ref=DeferredCallRef(
            pcode_op_ref=pcode_ref,
            target_ref=CallTargetRef.from_name("callee"),
            sequence=0,
        ),
        call_argument_recovery_status=CallArgumentEvidence.RECOVERY_INCONCLUSIVE,
        call_argument_recovery_reason="argument_recovery_inconclusive",
    )
    analysis1 = FunctionReturnAnalysis(
        function_name="func1",
        entry_point="0x1",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1", value=x, conditions=[])],
        return_type="int",
    )
    analysis1.deferred_calls = {deferred.deferred_call_ref.stable_key(): deferred}
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x2",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2", value=x, conditions=[])],
        return_type="int",
    )

    formula_builder = Mock()
    formula_builder.build_equivalence_formula_extended.return_value = FormulaBuilderResult(
        formula="(set-logic QF_BV)\n(check-sat)",
        return_var1="return_1",
        return_var2="return_2",
        constrained_fragments=[],
        extra_vars1=[],
        extra_vars2=[],
        param_fragment_constrained=[],
    )
    formula_builder.build_base_context.return_value = {
        "header_lines": [
            "(declare-const x_1 (_ BitVec 32))",
            "(declare-const x_2 (_ BitVec 32))",
            "(assert (= x_1 x_2))",
        ],
        "params1": [ParameterInfo(original_name="x", smt_name="x_1", bit_width=32, index=0)],
        "params2": [ParameterInfo(original_name="x", smt_name="x_2", bit_width=32, index=0)],
        "extra_vars1": [],
        "extra_vars2": [],
        "constrained_fragments": [],
        "return_size1": 32,
        "return_size2": 32,
    }

    strategy = MonolithicStrategy(formula_builder, _UnsatSolverRunner(), debug=False)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.counterexample_raw is None

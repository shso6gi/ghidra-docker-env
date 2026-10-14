from scripts.function_tracer_pcode.tests.unit._input_correspondence_support import echo_input_correspondence
import hashlib

from scripts.function_tracer_pcode.core.evidence_authority import record_function_unary_evidence

from contextlib import contextmanager
from copy import deepcopy

from typing import Tuple

from unittest.mock import Mock

from scripts.function_tracer_pcode.analysis.effects.summary import (
    CanonicalLocation,
    CallArgumentEvidence,
    CallTargetResolutionEvidence,
    EffectSummary,
    StoreEffect,
    UnsupportedCallEffectRef,
    post_state_read_expression_for_location,
)

from scripts.function_tracer_pcode.proof.formula.builder import FormulaBuilderResult

from scripts.function_tracer_pcode.proof.formula.types import ParameterInfo

from scripts.function_tracer_pcode.proof.strategies.monolithic import MonolithicStrategy

from scripts.function_tracer_pcode.proof.strategies.pairwise import PairwiseStrategy

from scripts.function_tracer_pcode.proof.strategies.base import ReturnCoverageCheckResult

from scripts.function_tracer_pcode.proof.strategies.pairwise_models import QueryResult, ReturnCase

from scripts.function_tracer_pcode.checker.unknown_reason import (
    UnknownRecoveryActionStatus,
    UnknownRecoveryProofObligation,
    UnknownRecoveryProofKind,
    UnknownReasonRecord,
    UnknownReasonId,
    build_proof_obligation_id,
    build_unknown_recovery_actions,
    get_unknown_recovery_plan,
    make_internal_v2_reason_diagnostic,
    make_unknown_reason,
)

from scripts.function_tracer_pcode.core import (
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

from scripts.function_tracer_pcode.core.runtime_refs import LocationBaseRef

from scripts.function_tracer_pcode.core.runtime_refs import UnknownValueRef

from scripts.function_tracer_pcode.smt import ParallelResult, SolverResult, SolverStatus
from scripts.function_tracer_pcode.proof.obligations import SolverQueryExecutionReceipt

from scripts.function_tracer_pcode.tests.unit._object_target_key_specificity import (
    _object_target_key_is_specific,
)
from scripts.function_tracer_pcode.tests.unit._publication import raw_function_analysis

def _param(name: str, index: int = 0, size: int = 4, data_type: str = "int"):
    return {
        "name": name,
        "index": index,
        "size": size,
        "data_type": data_type,
        "is_signed": "unsigned" not in data_type,
    }


def _solver_bound_query_result(
    is_equivalent,
    *,
    query="(assert false)\n(check-sat)",
    model=None,
    pair_id="(0,0)",
    stage="with-ineq",
):
    status = SolverStatus.UNSAT if is_equivalent else SolverStatus.SAT
    parallel_result = ParallelResult(
        results=[SolverResult("fake", status, model=model)]
    )
    result = QueryResult(
        is_equivalent=is_equivalent,
        counterexample_raw=model,
        solver_results=parallel_result,
    )
    result.last_query = query
    result.pair_stage = stage
    result.solver_query_execution_receipt = (
        SolverQueryExecutionReceipt.from_execution(
            query=query,
            query_label=pair_id,
            proof_stage=stage,
            parallel_result=parallel_result,
            solver_identity=("unit", "fake", ("fake",)),
            timeout_budget=5.0,
            use_hard_timeout=False,
        )
    )
    return result

def _const(value: int, size: int = 4) -> Expression:
    return Expression.constant(value, size)

def _present_return_abi_facts(return_type: str = "int") -> dict:
    """Return the schema-v1 envelope required by pairwise test producers."""
    width = {"int": 4, "long": 8}.get(return_type, 4)
    return {
        "schema_version": 1,
        "calling_convention": {
            "status": "PRESENT",
            "value": ("ghidra_calling_convention_v1", "default"),
            "source": "sat_decisiveness_fixture",
        },
        "declared_or_effective_return_type": {
            "status": "PRESENT",
            "value": ("ghidra_return_type_v1", f"/{return_type}", width),
            "source": "sat_decisiveness_fixture",
        },
        "return_storage_descriptor": {
            "status": "PRESENT",
            "value": (
                "ghidra_return_storage_v1",
                (("ghidra_return_storage_member_v1", "register", 0, width),),
            ),
            "source": "sat_decisiveness_fixture",
        },
    }

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
    return raw_function_analysis(
        function_name=name,
        entry_point="0x1000",
        parameters=params,
        returns=[ReturnInfo(address="0x1000", value=value, conditions=[])],
        return_type="int",
        return_abi_facts=_present_return_abi_facts(),
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
    monkeypatch.setattr(strategy, "_case_contains_unresolved_expression", lambda *_args, **_kwargs: False)
    strategy._solve_query_after_guard = Mock(
        return_value=_solver_bound_query_result(True)
    )

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

def _return_coverage_gap_analyses():
    x = Expression.parameter("x", 0, size=4)
    analysis1 = raw_function_analysis(
        function_name="func1",
        entry_point="0x1",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1", value=_const(1), conditions=[_eq(x, _const(0))])],
        return_type="int",
        return_abi_facts=_present_return_abi_facts(),
    )
    analysis2 = raw_function_analysis(
        function_name="func2",
        entry_point="0x2",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2", value=_const(1), conditions=[])],
        return_type="int",
        return_abi_facts=_present_return_abi_facts(),
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
    monkeypatch.setattr(strategy, "_case_contains_unresolved_expression", lambda *_args, **_kwargs: False)
    strategy._solve_query_after_guard = Mock(
        return_value=_solver_bound_query_result(True)
    )

def _analysis_with_unsupported_call_effect() -> FunctionReturnAnalysis:
    site = UnsupportedCallEffectRef(
        pcode_op_ref=PcodeOpRef(address_offset=0x3020, seq_time=4, seq_order=1, mnemonic="CALLIND"),
        target_ref=None,
        target_expr=Expression.parameter("fp", 0, size=8),
        reason="target_identity_unavailable",
        order_key=9,
    )
    return raw_function_analysis(
        function_name="func1",
        entry_point="0x1000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1000", value=_const(1), conditions=[])],
        return_type="int",
        return_abi_facts=_present_return_abi_facts(),
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
    return raw_function_analysis(
        function_name=function_name,
        entry_point=hex(entry),
        function_ref=CallTargetRef.from_name(function_name, program_id=entry, entry_offset=entry),
        binary_id=binary_id,
        parameters=parameters,
        returns=[ReturnInfo(address=hex(entry), value=_const(1), conditions=[])],
        return_type="int",
        return_abi_facts=_present_return_abi_facts(),
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
    parameter_names=("fp", "a", "b"),
) -> FunctionReturnAnalysis:
    parameters = [
        _param(parameter_names[0], index=0, size=8),
        _param(parameter_names[1], index=1, size=4),
        _param(parameter_names[2], index=2, size=4),
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
    return raw_function_analysis(
        function_name=function_name,
        entry_point=hex(entry),
        function_ref=CallTargetRef.from_name(function_name, program_id=entry, entry_offset=entry),
        binary_id=binary_id,
        parameters=parameters,
        returns=[ReturnInfo(address=hex(entry), value=return_value, conditions=[])],
        return_type="int",
        return_abi_facts=_present_return_abi_facts(),
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
    return raw_function_analysis(
        function_name="func1",
        entry_point=hex(entry),
        function_ref=CallTargetRef.from_name("func1", program_id=1, entry_offset=entry),
        parameters=[_param("x")],
        returns=[ReturnInfo(address=hex(entry), value=_const(1), conditions=[])],
        return_type="int",
        return_abi_facts=_present_return_abi_facts(),
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
    return raw_function_analysis(
        function_name="func1",
        entry_point="0x1000",
        function_ref=CallTargetRef.from_name("func1", program_id=1, entry_offset=0x1000),
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1000", value=_const(1), conditions=[])],
        return_type="int",
        return_abi_facts=_present_return_abi_facts(),
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
        raw_function_analysis(
            function_name="func1",
            entry_point="0x1000",
            function_ref=CallTargetRef.from_name("func1", program_id=1, entry_offset=0x1000),
            parameters=[_param("x")],
            returns=[ReturnInfo(address="0x1000", value=_const(1), conditions=[])],
            return_type="int",
            return_abi_facts=_present_return_abi_facts(),
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
    return raw_function_analysis(
        function_name="func1",
        entry_point="0x1000",
        function_ref=CallTargetRef.from_name("func1", program_id=1, entry_offset=0x1000),
        parameters=[_param("fp", index=0, size=8), _param("selector", index=1)],
        returns=[ReturnInfo(address="0x1000", value=_const(1), conditions=[])],
        return_type="int",
        return_abi_facts=_present_return_abi_facts(),
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
    target_reason_ids = {
        "unsupported_call_effect": "unsupported_call_effect_semantics",
        "call_effect_blocker": "unsupported_call_effect_semantics",
        "call_argument_evidence": "call_argument_extraction_incomplete",
        "call_target_resolution_evidence": "call_target_resolution_unproven",
    }
    evidence = {
        "object_derived": True,
        "status": "complete",
        "reason_id": target_reason_ids.get(
            object_target_key[0], "unsupported_call_effect_semantics"
        ),
        "recovery_proof_kind": UnknownRecoveryProofKind.CALL_EFFECT_SUMMARY_PROOF.value,
        "proof_stage": "object_evidence_collected",
        "evidence_kind": "call_effect_summary",
        "object_target_key": object_target_key,
    }
    evidence["proof_obligation_id"] = _expected_call_effect_summary_proof_id(evidence)
    evidence.update(overrides)
    return _fixture_comparison_evidence(evidence)

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
    # bounded call refinement は analysis 層が関数単体で作る事実。
    record_function_unary_evidence(analysis, record)

def _completed_proof_ids_for_call_effect_evidence(evidence):
    analysis = raw_function_analysis(
        function_name="func1",
        entry_point="0x1000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1000", value=_const(1), conditions=[])],
        return_type="int",
        return_abi_facts=_present_return_abi_facts(),
        completed_recovery_proof_evidence=(evidence,),
    )
    return PairwiseStrategy._completed_recovery_proof_ids(analysis)

def _blocking_unsafety_object_target_key(blocking_reason, analysis1):
    strategy = PairwiseStrategy(echo_input_correspondence(Mock()), Mock(), debug=False)
    analysis2 = raw_function_analysis(
        function_name="func2",
        entry_point="0x2000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=_const(1), conditions=[])],
        return_type="int",
        return_abi_facts=_present_return_abi_facts(),
    )
    reason = strategy._make_blocking_unsafety_unknown_reason(
        blocking_reason,
        analysis1,
        analysis2,
        stage="S_PAIRWISE",
    )
    return reason.object_target_key

def _analysis_with_call_effect_summary_proof_evidence(**evidence_overrides) -> FunctionReturnAnalysis:
    return raw_function_analysis(
        function_name="func1",
        entry_point="0x1000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1000", value=_const(1), conditions=[])],
        return_type="int",
        return_abi_facts=_present_return_abi_facts(),
        completed_recovery_proof_evidence=(
            _call_effect_summary_proof_evidence(**evidence_overrides),
        ),
    )

def _expected_call_effect_summary_proof_id(evidence):
    return build_proof_obligation_id(
        evidence["reason_id"],
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
    return _fixture_comparison_evidence(evidence)

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
        "reason_id": action.reason_id,
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
    return _fixture_comparison_evidence(evidence)

def _sat_unsafety_resolution_action(evidence_refs=("counterexample_replay_missing",)):
    """The recovery action of a pending SAT-safety obligation with ``evidence_refs``.

    The default is the replay-type obligation: a replay proof may discharge only that
    type (plan v4 I5), so the evidence-validator tests exercise their own field there.
    """
    strategy = PairwiseStrategy(echo_input_correspondence(Mock()), Mock(), debug=False)
    analysis1 = _analysis_with_unsupported_call_effect()
    analysis2 = raw_function_analysis(
        function_name="func2",
        entry_point="0x2000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=_const(2), conditions=[])],
        return_type="int",
        return_abi_facts=_present_return_abi_facts(),
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
        tuple(evidence_refs),
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
    formula_builder = echo_input_correspondence(Mock())
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
    return raw_function_analysis(
        function_name=function_name,
        entry_point=hex(entry),
        function_ref=CallTargetRef.from_name(function_name, program_id=entry, entry_offset=entry),
        binary_id=binary_id,
        parameters=[_param("x")],
        returns=[ReturnInfo(address=hex(entry), value=param, conditions=[guard])],
        return_type="int",
        return_abi_facts=_present_return_abi_facts(),
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
    monkeypatch.setattr(strategy, "_unresolved_return_coverage_unknown_reasons", lambda *_args, **_kwargs: [])

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
    return raw_function_analysis(
        function_name="func1",
        entry_point="0x1000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1000", value=_const(1), conditions=[])],
        return_type="int",
        return_abi_facts=_present_return_abi_facts(),
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

def _fixture_comparison_binding():
    """fixture の比較の authority（raw pair と最終 relation、Issue #167）。

    fixture の比較中の証拠（``_fixture_comparison_evidence``）はこの比較に束縛され、gate は
    ``_fixture_comparison()`` の範囲で照合する。relation は parameter 1（count）を左 64 bit /
    右 32 bit にとり、左に 32 bit からの sign extension を含意する（readonly fixture proof の
    ``entailed_assumption`` と同じ仮定）。
    """

    from scripts.function_tracer_pcode.core import FunctionReturnAnalysis
    from scripts.function_tracer_pcode.proof.formula.input_correspondence import (
        build_input_correspondence_set,
    )
    from scripts.function_tracer_pcode.semantics.rewrite_contract import ExtensionKind
    from scripts.function_tracer_pcode.tests.unit._input_correspondence_support import (
        synthetic_input_extension_evidence,
    )

    def analysis(count_size, binary_id, entry_point):
        return raw_function_analysis(
            function_name="readonly_fixture",
            entry_point=entry_point,
            parameters=[
                {"name": "base", "index": 0, "size": 8},
                {"name": "count", "index": 1, "size": count_size, "is_signed": True},
            ],
            returns=[],
            return_type="int",
            binary_id=binary_id,
        )

    left = analysis(8, "left-binary", "0x1000")
    right = analysis(4, "right-binary", "0x2000")
    iee = synthetic_input_extension_evidence(left, 1, logical_bits=32, storage_bits=64, kind=ExtensionKind.SIGN)
    relation = build_input_correspondence_set(left, right, input_extension_evidence=(iee,))
    assert relation.entailed_projection_extension("left", 1, 64, 32) is not None
    from scripts.function_tracer_pcode.tests.unit._input_correspondence_support import comparison_binding_of

    return comparison_binding_of(left, right, relation)


def _readonly_fixture_relation():
    return _fixture_comparison_binding().relation


@contextmanager
def _fixture_comparison():
    """fixture の比較の範囲（fixture の比較中の証拠は、この中の gate でだけ採用される）。"""

    from scripts.function_tracer_pcode.proof.formula.input_correspondence import comparison_scope

    with comparison_scope(_fixture_comparison_binding()):
        yield


_readonly_fixture_comparison = _fixture_comparison


def _fixture_comparison_evidence(record):
    """fixture の比較の中で作った証拠として ``record`` を束縛する。"""

    from scripts.function_tracer_pcode.proof.formula.input_correspondence import (
        CrossSideIdentification,
        bind_evidence_to_comparison,
    )

    # fixture の証拠は producer の代役で、左右の同一視の検査（plan v4 PR-P）はこの fixture の
    # 対象外: relation の premise の下の証拠として束縛する（同一視の検査は専用の test が持つ）。
    return bind_evidence_to_comparison(
        record, _fixture_comparison_binding(), identification=CrossSideIdentification.CORRESPONDENCE,
    )


def _evidence_of_this_pair(analysis1, analysis2):
    """analysis に載せた fixture の比較中の証拠を、(analysis1, analysis2) の比較の証拠にする。

    ``strategy.check`` を直接呼ぶ test 用: check は自分の比較（この raw pair と最終 relation）
    の範囲を開くので、前の branch がこの比較で作った証拠として渡す。
    """

    from scripts.function_tracer_pcode.core.evidence_authority import (
        AUTHORITY_SCOPE_KEY,
        COMPARISON,
        COMPARISON_AUTHORITY_KEY,
    )
    from scripts.function_tracer_pcode.proof.formula.input_correspondence import (
        CrossSideIdentification,
        bind_evidence_to_comparison,
    )
    from scripts.function_tracer_pcode.proof.formula.input_correspondence.binding import (
        CROSS_SIDE_IDENTIFICATION_KEY,
    )
    from scripts.function_tracer_pcode.tests.unit._input_correspondence_support import comparison_binding_of

    comparison = comparison_binding_of(analysis1, analysis2)
    for analysis in (analysis1, analysis2):
        records = []
        for record in getattr(analysis, "completed_recovery_proof_evidence", ()) or ():
            if record.get(AUTHORITY_SCOPE_KEY) == COMPARISON:
                record = {key: value for key, value in record.items() if key != COMPARISON_AUTHORITY_KEY}
                record.pop(AUTHORITY_SCOPE_KEY)
                declared = record.get(CROSS_SIDE_IDENTIFICATION_KEY)
                record = bind_evidence_to_comparison(
                    record, comparison,
                    identification=None if declared is None else CrossSideIdentification(declared),
                )
            records.append(record)
        analysis.completed_recovery_proof_evidence = tuple(records)


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
                    # 入力 extension の出所は最終 InputCorrespondence だけ（Issue #167）。
                    "proof_source": "final_input_correspondence",
                    "input_correspondence_digest": _readonly_fixture_relation().digest,
                    "entailed_assumption": ("rewrite_assumption_v1", 1, 64, 32, "sign"),
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
    return _fixture_comparison_evidence(evidence)

def _method_b_reason(target=None):
    return make_internal_v2_reason_diagnostic(
        "loop_summary_semantic_equality_unproven",
        stage="S_PAIRWISE",
        pair_or_case="(0,0)",
        evidence_refs=("loop_summary_guard_mismatch",),
        recovery_proof_obligations=get_unknown_recovery_plan(
            UnknownReasonId.METHOD_B_CLOSURE_BLOCKED
        ).proof_obligations,
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
        "reason_id": action.reason_id,
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
    return _fixture_comparison_evidence(evidence)

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
    return raw_function_analysis(
        function_name="f",
        entry_point="0x401000",
        function_ref=CallTargetRef.from_name("f", program_id=12345, entry_offset=0x401000),
        parameters=[_param("x")],
        returns=[returns[index] for index in returns_order],
        return_type="int",
        return_abi_facts=_present_return_abi_facts(),
        binary_id=binary_id,
    )

# Export private helpers as well; split tests retain the original module globals.
__all__ = [name for name in globals() if not name.startswith('__')]

# -*- coding: utf-8 -*-
"""Pairwise 前の return case 統合に関する回帰テスト"""

import sys
from pathlib import Path
from unittest.mock import Mock

import pytest


workspace_root = Path(__file__).parent.parent.parent.parent
if str(workspace_root) not in sys.path:
    sys.path.insert(0, str(workspace_root))

from scripts.function_tracer_pcode.proof.strategies.pairwise_query_builder import (
    _build_object_centric_condition_signature,
    build_normalized_inequality_query,
    build_pair_query,
    extract_return_cases,
)
from scripts.function_tracer_pcode.proof.strategies.pairwise_models import QueryResult, ReturnCase
from scripts.function_tracer_pcode.proof.strategies.pairwise_query_executor import (
    solve_query_twostage,
)
from scripts.function_tracer_pcode.proof.strategies.pairwise import PairwiseStrategy
from scripts.function_tracer_pcode.proof.formula.builder import FormulaBuilder
from scripts.function_tracer_pcode.proof.formula.types import ParameterInfo
from scripts.function_tracer_pcode.checker.unknown_reason import (
    UnknownReasonId,
    build_unknown_recovery_actions,
    make_unknown_reason,
)
from scripts.function_tracer_pcode.analysis.effects.summary import (
    CanonicalLocation,
    EffectSummary,
    StoreEffect,
    lower_post_state_expression_for_smt,
    post_state_read_expression_for_location,
)
from scripts.function_tracer_pcode.analysis.returns.analyzer import ReturnAnalyzer
from scripts.function_tracer_pcode.core import (
    Condition,
    Expression,
    ExpressionType,
    FunctionReturnAnalysis,
    LocationBaseRef,
    PostStateValueRef,
    ReductionAccumulatorProof,
    ReadonlyReductionTermRef,
    ReadonlyReductionWitness,
    ReturnInfo,
    StorageInfo,
)
from conftest import resolve_mock_data_type


def _param(name: str) -> Expression:
    return Expression(ExpressionType.PARAMETER, name=name, size=8)


def _const(value: int) -> Expression:
    return Expression(ExpressionType.CONSTANT, value=value, size=8)


def _loc(name: str, offset: int, size: int) -> CanonicalLocation:
    return CanonicalLocation(
        base_ref=LocationBaseRef.parameter(name, index=0),
        offset=offset,
        size=size,
    )


def _neg(expr: Expression) -> Expression:
    return Expression(
        ExpressionType.UNARY_OP,
        operator="INT_2COMP",
        operands=[expr],
        size=8,
    )


def _cond(operator: str, left: Expression, right: Expression, negated: bool = False) -> Condition:
    return Condition(
        Expression(
            ExpressionType.BINARY_OP,
            operator=operator,
            operands=[left, right],
            size=1,
        ),
        negated=negated,
    )


def _bool_or(left: Condition, right: Condition, negated: bool = False) -> Condition:
    return Condition(
        Expression(
            ExpressionType.BINARY_OP,
            operator="BOOL_OR",
            operands=[left.expression, right.expression],
            size=1,
        ),
        negated=negated,
    )


def _analysis(returns) -> FunctionReturnAnalysis:
    return FunctionReturnAnalysis(
        function_name="f",
        entry_point="0x1000",
        parameters=[],
        returns=returns,
        return_type="long",
    )


def test_object_centric_condition_signature_sorts_mixed_none_and_int_keys():
    class _Condition:
        def __init__(self, key):
            self._key = key

        def structural_key(self, *, budget: int = 256):
            assert budget == 256
            return self._key

    signature = _build_object_centric_condition_signature(
        [
            _Condition(("condition", ("runtime_ref", None), 1)),
            _Condition(("condition", ("runtime_ref", 7), 1)),
        ]
    )

    assert signature == tuple(
        sorted(
            [
                ("condition", ("runtime_ref", None), 1),
                ("condition", ("runtime_ref", 7), 1),
            ],
            key=repr,
        )
    )


def _signed_semantic_param(
    *,
    name: str,
    suffix: str,
    bits: int,
    index: int = 0,
    semantic_bits: int | None = None,
) -> ParameterInfo:
    return ParameterInfo(
        original_name=name,
        smt_name=f"{name}{suffix}",
        bit_width=bits,
        index=index,
        is_signed=True,
        semantic_narrow_bits=semantic_bits,
        semantic_signedness="signed" if semantic_bits is not None else None,
    )


def _storage(name: str, offset: int, size_bits: int) -> StorageInfo:
    return StorageInfo(
        is_register=True,
        space_name="register",
        register_name=name,
        base_register_name="a1",
        base_register_offset=0x31D4,
        base_register_size_bits=64,
        bit_offset_in_base=offset,
        size=max(1, size_bits // 8),
        size_bits=size_bits,
    )


def _readonly_projection_ref(*, storage: StorageInfo, param_size: int):
    proof = ReductionAccumulatorProof(
        reduction_kind="memory_sum",
        pointer_base_ref=LocationBaseRef.parameter("base", index=0),
        count_parameter_name="count",
        count_parameter_index=1,
        count_parameter_storage_identity_key=storage.storage_identity_key(),
        limit_expr=Expression.parameter(
            "count",
            index=1,
            data_type="int" if param_size == 4 else "long",
            size=param_size,
            storage_info=storage,
        ),
        result_size=4,
        stride=4,
        element_size=4,
        index_scale=4,
        loop_body_witnesses=(
            ReadonlyReductionWitness(
                exact_count=1,
                terms=(ReadonlyReductionTermRef(byte_offset=0, access_size=4),),
            ),
            ReadonlyReductionWitness(
                exact_count=2,
                terms=(
                    ReadonlyReductionTermRef(byte_offset=0, access_size=4),
                    ReadonlyReductionTermRef(byte_offset=4, access_size=4),
                ),
            ),
        ),
    )
    ref = proof.lower_to_readonly_reduction_ref()
    assert ref is not None
    return ref


def _readonly_projection_case(ref, *, param_size: int, storage: StorageInfo) -> ReturnCase:
    value = Expression(ExpressionType.UNKNOWN, name="readonly", size=4, runtime_ref=ref)
    params = [
        {"name": "base", "index": 0, "size": 8},
        {
            "name": "count",
            "index": 1,
            "size": param_size,
            "is_signed": True,
            "storage_info": storage,
        },
    ]
    return ReturnCase(
        index=0,
        conditions=[],
        summary_conditions=[],
        value_expr=value,
        return_info=ReturnInfo(address="0x1000", value=value, conditions=[]),
        parameters=params,
        return_type="int",
    )


def _readonly_projection_reason_and_analyses(*, left_param: dict | None = None):
    wide_storage = _storage("a1", 0, 64)
    narrow_storage = _storage("a1_lo", 32, 32)
    left_ref = _readonly_projection_ref(storage=wide_storage, param_size=8)
    right_ref = _readonly_projection_ref(storage=narrow_storage, param_size=4)
    left_case = _readonly_projection_case(left_ref, param_size=4, storage=wide_storage)
    right_case = _readonly_projection_case(right_ref, param_size=4, storage=narrow_storage)
    if left_param is not None:
        left_case.parameters[1].update(left_param)
        for key, value in list(left_case.parameters[1].items()):
            if value is None:
                left_case.parameters[1].pop(key)
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    analysis1 = FunctionReturnAnalysis(
        function_name="f",
        entry_point="0x1000",
        parameters=left_case.parameters,
        returns=[left_case.return_info],
        return_type="int",
    )
    analysis2 = FunctionReturnAnalysis(
        function_name="f",
        entry_point="0x2000",
        parameters=right_case.parameters,
        returns=[right_case.return_info],
        return_type="int",
    )
    target = strategy._readonly_identity_object_target_key(
        base_ctx={"analysis1": analysis1, "analysis2": analysis2},
        case1=left_case,
        case2=right_case,
        pair_id="(0,0)",
    )
    reason = make_unknown_reason(
        UnknownReasonId.READONLY_IDENTITY_MISSING,
        stage="S_PAIRWISE",
        pair_or_case="(0,0)",
        evidence_kind="object_storage_identity",
        object_target_key=target,
    )
    return strategy, reason, analysis1, analysis2, left_case, right_case


def test_extract_return_cases_deduplicates_same_condition_set():
    cond_eq_zero = _cond("INT_EQUAL", _param("param_1"), _const(0))
    cond_nonzero = _cond("INT_NOTEQUAL", _param("param_2"), _const(0))

    analysis = _analysis(
        [
            ReturnInfo(
                address="0x1001",
                value=_param("param_1"),
                conditions=[cond_eq_zero, cond_nonzero, cond_eq_zero],
            ),
            ReturnInfo(
                address="0x1002",
                value=_param("param_1"),
                conditions=[cond_nonzero, cond_eq_zero],
            ),
        ]
    )

    cases = extract_return_cases(analysis)

    assert len(cases) == 1
    assert cases[0].source_indices == [0, 1]
    assert len(cases[0].conditions) == 2


def test_extract_return_cases_deduplicates_after_safe_value_normalization():
    analysis = _analysis(
        [
            ReturnInfo(
                address="0x1001",
                value=_param("param_1"),
                conditions=[],
            ),
            ReturnInfo(
                address="0x1002",
                value=_neg(_neg(_param("param_1"))),
                conditions=[],
            ),
        ]
    )

    cases = extract_return_cases(analysis)

    assert len(cases) == 1
    assert cases[0].source_indices == [0, 1]
    assert cases[0].value_expr.to_smt() == _param("param_1").to_smt()


def test_extract_return_cases_keeps_distinct_conditions_separate():
    analysis = _analysis(
        [
            ReturnInfo(
                address="0x1001",
                value=_param("param_1"),
                conditions=[_cond("INT_EQUAL", _param("param_1"), _const(0))],
            ),
            ReturnInfo(
                address="0x1002",
                value=_param("param_1"),
                conditions=[_cond("INT_NOTEQUAL", _param("param_1"), _const(0))],
            ),
        ]
    )

    cases = extract_return_cases(analysis)

    assert len(cases) == 2
    assert cases[0].source_indices == [0]
    assert cases[1].source_indices == [1]


def test_extract_return_cases_skips_contradictory_condition_regions():
    analysis = _analysis(
        [
            ReturnInfo(
                address="0x1001",
                value=_param("param_1"),
                conditions=[
                    _cond("INT_EQUAL", _param("param_1"), _const(0)),
                    _cond("INT_NOTEQUAL", _param("param_1"), _const(0)),
                ],
            ),
            ReturnInfo(
                address="0x1002",
                value=_const(7),
                conditions=[_cond("INT_NOTEQUAL", _param("param_1"), _const(0))],
            ),
        ]
    )

    cases = extract_return_cases(analysis)

    assert len(cases) == 1
    assert cases[0].value_expr.to_smt() == _const(7).to_smt()


def test_extract_return_cases_prunes_impossible_or_region():
    cond_a = _cond("INT_EQUAL", _param("param_1"), _const(0))
    cond_b = _cond("INT_EQUAL", _param("param_2"), _const(0))

    analysis = _analysis(
        [
            ReturnInfo(
                address="0x1001",
                value=_param("param_1"),
                conditions=[_bool_or(cond_a, cond_b), cond_a.negate(), cond_b.negate()],
            ),
            ReturnInfo(
                address="0x1002",
                value=_const(7),
                conditions=[_bool_or(cond_a, cond_b)],
            ),
        ]
    )

    cases = extract_return_cases(analysis)

    assert len(cases) == 1
    assert cases[0].value_expr.to_smt() == _const(7).to_smt()


def test_return_case_value_smt_lowers_symbolic_post_state_reads_with_effect_summary():
    trace = Expression(ExpressionType.PARAMETER, name="trace", value=0, size=8)
    start = Expression(ExpressionType.PARAMETER, name="start", value=1, size=4)
    limit = Expression(ExpressionType.PARAMETER, name="limit", value=2, size=4)

    trace_nonnull = _cond("INT_NOTEQUAL", trace, _const(0))
    loop_active = _cond("INT_SLESS", start, limit)
    final_iter = _cond("INT_EQUAL", limit, Expression.binary_op("INT_ADD", start, _const(1)))
    odd_iteration = _cond(
        "INT_NOTEQUAL",
        Expression.binary_op("INT_AND", start, _const(1)),
        _const(0),
    )
    even_iteration = odd_iteration.negate()

    params = [
        {"name": "trace", "index": 0, "size": 8},
        {"name": "start", "index": 1, "size": 4},
        {"name": "limit", "index": 2, "size": 4},
    ]
    steps_addr = Expression.binary_op("INT_ADD", trace, _const(4))
    value_expr = Expression.binary_op(
        "INT_ADD",
        post_state_read_expression_for_location(
            CanonicalLocation(base_ref=LocationBaseRef.parameter("trace", index=0), offset=4, size=4),
            params,
            symbolic=True,
        ),
        post_state_read_expression_for_location(
            CanonicalLocation(base_ref=LocationBaseRef.parameter("trace", index=0), offset=0, size=4),
            params,
            symbolic=True,
        ),
    )
    effects = [
        StoreEffect(
            location=CanonicalLocation(base_ref=LocationBaseRef.parameter("trace", index=0), offset=0, size=4),
            value=Expression.binary_op("INT_ADD", Expression.memory(trace, size=4), _neg(start)),
            conditions=[trace_nonnull, loop_active, odd_iteration, final_iter],
            order_key=5,
        ),
        StoreEffect(
            location=CanonicalLocation(base_ref=LocationBaseRef.parameter("trace", index=0), offset=0, size=4),
            value=Expression.binary_op("INT_ADD", Expression.memory(trace, size=4), start),
            conditions=[trace_nonnull, loop_active, even_iteration, final_iter],
            order_key=5,
        ),
        StoreEffect(
            location=CanonicalLocation(base_ref=LocationBaseRef.parameter("trace", index=0), offset=4, size=4),
            value=Expression.binary_op("INT_ADD", Expression.memory(steps_addr, size=4), _const(1)),
            conditions=[trace_nonnull, loop_active, final_iter],
            order_key=6,
        ),
    ]
    analysis = FunctionReturnAnalysis(
        function_name="f",
        entry_point="0x1000",
        parameters=params,
        returns=[
            ReturnInfo(
                address="0x1004",
                value=value_expr,
                conditions=[trace_nonnull, loop_active, final_iter],
            )
        ],
        return_type="int",
        effect_summary=EffectSummary(
            parameter_names=["trace", "start", "limit"],
            effects=effects,
        ),
    )

    cases = extract_return_cases(analysis)

    assert len(cases) == 1
    smt = cases[0].get_value_smt(lambda expr: expr)
    assert "__locread__" not in smt
    assert "ite" in smt
    assert "bvneg start" in smt


def test_return_case_value_smt_lowers_object_centric_post_state_memory_with_effect_summary():
    trace = Expression(ExpressionType.PARAMETER, name="trace", value=0, size=8)
    start = Expression(ExpressionType.PARAMETER, name="start", value=1, size=4)
    limit = Expression(ExpressionType.PARAMETER, name="limit", value=2, size=4)

    trace_nonnull = _cond("INT_NOTEQUAL", trace, _const(0))
    loop_active = _cond("INT_SLESS", start, limit)
    final_iter = _cond("INT_EQUAL", limit, Expression.binary_op("INT_ADD", start, _const(1)))
    odd_iteration = _cond(
        "INT_NOTEQUAL",
        Expression.binary_op("INT_AND", start, _const(1)),
        _const(0),
    )
    even_iteration = odd_iteration.negate()

    params = [
        {"name": "trace", "index": 0, "size": 8},
        {"name": "start", "index": 1, "size": 4},
        {"name": "limit", "index": 2, "size": 4},
    ]
    value_expr = post_state_read_expression_for_location(
        CanonicalLocation(base_ref=LocationBaseRef.parameter("trace", index=0), offset=0, size=4),
        params,
        symbolic=True,
    )
    effects = [
        StoreEffect(
            location=CanonicalLocation(base_ref=LocationBaseRef.parameter("trace", index=0), offset=0, size=4),
            value=Expression.binary_op("INT_ADD", Expression.memory(trace, size=4), _neg(start)),
            conditions=[trace_nonnull, loop_active, odd_iteration, final_iter],
            order_key=5,
        ),
        StoreEffect(
            location=CanonicalLocation(base_ref=LocationBaseRef.parameter("trace", index=0), offset=0, size=4),
            value=Expression.binary_op("INT_ADD", Expression.memory(trace, size=4), start),
            conditions=[trace_nonnull, loop_active, even_iteration, final_iter],
            order_key=5,
        ),
    ]
    analysis = FunctionReturnAnalysis(
        function_name="f",
        entry_point="0x1000",
        parameters=params,
        returns=[
            ReturnInfo(
                address="0x1004",
                value=value_expr,
                conditions=[trace_nonnull, loop_active, final_iter],
            )
        ],
        return_type="int",
        effect_summary=EffectSummary(
            parameter_names=["trace", "start", "limit"],
            effects=effects,
        ),
    )

    cases = extract_return_cases(analysis)

    assert len(cases) == 1
    smt = cases[0].get_value_smt(lambda expr: expr)
    assert "__locread__" not in smt
    assert "ite" in smt
    assert "bvneg start" in smt


def test_extract_return_cases_preserves_original_object_centric_value_for_smt_lowering():
    param_1 = _param("param_1")
    param_2 = _param("param_2")
    nonnull_1 = _cond("INT_NOTEQUAL", param_1, _const(0))
    nonnull_2 = _cond("INT_NOTEQUAL", param_2, _const(0))
    swap_taken = _cond(
        "INT_SLESS",
        Expression.memory(param_2, size=4),
        Expression.memory(param_1, size=4),
    )

    params = [
        {"name": "param_1", "index": 0, "size": 8},
        {"name": "param_2", "index": 1, "size": 8},
    ]
    value_expr = Expression.binary_op(
        "INT_SUB",
        post_state_read_expression_for_location(
            CanonicalLocation(base_ref=LocationBaseRef.parameter("param_1", index=0), offset=0, size=4),
            params,
            symbolic=True,
        ),
        post_state_read_expression_for_location(
            CanonicalLocation(base_ref=LocationBaseRef.parameter("param_2", index=1), offset=0, size=4),
            params,
            symbolic=True,
        ),
    )
    effects = [
        StoreEffect(
            location=CanonicalLocation(base_ref=LocationBaseRef.parameter("param_1", index=0), offset=0, size=4),
            value=Expression.memory(param_2, size=4),
            conditions=[swap_taken],
            order_key=10,
        ),
        StoreEffect(
            location=CanonicalLocation(base_ref=LocationBaseRef.parameter("param_2", index=1), offset=0, size=4),
            value=Expression.memory(param_1, size=4),
            conditions=[swap_taken],
            order_key=11,
        ),
    ]
    analysis = FunctionReturnAnalysis(
        function_name="f",
        entry_point="0x1000",
        parameters=params,
        returns=[
            ReturnInfo(
                address="0x1004",
                value=value_expr,
                conditions=[nonnull_1, nonnull_2, swap_taken],
            )
        ],
        return_type="int",
        effect_summary=EffectSummary(
            parameter_names=["param_1", "param_2"],
            effects=effects,
        ),
    )

    cases = extract_return_cases(analysis)

    assert len(cases) == 1
    assert cases[0].value_expr.operator == "INT_SUB"
    assert cases[0].normalized_value_expr.operator == "INT_ADD"
    smt = cases[0].get_value_smt(lambda expr: expr)
    assert "(select mem32 param_2)" in smt
    assert "(select mem32 param_1)" in smt
    assert "(bvsub (select mem32 param_1) (select mem32 param_2))" not in smt


def test_return_case_value_smt_does_not_replay_materialized_object_state_value():
    dst = _param("dst")
    src = _param("src")
    copy_flag = Expression(ExpressionType.PARAMETER, name="copy_flag", value=2, size=4)
    dst_nonnull = _cond("INT_NOTEQUAL", dst, Expression(ExpressionType.CONSTANT, value=0, size=8))
    src_nonnull = _cond("INT_NOTEQUAL", src, Expression(ExpressionType.CONSTANT, value=0, size=8))
    accumulate_taken = Condition(
        Expression(
            ExpressionType.BINARY_OP,
            operator="INT_EQUAL",
            operands=[copy_flag, Expression(ExpressionType.CONSTANT, value=0, size=4)],
            size=1,
        ),
        False,
    )
    params = [
        {"name": "dst", "index": 0, "size": 8},
        {"name": "src", "index": 1, "size": 8},
        {"name": "copy_flag", "index": 2, "size": 4},
    ]
    accumulated = Expression.binary_op(
        "INT_ADD",
        Expression.memory(dst, size=4),
        Expression.memory(src, size=4),
    )
    effects = [
        StoreEffect(
            location=CanonicalLocation(base_ref=LocationBaseRef.parameter("dst", index=0), offset=0, size=4),
            value=accumulated,
            conditions=[dst_nonnull, src_nonnull, accumulate_taken],
            order_key=7,
        ),
    ]
    value_expr = post_state_read_expression_for_location(
        CanonicalLocation(base_ref=LocationBaseRef.parameter("dst", index=0), offset=0, size=4),
        params,
        symbolic=True,
    )

    value_expr = lower_post_state_expression_for_smt(
        value_expr,
        [dst_nonnull, src_nonnull, accumulate_taken],
        effects,
        params,
    )
    assert isinstance(getattr(value_expr, "runtime_ref", None), PostStateValueRef)

    case = ReturnCase(
        index=0,
        conditions=[dst_nonnull, src_nonnull, accumulate_taken],
        value_expr=value_expr,
        return_info=ReturnInfo(
            address="0x1004",
            value=value_expr,
            conditions=[dst_nonnull, src_nonnull, accumulate_taken],
        ),
        parameters=params,
        effect_summary=EffectSummary(
            parameter_names=["dst", "src", "copy_flag"],
            effects=effects,
        ),
    )

    smt = case.get_value_smt(lambda expr: expr)

    assert smt.count("(select mem32 dst)") == 1
    assert smt.count("(select mem32 src)") == 1


def test_return_case_value_smt_lowers_nested_symbolic_post_state_reads_with_effect_summary():
    trace = Expression(ExpressionType.PARAMETER, name="trace", size=8)
    start = Expression(ExpressionType.PARAMETER, name="start", size=4)
    limit = Expression(ExpressionType.PARAMETER, name="limit", size=4)

    trace_nonnull = _cond("INT_NOTEQUAL", trace, _const(0))
    loop_active = _cond("INT_SLESS", start, limit)
    final_iter = _cond("INT_EQUAL", limit, Expression.binary_op("INT_ADD", start, _const(1)))
    odd_iteration = _cond(
        "INT_NOTEQUAL",
        Expression.binary_op("INT_AND", start, _const(1)),
        _const(0),
    )
    even_iteration = odd_iteration.negate()

    params = [
        {"name": "trace", "index": 0, "size": 8},
        {"name": "start", "index": 1, "size": 4},
        {"name": "limit", "index": 2, "size": 4},
    ]
    steps_addr = Expression.binary_op("INT_ADD", trace, _const(4))
    value_expr = Expression.binary_op(
        "INT_ADD",
        post_state_read_expression_for_location(
            _loc("trace", 0, 4),
            params,
            symbolic=True,
        ),
        Expression.binary_op(
            "INT_SUB",
            Expression.binary_op(
                "INT_ADD",
                limit,
                post_state_read_expression_for_location(
                    _loc("trace", 4, 4),
                    params,
                    symbolic=True,
                ),
            ),
            start,
        ),
    )
    effects = [
        StoreEffect(
            location=_loc("trace", 0, 4),
            value=Expression.binary_op("INT_ADD", Expression.memory(trace, size=4), _neg(start)),
            conditions=[trace_nonnull, loop_active, odd_iteration, final_iter],
            order_key=5,
        ),
        StoreEffect(
            location=_loc("trace", 0, 4),
            value=Expression.binary_op("INT_ADD", Expression.memory(trace, size=4), start),
            conditions=[trace_nonnull, loop_active, even_iteration, final_iter],
            order_key=5,
        ),
        StoreEffect(
            location=_loc("trace", 4, 4),
            value=Expression.binary_op(
                "INT_SUB",
                Expression.binary_op("INT_ADD", limit, Expression.memory(steps_addr, size=4)),
                start,
            ),
            conditions=[trace_nonnull, loop_active, final_iter],
            order_key=6,
        ),
    ]
    analysis = FunctionReturnAnalysis(
        function_name="f",
        entry_point="0x1000",
        parameters=params,
        returns=[
            ReturnInfo(
                address="0x1004",
                value=value_expr,
                conditions=[trace_nonnull, loop_active, odd_iteration, final_iter],
            )
        ],
        return_type="int",
        effect_summary=EffectSummary(
            parameter_names=["trace", "start", "limit"],
            effects=effects,
        ),
    )

    cases = extract_return_cases(analysis)

    assert len(cases) == 1
    smt = cases[0].get_value_smt(lambda expr: expr)
    assert "__locread__" not in smt
    assert "select mem32 trace" in smt
    assert "select mem32 (bvadd trace (_ bv4 64))" in smt


def test_return_case_value_smt_does_not_replay_explicit_prestate_expression_again():
    trace = Expression(ExpressionType.PARAMETER, name="param_1", size=8)
    start = Expression(ExpressionType.PARAMETER, name="param_2", size=4)
    limit = Expression(ExpressionType.PARAMETER, name="param_3", size=4)

    trace_nonnull = _cond("INT_NOTEQUAL", trace, _const(0))
    loop_active = _cond("INT_SLESS", start, limit)
    final_iter = _cond("INT_EQUAL", limit, Expression.binary_op("INT_ADD", start, _const(1)))
    odd_iteration = _cond(
        "INT_NOTEQUAL",
        Expression.binary_op("INT_AND", start, _const(1)),
        _const(0),
    )

    params = [
        {"name": "param_1", "index": 0, "size": 8},
        {"name": "param_2", "index": 1, "size": 4},
        {"name": "param_3", "index": 2, "size": 4},
    ]
    steps_addr = Expression.binary_op("INT_ADD", trace, _const(4))
    explicit_expr = Expression.binary_op(
        "INT_ADD",
        Expression.binary_op("INT_ADD", Expression.memory(steps_addr, size=4), _const(1)),
        Expression.binary_op("INT_ADD", _neg(start), Expression.memory(trace, size=4)),
    )
    effects = [
        StoreEffect(
            location=_loc("param_1", 0, 4),
            value=Expression.binary_op("INT_ADD", Expression.memory(trace, size=4), _neg(start)),
            conditions=[trace_nonnull, loop_active, odd_iteration, final_iter],
            order_key=5,
        ),
        StoreEffect(
            location=_loc("param_1", 4, 4),
            value=Expression.binary_op("INT_ADD", Expression.memory(steps_addr, size=4), _const(1)),
            conditions=[trace_nonnull, loop_active, final_iter],
            order_key=6,
        ),
    ]
    analysis = FunctionReturnAnalysis(
        function_name="f",
        entry_point="0x1000",
        parameters=params,
        returns=[
            ReturnInfo(
                address="0x1004",
                value=explicit_expr,
                conditions=[trace_nonnull, loop_active, odd_iteration, final_iter],
            )
        ],
        return_type="int",
        effect_summary=EffectSummary(
            parameter_names=["param_1", "param_2", "param_3"],
            effects=effects,
        ),
    )

    cases = extract_return_cases(analysis)

    assert len(cases) == 1
    smt = cases[0].get_value_smt(lambda expr: expr)
    assert "__locread__" not in smt
    assert smt.count("(bvneg param_2)") == 1
    assert smt.count("(_ bv1 32)") == 1


def test_return_analyzer_collapses_complementary_symbolic_post_state_cases_when_values_match():
    params = [{"name": "trace", "index": 0, "size": 8}]
    symbolic_value = post_state_read_expression_for_location(
        _loc("trace", 0, 4),
        params,
        symbolic=True,
    )
    assert symbolic_value is not None

    zero = _cond("INT_EQUAL", _param("param_1"), _const(0))
    nonzero = zero.negate()
    infos = [
        ReturnInfo(
            address="0x1001",
            value=symbolic_value,
            conditions=[zero],
        ),
        ReturnInfo(
            address="0x1001",
            value=symbolic_value,
            conditions=[nonzero],
        ),
    ]

    merged = ReturnAnalyzer(program=None, debug=False)._merge_equivalent_return_infos(infos)

    assert len(merged) == 1
    assert merged[0].conditions == []


def test_return_analyzer_keeps_pre_and_post_state_values_separate_even_when_rendering_matches():
    params = [
        {"name": "a", "index": 0, "size": 8},
        {"name": "b", "index": 1, "size": 8},
    ]
    nonnull = _cond("INT_NOTEQUAL", _param("a"), _const(0))
    null = nonnull.negate()

    pre_state = Expression.binary_op(
        "INT_SUB",
        Expression.memory(_param("a"), size=4),
        Expression.memory(_param("b"), size=4),
    )
    post_state = Expression.binary_op(
        "INT_SUB",
        post_state_read_expression_for_location(
            CanonicalLocation(base_ref=LocationBaseRef.parameter("a", index=0), offset=0, size=4),
            params,
            symbolic=True,
        ),
        post_state_read_expression_for_location(
            CanonicalLocation(base_ref=LocationBaseRef.parameter("b", index=1), offset=0, size=4),
            params,
            symbolic=True,
        ),
    )

    assert pre_state.to_string() == post_state.to_string()

    infos = [
        ReturnInfo(address="0x1001", value=pre_state, conditions=[nonnull]),
        ReturnInfo(address="0x1001", value=post_state, conditions=[null]),
    ]

    merged = ReturnAnalyzer(program=None, debug=False)._merge_equivalent_return_infos(infos)

    assert len(merged) == 2


def test_build_pair_query_coerces_case_values_to_return_width():
    case1 = ReturnCase(
        index=0,
        conditions=[],
        value_expr=Expression(ExpressionType.PARAMETER, name="param_1", size=8),
        return_info=ReturnInfo(address="0x1001", value=Expression(ExpressionType.PARAMETER, name="param_1", size=8)),
        return_type="ulong",
        return_type_obj=resolve_mock_data_type("ulong"),
    )
    case2 = ReturnCase(
        index=1,
        conditions=[],
        value_expr=Expression(ExpressionType.CONSTANT, value=2, size=4),
        return_info=ReturnInfo(address="0x1002", value=Expression(ExpressionType.CONSTANT, value=2, size=4)),
        return_type="ulong",
        return_type_obj=resolve_mock_data_type("ulong"),
    )

    query = build_pair_query(
        {"header_lines": [], "return_size1": 64, "return_size2": 64},
        case1,
        case2,
        lambda text: text,
        lambda text: text,
        "(0,1)",
    )

    assert "(assert (not (= param_1 ((_ zero_extend 32) (_ bv2 32)))))" in query


def test_build_pair_query_rejects_width_mismatch_overlap_without_bridge_proof():
    case1 = ReturnCase(
        index=0,
        conditions=[],
        value_expr=Expression(ExpressionType.PARAMETER, name="param_1", size=8),
        return_info=ReturnInfo(address="0x1001", value=Expression(ExpressionType.PARAMETER, name="param_1", size=8)),
        return_type="ulong",
        return_type_obj=resolve_mock_data_type("ulong"),
    )
    case2 = ReturnCase(
        index=1,
        conditions=[],
        value_expr=Expression(ExpressionType.PARAMETER, name="param_1", size=4),
        return_info=ReturnInfo(address="0x1002", value=Expression(ExpressionType.PARAMETER, name="param_1", size=4)),
        return_type="uint",
        return_type_obj=resolve_mock_data_type("uint"),
    )

    with pytest.raises(ValueError, match="return width mismatch|width mismatch"):
        build_pair_query(
            {"header_lines": [], "return_size1": 64, "return_size2": 32},
            case1,
            case2,
            lambda text: text,
            lambda text: text,
            "(0,1)",
        )


def test_pairwise_executor_returns_unknown_for_width_mismatch_without_overlap_query():
    case1 = ReturnCase(
        index=0,
        conditions=[],
        value_expr=Expression(ExpressionType.PARAMETER, name="param_1", size=8),
        return_info=ReturnInfo(address="0x1001", value=Expression(ExpressionType.PARAMETER, name="param_1", size=8)),
        return_type="ulong",
        return_type_obj=resolve_mock_data_type("ulong"),
    )
    case2 = ReturnCase(
        index=1,
        conditions=[],
        value_expr=Expression(ExpressionType.PARAMETER, name="param_1", size=4),
        return_info=ReturnInfo(address="0x1002", value=Expression(ExpressionType.PARAMETER, name="param_1", size=4)),
        return_type="uint",
        return_type_obj=resolve_mock_data_type("uint"),
    )

    class _Strategy:
        enable_solver_proven_rewrite_fallback = False
        enable_normalization_fallback = False
        _active_normalization_stats = {
            "unknown_results": 0,
            "return_width_bridge_missing": 0,
        }

        def _build_condition_only_query(self, *_args):
            return "(set-logic QF_BV)\n(check-sat)"

        def _solve_query_internal(self, *_args, **_kwargs):
            return QueryResult(is_equivalent=None)

        def _debug_print(self, _message):
            pass

    result = solve_query_twostage(
        _Strategy(),
        {"header_lines": [], "return_size1": 64, "return_size2": 32},
        case1,
        case2,
        lambda text: text,
        lambda text: text,
        "(0,1)",
    )

    assert result.is_equivalent is None
    assert result.pair_stage == "return-width-mismatch"
    assert result.blocking_reason == "return_width_bridge_missing"
    assert result.object_target_key is not None
    assert result.object_target_key == ("canonical_return_observation", "(0,1)")
    assert _Strategy._active_normalization_stats["unknown_results"] == 1
    assert _Strategy._active_normalization_stats["return_width_bridge_missing"] == 1

    reason = make_unknown_reason(
        result.blocking_reason,
        stage="S_PAIRWISE",
        pair_or_case="(0,1)",
        evidence_refs=(result.pair_stage, result.blocking_detail),
        object_target_key=result.object_target_key,
        detail=result.blocking_detail,
    )
    actions = build_unknown_recovery_actions([reason])

    assert {action.proof_stage for action in actions} == {
        "abi_relation",
        "high_bit_relation",
    }
    assert {action.proof_kind for action in actions} == {
        "abi_relation_proof",
        "high_bit_proof",
    }
    assert all(action.object_target_key == result.object_target_key for action in actions)
    assert all(action.proof_obligation_id is not None for action in actions)
    assert all(action.proof_obligation_id[-1] == result.object_target_key for action in actions)


def test_pairwise_executor_uses_semantic_abi_guard_unsat_before_return_width_backlog():
    case1 = ReturnCase(
        index=0,
        conditions=[],
        value_expr=Expression(ExpressionType.CONSTANT, value=1, size=8),
        return_info=ReturnInfo(address="0x1001", value=Expression(ExpressionType.CONSTANT, value=1, size=8)),
        return_type="long",
        return_type_obj=resolve_mock_data_type("long"),
    )
    case2 = ReturnCase(
        index=1,
        conditions=[],
        value_expr=Expression(ExpressionType.CONSTANT, value=0, size=4),
        return_info=ReturnInfo(address="0x1002", value=Expression(ExpressionType.CONSTANT, value=0, size=4)),
        return_type="int",
        return_type_obj=resolve_mock_data_type("int"),
    )

    class _Strategy:
        enable_solver_proven_rewrite_fallback = False
        enable_normalization_fallback = False
        _active_normalization_stats = {
            "unknown_results": 0,
            "return_width_bridge_missing": 0,
        }

        def __init__(self):
            self.calls = []

        def _build_condition_only_query(self, *_args):
            return "(set-logic QF_BV)\n(check-sat)"

        def _solve_query_internal(self, query, _pair_id, stage="full", **_kwargs):
            self.calls.append((stage, query))
            if stage == "conds-only-return-width-abi-guard":
                assert "Return-width guard ABI relations" in query
                assert "(assert (= param_1 ((_ sign_extend 32) param_1_2)))" in query
                return QueryResult(is_equivalent=True)
            return QueryResult(is_equivalent=None)

        def _debug_print(self, _message):
            pass

    strategy = _Strategy()
    result = solve_query_twostage(
        strategy,
        {
            "header_lines": [
                "(declare-const param_1 (_ BitVec 64))",
                "(declare-const param_1_2 (_ BitVec 32))",
            ],
            "params1": [
                _signed_semantic_param(
                    name="param_1",
                    suffix="",
                    bits=64,
                    semantic_bits=32,
                )
            ],
            "params2": [
                _signed_semantic_param(name="param_1", suffix="_2", bits=32)
            ],
            "return_size1": 64,
            "return_size2": 32,
        },
        case1,
        case2,
        lambda text: text,
        lambda text: text,
        "(0,1)",
    )

    assert result.is_equivalent is True
    assert result.pair_stage == "conds-only-return-width-abi-guard"
    assert [stage for stage, _query in strategy.calls] == [
        "conds-only",
        "conds-only-return-width-abi-guard",
    ]
    assert _Strategy._active_normalization_stats["unknown_results"] == 0
    assert _Strategy._active_normalization_stats["return_width_bridge_missing"] == 0


@pytest.mark.parametrize(
    ("semantic_bits", "abi_guard_result"),
    [
        (None, None),
        (32, False),
    ],
)
def test_pairwise_executor_keeps_return_width_backlog_without_proven_semantic_abi_guard(
    semantic_bits,
    abi_guard_result,
):
    case1 = ReturnCase(
        index=0,
        conditions=[],
        value_expr=Expression(ExpressionType.CONSTANT, value=1, size=8),
        return_info=ReturnInfo(address="0x1001", value=Expression(ExpressionType.CONSTANT, value=1, size=8)),
        return_type="long",
        return_type_obj=resolve_mock_data_type("long"),
    )
    case2 = ReturnCase(
        index=1,
        conditions=[],
        value_expr=Expression(ExpressionType.CONSTANT, value=0, size=4),
        return_info=ReturnInfo(address="0x1002", value=Expression(ExpressionType.CONSTANT, value=0, size=4)),
        return_type="int",
        return_type_obj=resolve_mock_data_type("int"),
    )

    class _Strategy:
        enable_solver_proven_rewrite_fallback = False
        enable_normalization_fallback = False
        _active_normalization_stats = {
            "unknown_results": 0,
            "return_width_bridge_missing": 0,
        }

        def __init__(self):
            self.calls = []

        def _build_condition_only_query(self, *_args):
            return "(set-logic QF_BV)\n(check-sat)"

        def _solve_query_internal(self, _query, _pair_id, stage="full", **_kwargs):
            self.calls.append(stage)
            if stage == "conds-only-return-width-abi-guard":
                return QueryResult(is_equivalent=abi_guard_result)
            return QueryResult(is_equivalent=None)

        def _debug_print(self, _message):
            pass

    strategy = _Strategy()
    result = solve_query_twostage(
        strategy,
        {
            "header_lines": [
                "(declare-const param_1 (_ BitVec 64))",
                "(declare-const param_1_2 (_ BitVec 32))",
            ],
            "params1": [
                _signed_semantic_param(
                    name="param_1",
                    suffix="",
                    bits=64,
                    semantic_bits=semantic_bits,
                )
            ],
            "params2": [
                _signed_semantic_param(name="param_1", suffix="_2", bits=32)
            ],
            "return_size1": 64,
            "return_size2": 32,
        },
        case1,
        case2,
        lambda text: text,
        lambda text: text,
        "(0,1)",
    )

    assert result.is_equivalent is None
    assert result.pair_stage == "return-width-mismatch"
    assert result.blocking_reason == "return_width_bridge_missing"
    expected_calls = ["conds-only"]
    if semantic_bits is not None:
        expected_calls.append("conds-only-return-width-abi-guard")
    assert strategy.calls == expected_calls
    assert _Strategy._active_normalization_stats["unknown_results"] == 1
    assert _Strategy._active_normalization_stats["return_width_bridge_missing"] == 1


def test_build_normalized_inequality_query_coerces_normalized_values_to_return_width():
    case1 = ReturnCase(
        index=0,
        conditions=[],
        value_expr=Expression(ExpressionType.PARAMETER, name="param_1", size=8),
        return_info=ReturnInfo(address="0x1001", value=Expression(ExpressionType.PARAMETER, name="param_1", size=8)),
        return_type="ulong",
        return_type_obj=resolve_mock_data_type("ulong"),
    )
    case2 = ReturnCase(
        index=1,
        conditions=[],
        value_expr=Expression(ExpressionType.CONSTANT, value=2, size=4),
        return_info=ReturnInfo(address="0x1002", value=Expression(ExpressionType.CONSTANT, value=2, size=4)),
        return_type="ulong",
        return_type_obj=resolve_mock_data_type("ulong"),
    )

    norm_expr = Expression(ExpressionType.CONSTANT, value=2, size=4)
    query = build_normalized_inequality_query(
        {"header_lines": [], "return_size1": 64, "return_size2": 64},
        case1,
        case2,
        lambda text: text,
        lambda text: text,
        norm_expr,
        norm_expr,
        "(_ bv2 32)",
        "(_ bv2 32)",
        "(0,1)",
    )

    assert "(assert (not (= ((_ zero_extend 32) (_ bv2 32)) ((_ zero_extend 32) (_ bv2 32)))))" in query


def test_build_pair_query_extracts_rendered_wide_value_back_to_declared_return_width():
    case1 = ReturnCase(
        index=0,
        conditions=[],
        value_expr=Expression(ExpressionType.PARAMETER, name="param_1", size=4),
        return_info=ReturnInfo(address="0x1001", value=Expression(ExpressionType.PARAMETER, name="param_1", size=4)),
        return_type="int",
    )
    wide_add = Expression(
        ExpressionType.BINARY_OP,
        operator="INT_ADD",
        operands=[
            Expression(ExpressionType.PARAMETER, name="param_1", size=4),
            Expression(ExpressionType.CONSTANT, value=7, size=8),
        ],
        size=4,
    )
    case2 = ReturnCase(
        index=1,
        conditions=[],
        value_expr=wide_add,
        return_info=ReturnInfo(address="0x1002", value=wide_add),
        return_type="int",
    )

    query = build_pair_query(
        {"header_lines": [], "return_size1": 32, "return_size2": 32},
        case1,
        case2,
        lambda text: text,
        lambda text: text,
        "(0,1)",
    )

    assert "(assert (not (= param_1 (bvadd param_1 (_ bv7 32)))))" in query


def test_build_pair_query_sign_extends_ambiguous_negative_constant_with_signed_evidence():
    signed_case = ReturnCase(
        index=0,
        conditions=[
            Condition(
                Expression(
                    ExpressionType.BINARY_OP,
                    operator="INT_SLESS",
                    operands=[
                        Expression(ExpressionType.PARAMETER, name="param_1", size=8),
                        Expression(ExpressionType.CONSTANT, value=-100, size=8),
                    ],
                    size=1,
                )
            )
        ],
        value_expr=Expression(ExpressionType.CONSTANT, value=0xFFFFFFFD, size=8),
        return_info=ReturnInfo(address="0x1003", value=Expression(ExpressionType.CONSTANT, value=0xFFFFFFFD, size=8)),
        return_type="undefined8",
    )
    other_case = ReturnCase(
        index=1,
        conditions=[],
        value_expr=Expression(ExpressionType.CONSTANT, value=0xFFFFFFFD, size=8),
        return_info=ReturnInfo(address="0x1004", value=Expression(ExpressionType.CONSTANT, value=0xFFFFFFFD, size=8)),
        return_type="undefined8",
    )

    query = build_pair_query(
        {"header_lines": [], "return_size1": 64, "return_size2": 64},
        signed_case,
        other_case,
        lambda text: text,
        lambda text: text,
        "(0,1)",
    )

    assert "(_ bv18446744073709551613 64)" in query


def test_nested_zero_extend_uses_rendered_operand_width_without_double_extension():
    param = Expression(ExpressionType.PARAMETER, name="param_1", size=4)
    wide_seven = Expression(ExpressionType.CONSTANT, value=7, size=8)
    inner_add = Expression(
        ExpressionType.BINARY_OP,
        operator="INT_ADD",
        operands=[param, wide_seven],
        size=4,
    )
    inner_zext = Expression(
        ExpressionType.UNARY_OP,
        operator="INT_ZEXT",
        operands=[inner_add],
        size=8,
    )
    mult_expr = Expression(
        ExpressionType.BINARY_OP,
        operator="INT_MULT",
        operands=[
            Expression(ExpressionType.CONSTANT, value=2, size=8),
            inner_zext,
        ],
        size=4,
    )
    outer_zext = Expression(
        ExpressionType.UNARY_OP,
        operator="INT_ZEXT",
        operands=[mult_expr],
        size=8,
    )

    smt = outer_zext.to_smt()

    assert "((_ zero_extend 32) (bvmul" not in smt
    assert smt == "(bvmul (_ bv2 64) ((_ zero_extend 32) (bvadd param_1 (_ bv7 32))))"


def test_readonly_identity_projection_producer_records_completed_proof_with_narrow_storage_type():
    strategy, reason, analysis1, analysis2, left_case, right_case = _readonly_projection_reason_and_analyses()

    strategy._record_completed_readonly_identity_projection_proof_if_safe(
        reason,
        analysis1,
        analysis2,
        left_case,
        right_case,
    )

    assert strategy._readonly_identity_proof_is_complete(reason, analysis1, analysis2) is True
    evidence = analysis1.completed_recovery_proof_evidence[0]
    content = evidence["proof_content"]
    assert content["parameter_extension"]["proof_source"] == "declared_parameter_narrow_type_on_wide_storage"
    assert content["parameter_extension"]["extension"] == "sign_extend"


def test_readonly_identity_projection_producer_records_completed_proof_with_object_signedness():
    class SignedDataType:
        def isSigned(self):
            return True

    strategy, reason, analysis1, analysis2, left_case, right_case = _readonly_projection_reason_and_analyses(
        left_param={"is_signed": None, "data_type_obj": SignedDataType()},
    )

    strategy._record_completed_readonly_identity_projection_proof_if_safe(
        reason,
        analysis1,
        analysis2,
        left_case,
        right_case,
    )

    assert strategy._readonly_identity_proof_is_complete(reason, analysis1, analysis2) is True
    content = analysis1.completed_recovery_proof_evidence[0]["proof_content"]
    assert content["parameter_extension"]["proof_source"] == "declared_parameter_narrow_type_on_wide_storage"
    assert content["parameter_extension"]["extension"] == "sign_extend"


def test_readonly_identity_declared_signedness_rejects_non_bool_values():
    assert PairwiseStrategy._readonly_parameter_declared_signedness({"is_signed": None}) is None
    assert PairwiseStrategy._readonly_parameter_declared_signedness({"is_signed": 1}) is None

    class NumericSignedDataType:
        def isSigned(self):
            return 1

    assert (
        PairwiseStrategy._readonly_parameter_declared_signedness(
            {"data_type_obj": NumericSignedDataType()},
        )
        is None
    )


def test_readonly_identity_projection_producer_rejects_missing_declared_signedness():
    strategy, reason, analysis1, analysis2, left_case, right_case = _readonly_projection_reason_and_analyses(
        left_param={"is_signed": None, "data_type_obj": None},
    )

    strategy._record_completed_readonly_identity_projection_proof_if_safe(
        reason,
        analysis1,
        analysis2,
        left_case,
        right_case,
    )

    assert analysis1.completed_recovery_proof_evidence == ()
    assert strategy._readonly_identity_proof_is_complete(reason, analysis1, analysis2) is False


def test_readonly_identity_projection_producer_rejects_data_type_obj_without_signedness():
    class OpaqueDataType:
        pass

    strategy, reason, analysis1, analysis2, left_case, right_case = _readonly_projection_reason_and_analyses(
        left_param={"is_signed": None, "data_type_obj": OpaqueDataType()},
    )

    strategy._record_completed_readonly_identity_projection_proof_if_safe(
        reason,
        analysis1,
        analysis2,
        left_case,
        right_case,
    )

    assert analysis1.completed_recovery_proof_evidence == ()
    assert strategy._readonly_identity_proof_is_complete(reason, analysis1, analysis2) is False


def test_readonly_identity_projection_producer_rejects_data_type_obj_unknown_signedness():
    class UnknownSignednessDataType:
        def isSigned(self):
            return None

    strategy, reason, analysis1, analysis2, left_case, right_case = _readonly_projection_reason_and_analyses(
        left_param={"is_signed": None, "data_type_obj": UnknownSignednessDataType()},
    )

    strategy._record_completed_readonly_identity_projection_proof_if_safe(
        reason,
        analysis1,
        analysis2,
        left_case,
        right_case,
    )

    assert analysis1.completed_recovery_proof_evidence == ()
    assert strategy._readonly_identity_proof_is_complete(reason, analysis1, analysis2) is False


def test_readonly_identity_projection_producer_rejects_term_contract_mismatch():
    wide_storage = _storage("a1", 0, 64)
    narrow_storage = _storage("a1_lo", 32, 32)
    left_ref = _readonly_projection_ref(storage=wide_storage, param_size=8)
    right_proof = ReductionAccumulatorProof(
        reduction_kind="memory_sum",
        pointer_base_ref=LocationBaseRef.parameter("base", index=0),
        count_parameter_name="count",
        count_parameter_index=1,
        count_parameter_storage_identity_key=narrow_storage.storage_identity_key(),
        limit_expr=Expression.parameter(
            "count",
            index=1,
            data_type="int",
            size=4,
            storage_info=narrow_storage,
        ),
        result_size=4,
        stride=8,
        element_size=4,
        index_scale=8,
        loop_body_witnesses=(
            ReadonlyReductionWitness(
                exact_count=1,
                terms=(ReadonlyReductionTermRef(byte_offset=0, access_size=4),),
            ),
        ),
    )
    right_ref = right_proof.lower_to_readonly_reduction_ref()
    assert right_ref is not None
    left_case = _readonly_projection_case(left_ref, param_size=4, storage=wide_storage)
    right_case = _readonly_projection_case(right_ref, param_size=4, storage=narrow_storage)
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    analysis1 = FunctionReturnAnalysis(
        function_name="f",
        entry_point="0x1000",
        parameters=left_case.parameters,
        returns=[left_case.return_info],
        return_type="int",
    )
    analysis2 = FunctionReturnAnalysis(
        function_name="f",
        entry_point="0x2000",
        parameters=right_case.parameters,
        returns=[right_case.return_info],
        return_type="int",
    )
    target = strategy._readonly_identity_object_target_key(
        base_ctx={"analysis1": analysis1, "analysis2": analysis2},
        case1=left_case,
        case2=right_case,
        pair_id="(0,0)",
    )
    reason = make_unknown_reason(
        UnknownReasonId.READONLY_IDENTITY_MISSING,
        stage="S_PAIRWISE",
        pair_or_case="(0,0)",
        evidence_kind="object_storage_identity",
        object_target_key=target,
    )

    strategy._record_completed_readonly_identity_projection_proof_if_safe(
        reason,
        analysis1,
        analysis2,
        left_case,
        right_case,
    )

    assert analysis1.completed_recovery_proof_evidence == ()
    assert strategy._readonly_identity_proof_is_complete(reason, analysis1, analysis2) is False

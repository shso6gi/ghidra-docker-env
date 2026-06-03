# -*- coding: utf-8 -*-
"""branch_sign_bucket 系の object-centric return-region 回帰テスト"""

from scripts.function_tracer_pcode.analysis.analyzer import ReturnAnalyzer
from scripts.function_tracer_pcode.analysis.condition import ConditionNormalizer
from scripts.function_tracer_pcode.analysis.condition.simplifier import ConditionSimplifier
from scripts.function_tracer_pcode.analysis.effect_summary import CanonicalLocation, EffectSummary, StoreEffect
from scripts.function_tracer_pcode.model import (
    CallTargetRef,
    Condition,
    DeferredCallInfo,
    Expression,
    ExpressionType,
    READONLY_SUM_OPCODE,
    ReturnInfo,
)
from scripts.function_tracer_pcode.model.runtime_refs import (
    LocationBaseRef,
    ReadonlyReductionRef,
    ReadonlyReductionTermRef,
    ReadonlyReductionWitness,
    ReductionAccumulatorProof,
)

from conftest import create_mock_analysis


def _test_parameter_index(name: str) -> int:
    if name.startswith("param_") and name[len("param_") :].isdigit():
        return max(0, int(name[len("param_") :]) - 1)
    value = 0
    for ch in name:
        value = ((value * 131) + ord(ch)) & 0xFFFF
    return 1000 + value


def _param(name: str, size: int = 4) -> Expression:
    index = _test_parameter_index(name)
    return Expression.parameter(
        name,
        index=index,
        size=size,
        runtime_ref=LocationBaseRef.parameter(name, index=index),
    )


def _const(value: int, size: int = 4) -> Expression:
    return Expression(ExpressionType.CONSTANT, value=value, size=size)


def _ptradd(base: Expression, index: int, element_size: int = 4) -> Expression:
    return Expression.intrinsic(
        "PTRADD",
        [base, _const(index, size=base.size), _const(element_size, size=base.size)],
        size=base.size,
    )


def _load_at(base: Expression, index: int, element_size: int = 4) -> Expression:
    address = base if index == 0 else _ptradd(base, index, element_size)
    return Expression.memory(address, size=element_size)


def _sum_terms(*terms: Expression) -> Expression:
    if not terms:
        return _const(0)
    value = terms[0]
    for term in terms[1:]:
        value = Expression.binary_op("INT_ADD", value, term)
    return value


def _proof_backed_readonly_ref(base_name: str, count: Expression) -> ReadonlyReductionRef:
    witness = ReadonlyReductionWitness(
        exact_count=3,
        terms=(
            ReadonlyReductionTermRef(byte_offset=0, access_size=4),
            ReadonlyReductionTermRef(byte_offset=4, access_size=4),
            ReadonlyReductionTermRef(byte_offset=8, access_size=4),
        ),
    )
    proof = ReductionAccumulatorProof(
        reduction_kind="memory_sum",
        pointer_base_ref=LocationBaseRef.parameter(base_name, index=0),
        count_parameter_name=getattr(count, "name", None) or "count",
        count_parameter_index=1,
        limit_expr=count,
        result_size=4,
        stride=4,
        element_size=4,
        exact_return_witnesses=(witness,),
        return_region_value_proven=True,
    )
    return ReadonlyReductionRef(
        reduction_kind="memory_sum",
        pointer_base_ref=LocationBaseRef.parameter(base_name, index=0),
        count_parameter_name=getattr(count, "name", None) or "count",
        count_parameter_index=1,
        stride=4,
        element_size=4,
        result_size=4,
        semantic_witnesses=(witness,),
        accumulator_proof=proof,
    )


def _cond(operator: str, left: Expression, right: Expression, *, negated: bool = False) -> Condition:
    return Condition(
        Expression(
            ExpressionType.BINARY_OP,
            operator=operator,
            operands=[left, right],
            size=1,
        ),
        negated=negated,
    )


def _bool_to_int(expr: Expression, size: int = 4) -> Expression:
    return Expression(
        ExpressionType.UNARY_OP,
        operator="INT_ZEXT",
        operands=[expr],
        size=size,
    )


def _branch_sign_bucket_tail_value(compare_operator: str = "INT_SLESS") -> Expression:
    selector = Expression(
        ExpressionType.BINARY_OP,
        operator=compare_operator,
        operands=[_const(100), _param("value")],
        size=1,
    )
    return Expression(
        ExpressionType.BINARY_OP,
        operator="INT_OR",
        operands=[_bool_to_int(selector), _const(2)],
        size=4,
    )


def test_condition_simplifier_reduces_signed_compare_to_false_under_negative_range():
    value = _param("value")
    expr = Expression.binary_op("INT_SLESS", _const(100), value)
    conditions = [
        _cond("INT_SLESS", _const(-101), value),
        _cond("INT_SLESS", value, _const(0)),
    ]

    reduced = ConditionSimplifier.reduce_expression_under_conditions(expr, conditions)

    assert reduced.expr_type == ExpressionType.CONSTANT
    assert reduced.value == 0


def test_return_analyzer_splits_boolean_or_value_into_exclusive_value_cases():
    analyzer = ReturnAnalyzer(program=None, debug=False)
    conditions = [
        _cond("INT_SLESS", _const(-101), _param("value")),
        _cond("INT_NOTEQUAL", _param("value"), _const(0)),
    ]

    cases = analyzer._split_object_centric_return_case(
        _branch_sign_bucket_tail_value(),
        conditions,
    )

    assert len(cases) == 2
    assert {case_value.value for case_value, _case_conditions in cases} == {2, 3}

    left = ConditionSimplifier.build_constraint_set(cases[0][1])
    right = ConditionSimplifier.build_constraint_set(cases[1][1])
    assert left.overlaps_with(right.conditions) is False


def test_return_analyzer_exclusivizes_shadowed_branch_sign_bucket_regions():
    analyzer = ReturnAnalyzer(program=None, debug=False)
    negative_conditions = [
        _cond("INT_SLESS", _const(-101), _param("value")),
        _cond("INT_SLESS", _param("value"), _const(0)),
    ]
    merged_conditions = [
        _cond("INT_SLESS", _const(-101), _param("value")),
        _cond("INT_NOTEQUAL", _param("value"), _const(0)),
    ]

    split_tail_infos = [
        ReturnInfo(address="0x1008", value=value, conditions=conditions, branch_index=20 + index)
        for index, (value, conditions) in enumerate(
            analyzer._split_object_centric_return_case(
                _branch_sign_bucket_tail_value(),
                merged_conditions,
            )
        )
    ]

    exclusivized = analyzer._exclusivize_return_regions(
        [
            ReturnInfo(
                address="0x1004",
                value=_const(-2),
                conditions=negative_conditions,
                branch_index=10,
            ),
            *split_tail_infos,
        ]
    )

    assert len(exclusivized) == 3
    values = sorted(int(info.value.value) for info in exclusivized)
    assert values == [-2, 2, 3]

    negative_info = next(info for info in exclusivized if int(info.value.value) == -2)
    plus_two_info = next(info for info in exclusivized if int(info.value.value) == 2)
    plus_three_info = next(info for info in exclusivized if int(info.value.value) == 3)

    negative_region = ConditionSimplifier.build_constraint_set(negative_info.conditions)
    plus_two_region = ConditionSimplifier.build_constraint_set(plus_two_info.conditions)
    plus_three_region = ConditionSimplifier.build_constraint_set(plus_three_info.conditions)

    assert negative_region.overlaps_with(plus_two_region.conditions) is False
    assert negative_region.overlaps_with(plus_three_region.conditions) is False
    assert plus_two_region.overlaps_with(plus_three_region.conditions) is False


def test_return_analyzer_exclusivization_honors_readonly_runtime_guards():
    analyzer = ReturnAnalyzer(program=None, debug=False)
    base = _param("param_1", size=8)
    count = _param("param_2", size=4)
    zero64 = _const(0, size=8)
    null_expr = Expression.binary_op("INT_EQUAL", base, zero64)
    nonpositive_expr = Expression.binary_op("INT_SLESS", count, _const(1))
    early_or = Condition(Expression.binary_op("BOOL_OR", null_expr, nonpositive_expr))
    not_null = Condition(null_expr, negated=True)
    positive_count = _cond("INT_SLESS", _const(0), count)
    count_le_three = _cond("INT_SLESSEQUAL", count, _const(3))
    proof = ReductionAccumulatorProof(
        reduction_kind="memory_sum",
        pointer_base_ref=LocationBaseRef.parameter("param_1", index=0),
        count_parameter_name="param_2",
        count_parameter_index=1,
        limit_expr=count,
        result_size=4,
        stride=4,
        element_size=4,
        guard_constraints=(positive_count,),
        return_region_value_proven=True,
    )
    summary_value = Expression.intrinsic(
        "READONLY_SUM",
        [base, count],
        size=4,
        runtime_ref=ReadonlyReductionRef(
            reduction_kind="memory_sum",
            pointer_base_ref=LocationBaseRef.parameter("param_1", index=0),
            count_parameter_name="param_2",
            count_parameter_index=1,
            stride=4,
            element_size=4,
            result_size=4,
            accumulator_proof=proof,
        ),
        opcode=READONLY_SUM_OPCODE,
    )
    summary = ReturnInfo(
        address="0x2000",
        value=summary_value,
        conditions=[not_null, count_le_three],
        branch_index=10,
    )
    early = ReturnInfo(
        address="0x2004",
        value=_const(-300),
        conditions=[early_or],
        branch_index=11,
    )

    exclusivized = analyzer._exclusivize_return_regions([summary, early])

    nonpositive_not_null = [not_null, Condition(nonpositive_expr)]
    early_regions = [
        info for info in exclusivized
        if getattr(info.value, "expr_type", None) == ExpressionType.CONSTANT
        and int(info.value.value) == -300
    ]
    summary_regions = [
        info for info in exclusivized
        if getattr(info.value, "expr_type", None) == ExpressionType.INTRINSIC
    ]

    assert any(
        ConditionSimplifier.build_constraint_set(info.conditions).overlaps_with(nonpositive_not_null)
        for info in early_regions
    )
    assert all(
        not ConditionSimplifier.build_constraint_set(info.conditions).overlaps_with(nonpositive_not_null)
        for info in summary_regions
    )


def test_runtime_guards_are_attached_to_active_phi_value_case_only():
    analyzer = ReturnAnalyzer(program=None, debug=False)
    base = _param("param_1", size=8)
    count = Expression.parameter("param_2", index=1, size=4)
    flag = Expression.parameter("flag", index=2, size=4)
    branch_guard = _cond("INT_EQUAL", flag, _const(1))
    positive_count = _cond("INT_SLESS", _const(0), count)
    nonpositive_count = _cond("INT_SLESSEQUAL", count, _const(0))
    proof = ReductionAccumulatorProof(
        reduction_kind="memory_sum",
        pointer_base_ref=LocationBaseRef.parameter("param_1", index=0),
        count_parameter_name="param_2",
        count_parameter_index=1,
        limit_expr=count,
        result_size=4,
        stride=4,
        element_size=4,
        guard_constraints=(positive_count,),
        return_region_value_proven=True,
    )
    summary_value = Expression.intrinsic(
        "READONLY_SUM",
        [base, count],
        size=4,
        runtime_ref=ReadonlyReductionRef(
            reduction_kind="memory_sum",
            pointer_base_ref=LocationBaseRef.parameter("param_1", index=0),
            count_parameter_name="param_2",
            count_parameter_index=1,
            stride=4,
            element_size=4,
            result_size=4,
            accumulator_proof=proof,
        ),
        opcode=READONLY_SUM_OPCODE,
    )
    phi_value = Expression.phi(
        [
            (branch_guard, summary_value),
            (None, _const(-300)),
        ]
    )
    phi_value.size = 4

    cases = analyzer._split_object_centric_return_case(phi_value, [])

    summary_cases = [case for case in cases if case[0].expr_type == ExpressionType.INTRINSIC]
    constant_cases = [case for case in cases if case[0].expr_type == ExpressionType.CONSTANT]

    assert len(summary_cases) == 1
    assert any(
        ConditionNormalizer.are_equivalent(condition, positive_count)
        for condition in summary_cases[0][1]
    )
    assert len(constant_cases) == 1
    constant_region = ConditionSimplifier.build_constraint_set(constant_cases[0][1])
    assert constant_region.overlaps_with([nonpositive_count]) is True
    assert not any(
        ConditionNormalizer.are_equivalent(condition, positive_count)
        for condition in constant_cases[0][1]
    )


def test_return_analyzer_prioritizes_exact_region_over_broad_phi_fallback():
    analyzer = ReturnAnalyzer(program=None, debug=False)
    broad_fallback = ReturnInfo(
        address="0x2000",
        value=_const(99),
        conditions=[
            _cond("INT_SLESS", _param("count"), _const(4)),
        ],
        branch_index=10,
    )
    exact_path = ReturnInfo(
        address="0x2000",
        value=_const(33),
        conditions=[
            _cond("INT_EQUAL", _param("count"), _const(3)),
        ],
        branch_index=11,
    )

    exclusivized = analyzer._exclusivize_return_regions([broad_fallback, exact_path])

    exact_info = next(info for info in exclusivized if int(info.value.value) == 33)
    fallback_infos = [info for info in exclusivized if int(info.value.value) == 99]

    assert any(
        ConditionNormalizer.are_equivalent(condition, exact_path.conditions[0])
        for condition in exact_info.conditions
    )
    exact_region = ConditionSimplifier.build_constraint_set(exact_info.conditions)
    for fallback_info in fallback_infos:
        fallback_region = ConditionSimplifier.build_constraint_set(fallback_info.conditions)
        assert fallback_region.overlaps_with(exact_region.conditions) is False


def test_return_analyzer_preserves_deferred_call_region_without_shadow_proof():
    analyzer = ReturnAnalyzer(program=None, debug=False)
    value = _param("param_1")
    deferred = DeferredCallInfo(
        placeholder_name="call_out_of_scope:callee#0",
        target_ref=CallTargetRef.from_name("callee"),
        arguments=[Expression.binary_op("INT_SUB", value, _const(1))],
        sequence=0,
    )
    unresolved_recursive_case = ReturnInfo(
        address="0x2400",
        value=Expression.unknown(
            deferred.placeholder_name,
            runtime_ref=deferred.unknown_ref,
        ),
        conditions=[
            Condition(
                Expression.binary_op(
                    "INT_NOTEQUAL",
                    Expression.binary_op(
                        "INT_ADD",
                        Expression.unknown("phi_circular"),
                        _const(0xFFFFFFFF),
                    ),
                    _const(0),
                )
            )
        ],
        branch_index=20,
    )
    concrete_case = ReturnInfo(
        address="0x2400",
        value=_const(0),
        conditions=[_cond("INT_EQUAL", value, _const(0))],
        branch_index=10,
    )

    can_shadow = analyzer._return_region_can_be_shadowed_by_prior(
        unresolved_recursive_case.conditions,
        unresolved_recursive_case,
        concrete_case,
        prior_conditions=concrete_case.conditions,
    )

    assert can_shadow is False


def test_return_analyzer_orders_proven_specific_region_before_broad_region():
    analyzer = ReturnAnalyzer(program=None, debug=False)
    value = _param("value")
    broad = ReturnInfo(
        address="0x2400",
        value=_const(1),
        conditions=[_cond("INT_NOTEQUAL", value, _const(0))],
        branch_index=10,
    )
    specific = ReturnInfo(
        address="0x2404",
        value=_const(2),
        conditions=[
            _cond("INT_NOTEQUAL", value, _const(0)),
            _cond("INT_SLESS", value, _const(3)),
        ],
        branch_index=11,
    )

    exclusivized = analyzer._exclusivize_return_regions([broad, specific])

    specific_info = next(info for info in exclusivized if int(info.value.value) == 2)
    assert ConditionSimplifier.build_constraint_set(specific_info.conditions).implies_all(
        specific.conditions
    )


def test_return_analyzer_does_not_shadow_same_region_with_unproven_readonly_prefix_shape():
    analyzer = ReturnAnalyzer(program=None, debug=False)
    base = _param("base", size=8)
    count = Expression.parameter("count", index=1, size=4)
    conditions = [_cond("INT_EQUAL", count, _const(3))]
    wrong_tail_artifact = _sum_terms(
        _load_at(base, 0),
        _load_at(base, 2),
        _load_at(base, 3),
    )
    exact_prefix = _sum_terms(
        _load_at(base, 1),
        _load_at(base, 0),
        _load_at(base, 2),
    )

    exclusivized = analyzer._exclusivize_return_regions(
        [
            ReturnInfo(
                address="0x3000",
                value=wrong_tail_artifact,
                conditions=conditions,
                branch_index=10,
            ),
            ReturnInfo(
                address="0x3000",
                value=exact_prefix,
                conditions=conditions,
                branch_index=11,
            ),
        ]
    )

    assert len(exclusivized) == 2


def test_return_analyzer_prefers_proof_backed_readonly_region_over_same_region_artifact():
    analyzer = ReturnAnalyzer(program=None, debug=False)
    base = _param("base", size=8)
    count = Expression.parameter("count", index=1, size=4)
    conditions = [_cond("INT_EQUAL", count, _const(3))]
    wrong_tail_artifact = _sum_terms(
        _load_at(base, 0),
        _load_at(base, 2),
        _load_at(base, 3),
    )
    exact_prefix = _sum_terms(
        _load_at(base, 1),
        _load_at(base, 0),
        _load_at(base, 2),
    )
    exact_prefix.runtime_ref = _proof_backed_readonly_ref("base", count)

    exclusivized = analyzer._exclusivize_return_regions(
        [
            ReturnInfo(
                address="0x3000",
                value=wrong_tail_artifact,
                conditions=conditions,
                branch_index=10,
            ),
            ReturnInfo(
                address="0x3000",
                value=exact_prefix,
                conditions=conditions,
                branch_index=11,
            ),
        ]
    )

    assert len(exclusivized) == 1
    assert exclusivized[0].value.structural_key(
        include_memory_read_order=False,
        include_semantic_runtime_refs=False,
    ) == exact_prefix.structural_key(
        include_memory_read_order=False,
        include_semantic_runtime_refs=False,
    )


def test_effect_sensitive_rewrite_does_not_treat_nontrivial_wrapper_as_location_carrier():
    analyzer = ReturnAnalyzer(program=None, debug=False)
    base = _param("trace", size=8)
    delta = _param("delta")
    count_location = CanonicalLocation(
        base_ref=LocationBaseRef.parameter("trace", index=0),
        offset=4,
        size=4,
    )
    count_read = _load_at(base, 1)
    original = Expression.binary_op(
        "INT_ADD",
        delta,
        Expression.binary_op("INT_ADD", count_read, _const(2)),
    )
    effect_summary = EffectSummary(
        parameter_names=["trace", "delta"],
        effects=[
            StoreEffect(
                location=count_location,
                value=Expression.binary_op("INT_ADD", count_read, _const(2)),
                conditions=[],
                order_key=1,
            )
        ],
    )
    analyzer._current_parameters = [
        {"name": "trace", "index": 0, "size": 8, "data_type": "int *"},
        {"name": "delta", "index": 1, "size": 4, "data_type": "int"},
    ]

    candidates = list(analyzer._iter_effect_sensitive_rewrite_candidates(original, [], effect_summary))

    assert all(kind != "final object-state symbolic" for kind, _candidate in candidates)


def test_return_analyzer_repairs_mixed_scalar_signedness_from_scalar_evidence():
    analyzer = ReturnAnalyzer(program=None, debug=False)
    analysis = create_mock_analysis(
        function_name="branch_sign_bucket",
        parameters=[
            {"name": "value", "data_type": "int", "size": 4, "index": 0},
        ],
        returns=[
            ReturnInfo(
                address="0x1004",
                value=_const(-2),
                conditions=[
                    _cond("INT_SLESS", _const(-101), _param("value")),
                    _cond("INT_SLESS", _param("value"), _const(0)),
                ],
                branch_index=10,
            ),
            ReturnInfo(
                address="0x1008",
                value=_branch_sign_bucket_tail_value(compare_operator="INT_LESS"),
                conditions=[
                    _cond("INT_SLESS", _const(-101), _param("value")),
                    _cond("INT_NOTEQUAL", _param("value"), _const(0)),
                ],
                branch_index=20,
            ),
        ],
    )

    analyzer._repair_mixed_scalar_signedness(analysis)

    repaired_value = analysis.returns[1].value
    assert repaired_value.operands[0].operator == "INT_ZEXT"
    assert repaired_value.operands[0].operands[0].operator == "INT_SLESS"
    assert "object_centric_scalar_signedness_repair" in analysis.analysis_notes

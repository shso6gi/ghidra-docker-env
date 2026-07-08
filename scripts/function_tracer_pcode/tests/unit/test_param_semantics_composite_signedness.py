# -*- coding: utf-8 -*-
"""Composite signedness inference regressions."""

from scripts.function_tracer_pcode.equivalence.arch.mips64 import MIPS64Handler
from scripts.function_tracer_pcode.equivalence.formula.builder import FormulaBuilder
from scripts.function_tracer_pcode.equivalence.param_semantics import (
    hint_objects_by_name,
    infer_parameter_semantics,
    infer_parameter_semantics_by_identity,
)
from scripts.function_tracer_pcode.equivalence.typing.fixer import TypeFixerConfig
from scripts.function_tracer_pcode.equivalence.typing.signedness_param_fix import ParamSignednessFixer
from scripts.function_tracer_pcode.model import (
    Condition,
    Expression,
    ExpressionType,
    FunctionReturnAnalysis,
    LocationBaseRef,
    ReadonlyReductionRef,
    ReturnInfo,
    StorageInfo,
)

from conftest import create_mock_analysis


def _param(name: str, size: int = 8, *, index: int = -1, storage_info=None) -> Expression:
    return Expression(
        ExpressionType.PARAMETER,
        name=name,
        value=index,
        size=size,
        storage_info=storage_info,
    )


def _const(value: int, size: int = 8) -> Expression:
    return Expression(ExpressionType.CONSTANT, value=value, size=size)


def _binary(operator: str, left: Expression, right: Expression, size: int) -> Expression:
    return Expression(
        ExpressionType.BINARY_OP,
        operator=operator,
        operands=[left, right],
        size=size,
    )


def _mask32(name: str, source_size: int = 8, *, index: int = -1, storage_info=None) -> Expression:
    return _binary(
        "INT_AND",
        _param(name, source_size, index=index, storage_info=storage_info),
        _const(0xFFFFFFFF, source_size),
        source_size,
    )


def _or_guard_condition(
    name1: str,
    name2: str,
    size: int = 8,
    *,
    index1: int = -1,
    index2: int = -1,
) -> Condition:
    return Condition(
        _binary(
            "INT_SLESS",
            _const(-1, size),
            _binary(
                "INT_OR",
                _param(name1, size, index=index1),
                _param(name2, size, index=index2),
                size,
            ),
            1,
        ),
        negated=False,
    )


def _sum_guard_condition(
    name1: str,
    name2: str,
    size: int = 8,
    *,
    index1: int = -1,
    index2: int = -1,
) -> Condition:
    return Condition(
        _binary(
            "INT_SLESS",
            _const(-1, size),
            _binary(
                "INT_ADD",
                _param(name1, size, index=index1),
                _param(name2, size, index=index2),
                size,
            ),
            1,
        ),
        negated=False,
    )


def _analysis_with_guard(condition: Condition) -> FunctionReturnAnalysis:
    masked_union = _binary(
        "INT_OR",
        _mask32("param_1", index=0),
        _mask32("param_2", index=1),
        8,
    )
    return FunctionReturnAnalysis(
        function_name="branch_multi_guard_like",
        entry_point="0x1000",
        parameters=[
            {"name": "param_1", "data_type": "ulong", "size": 8, "index": 0, "is_signed": False},
            {"name": "param_2", "data_type": "ulong", "size": 8, "index": 1, "is_signed": False},
        ],
        returns=[
            ReturnInfo(address="0x1000", conditions=[condition], value=masked_union),
        ],
    )


def _analysis_with_same_width_signedness_conflict() -> FunctionReturnAnalysis:
    count = _param("count", 4, index=0)
    return FunctionReturnAnalysis(
        function_name="signed_count_tail_like",
        entry_point="0x2000",
        parameters=[
            {
                "name": "count",
                "data_type": "uint",
                "size": 4,
                "index": 0,
                "is_signed": False,
                "storage": {"kind": "register", "size": 4, "size_bits": 32},
            }
        ],
        returns=[
            ReturnInfo(
                address="0x2000",
                conditions=[Condition(_binary("INT_SLESS", _const(0, 4), count, 1))],
                value=_const(1, 4),
            ),
            ReturnInfo(
                address="0x2001",
                conditions=[Condition(_binary("INT_LESS", _const(3, 4), count, 1))],
                value=_const(2, 4),
            ),
        ],
    )


def _analysis_with_storage_backed_narrowing() -> FunctionReturnAnalysis:
    count = _param("count", 8, index=0)
    return FunctionReturnAnalysis(
        function_name="mips64_signed_count_tail_like",
        entry_point="0x3000",
        parameters=[
            {
                "name": "count",
                "data_type": "ulong",
                "size": 8,
                "index": 0,
                "is_signed": False,
                "storage": {
                    "kind": "register",
                    "size": 4,
                    "size_bits": 32,
                    "base_register_size_bits": 64,
                },
            }
        ],
        returns=[
            ReturnInfo(
                address="0x3000",
                conditions=[Condition(_binary("INT_SLESS", _const(0, 8), count, 1))],
                value=_const(1, 4),
            ),
            ReturnInfo(
                address="0x3001",
                conditions=[Condition(_binary("INT_LESS", _const(3, 8), count, 1))],
                value=_const(2, 4),
            ),
        ],
    )


def _analysis_with_narrowed_direct_unsigned_and_composite_signed() -> FunctionReturnAnalysis:
    count = _param("count", 8, index=0)
    flags = _param("flags", 8, index=1)
    return FunctionReturnAnalysis(
        function_name="narrowed_direct_unsigned_with_composite_signed_like",
        entry_point="0x3200",
        parameters=[
            {
                "name": "count",
                "data_type": "ulong",
                "size": 8,
                "index": 0,
                "is_signed": False,
                "storage": {
                    "kind": "register",
                    "size": 4,
                    "size_bits": 32,
                    "base_register_size_bits": 64,
                },
            },
            {
                "name": "flags",
                "data_type": "ulong",
                "size": 8,
                "index": 1,
                "is_signed": False,
            },
        ],
        returns=[
            ReturnInfo(
                address="0x3200",
                conditions=[Condition(_binary("INT_LESS", _const(3, 8), count, 1))],
                value=_const(1, 4),
            ),
            ReturnInfo(
                address="0x3201",
                conditions=[
                    Condition(
                        _binary(
                            "INT_SLESS",
                            _const(-1, 8),
                            _binary("INT_OR", count, flags, 8),
                            1,
                        )
                    )
                ],
                value=_const(2, 4),
            ),
        ],
    )


def _analysis_with_same_width_composite_signed_test() -> FunctionReturnAnalysis:
    return FunctionReturnAnalysis(
        function_name="same_width_or_guard_like",
        entry_point="0x3500",
        parameters=[
            {"name": "param_1", "data_type": "uint", "size": 4, "index": 0, "is_signed": False},
            {"name": "param_2", "data_type": "uint", "size": 4, "index": 1, "is_signed": False},
        ],
        returns=[
            ReturnInfo(
                address="0x3500",
                conditions=[_or_guard_condition("param_1", "param_2", size=4, index1=0, index2=1)],
                value=_binary(
                    "INT_OR",
                    _param("param_1", 4, index=0),
                    _param("param_2", 4, index=1),
                    4,
                ),
            )
        ],
    )


def _analysis_with_zext_wrapped_signed_compare() -> FunctionReturnAnalysis:
    count = _param("count", 4, index=0)
    wrapped = Expression.unary_op("INT_ZEXT", count)
    wrapped.size = 8
    return FunctionReturnAnalysis(
        function_name="zext_wrapped_signed_compare_like",
        entry_point="0x3550",
        parameters=[
            {"name": "count", "data_type": "uint", "size": 4, "index": 0, "is_signed": False},
        ],
        returns=[
            ReturnInfo(
                address="0x3550",
                conditions=[Condition(_binary("INT_SLESS", _const(0, 8), wrapped, 1))],
                value=_const(1, 4),
            )
        ],
    )


def _analysis_with_storage_narrowing_and_zext_wrapped_signed_compare() -> FunctionReturnAnalysis:
    count = _param("count", 8, index=0)
    low_count = _binary("SUBPIECE", count, _const(0, 4), 4)
    wrapped = Expression.unary_op("INT_ZEXT", low_count)
    wrapped.size = 8
    return FunctionReturnAnalysis(
        function_name="storage_narrowing_zext_wrapped_signed_compare_like",
        entry_point="0x3570",
        parameters=[
            {
                "name": "count",
                "data_type": "ulong",
                "size": 8,
                "index": 0,
                "is_signed": False,
                "storage": {
                    "kind": "register",
                    "size": 4,
                    "size_bits": 32,
                    "base_register_size_bits": 64,
                },
            }
        ],
        returns=[
            ReturnInfo(
                address="0x3570",
                conditions=[Condition(_binary("INT_SLESS", _const(0, 8), wrapped, 1))],
                value=_const(1, 4),
            )
        ],
    )


def _analysis_with_storage_narrowing_and_pure_composite_signed_compare() -> FunctionReturnAnalysis:
    count = _param("count", 8, index=0)
    flags = _param("flags", 8, index=1)
    return FunctionReturnAnalysis(
        function_name="storage_narrowing_pure_composite_signed_compare_like",
        entry_point="0x3580",
        parameters=[
            {
                "name": "count",
                "data_type": "ulong",
                "size": 8,
                "index": 0,
                "is_signed": False,
                "storage": {
                    "kind": "register",
                    "size": 4,
                    "size_bits": 32,
                    "base_register_size_bits": 64,
                },
            },
            {
                "name": "flags",
                "data_type": "ulong",
                "size": 8,
                "index": 1,
                "is_signed": False,
            },
        ],
        returns=[
            ReturnInfo(
                address="0x3580",
                conditions=[
                    Condition(
                        _binary(
                            "INT_SLESS",
                            _const(-1, 8),
                            _binary("INT_OR", count, flags, 8),
                            1,
                        )
                    )
                ],
                value=_const(1, 4),
            )
        ],
    )


def _analysis_with_readonly_sum_signed_counter() -> FunctionReturnAnalysis:
    base = _param("base", 8, index=0)
    count = _param("count", 8, index=1)
    readonly_ref = ReadonlyReductionRef(
        reduction_kind="unit_test",
        pointer_base_ref=LocationBaseRef.parameter("base", index=0),
        count_parameter_name="count",
        count_parameter_index=1,
        stride=4,
        element_size=4,
        result_size=4,
        signed_counter=True,
    )
    value = Expression.intrinsic("READONLY_SUM", [base, count], size=4, runtime_ref=readonly_ref)
    return FunctionReturnAnalysis(
        function_name="readonly_sum_signed_counter_like",
        entry_point="0x3600",
        parameters=[
            {"name": "base", "data_type": "int *", "size": 8, "index": 0, "is_signed": False},
            {"name": "count", "data_type": "ulong", "size": 8, "index": 1, "is_signed": False},
        ],
        returns=[
            ReturnInfo(
                address="0x3600",
                conditions=[],
                value=value,
            )
        ],
    )


def _analysis_with_mixed_direct_unsigned_and_composite_signed_test() -> FunctionReturnAnalysis:
    count = _param("count", 4, index=0)
    flags = _param("flags", 4, index=1)
    return FunctionReturnAnalysis(
        function_name="mixed_signedness_evidence_like",
        entry_point="0x3600",
        parameters=[
            {"name": "count", "data_type": "uint", "size": 4, "index": 0, "is_signed": False},
            {"name": "flags", "data_type": "uint", "size": 4, "index": 1, "is_signed": False},
        ],
        returns=[
            ReturnInfo(
                address="0x3600",
                conditions=[Condition(_binary("INT_LESS", _const(3, 4), count, 1))],
                value=_const(1, 4),
            ),
            ReturnInfo(
                address="0x3601",
                conditions=[
                    Condition(
                        _binary(
                            "INT_SLESS",
                            _const(-1, 4),
                            _binary("INT_OR", count, flags, 4),
                            1,
                        )
                    )
                ],
                value=_const(2, 4),
            ),
        ],
    )


def _analysis_with_direct_tie_and_composite_signed_tiebreak() -> FunctionReturnAnalysis:
    count = _param("count", 4, index=0)
    flags = _param("flags", 4, index=1)
    return FunctionReturnAnalysis(
        function_name="direct_tie_with_composite_tiebreak_like",
        entry_point="0x3700",
        parameters=[
            {"name": "count", "data_type": "uint", "size": 4, "index": 0, "is_signed": False},
            {"name": "flags", "data_type": "uint", "size": 4, "index": 1, "is_signed": False},
        ],
        returns=[
            ReturnInfo(
                address="0x3700",
                conditions=[Condition(_binary("INT_SLESS", _const(3, 4), count, 1))],
                value=_const(1, 4),
            ),
            ReturnInfo(
                address="0x3701",
                conditions=[Condition(_binary("INT_LESS", _const(3, 4), count, 1))],
                value=_const(2, 4),
            ),
            ReturnInfo(
                address="0x3702",
                conditions=[
                    Condition(
                        _binary(
                            "INT_SLESS",
                            _const(-1, 4),
                            _binary("INT_OR", count, flags, 4),
                            1,
                        )
                    )
                ],
                value=_const(3, 4),
            ),
        ],
    )


def test_infer_parameter_semantics_propagates_signedness_through_bitwise_or_compare():
    analysis = _analysis_with_guard(_or_guard_condition("param_1", "param_2", index1=0, index2=1))

    hints = infer_parameter_semantics(analysis)

    assert hints[0].narrow_bits == 32
    assert hints[0].signedness == "unknown"
    assert hints[0].signedness_source == "width_only"
    assert hints[1].narrow_bits == 32
    assert hints[1].signedness == "unknown"
    assert hints[1].signedness_source == "width_only"


def test_infer_parameter_semantics_stays_conservative_for_arithmetic_composites():
    analysis = _analysis_with_guard(_sum_guard_condition("param_1", "param_2", index1=0, index2=1))

    hints = infer_parameter_semantics(analysis)

    assert hints[0].narrow_bits == 32
    assert hints[0].signedness == "unknown"
    assert hints[0].signedness_source == "width_only"
    assert hints[1].narrow_bits == 32
    assert hints[1].signedness == "unknown"
    assert hints[1].signedness_source == "width_only"


def test_infer_parameter_semantics_does_not_use_name_only_parameter_reference():
    analysis = FunctionReturnAnalysis(
        function_name="name_only_count_reference",
        entry_point="0x1800",
        parameters=[
            {"name": "count", "data_type": "ulong", "size": 8, "index": 0, "is_signed": False},
        ],
        returns=[
            ReturnInfo(
                address="0x1800",
                conditions=[],
                value=_mask32("count"),
            )
        ],
    )

    assert infer_parameter_semantics(analysis) == {}


def test_infer_parameter_semantics_does_not_double_count_index_and_storage_identity():
    storage = StorageInfo(
        is_register=True,
        space_name="register",
        register_name="a0",
        base_register_name="a0",
        size=4,
        size_bits=32,
    )
    indexed_count = _param("count", 4, index=0, storage_info=storage)
    storage_count = _param("count_alias", 4, storage_info=storage)
    analysis = FunctionReturnAnalysis(
        function_name="mixed_identity_signedness_evidence",
        entry_point="0x1900",
        parameters=[
            {
                "name": "count",
                "data_type": "int",
                "size": 4,
                "index": 0,
                "is_signed": True,
                "storage": storage,
            },
        ],
        returns=[
            ReturnInfo(
                address="0x1900",
                conditions=[Condition(_binary("INT_LESS", _const(3, 4), indexed_count, 1))],
                value=_const(1, 4),
            ),
            ReturnInfo(
                address="0x1904",
                conditions=[Condition(_binary("INT_SLESS", _const(3, 4), storage_count, 1))],
                value=_const(2, 4),
            ),
        ],
    )

    assert infer_parameter_semantics(analysis) == {}


def test_infer_parameter_semantics_by_identity_uses_storage_only_descriptor():
    storage = StorageInfo(
        is_register=True,
        space_name="register",
        register_name="a0",
        base_register_name="a0",
        size=4,
        size_bits=32,
    )
    count = _param("count", 8, storage_info=storage)
    analysis = FunctionReturnAnalysis(
        function_name="storage_only_identity_hint",
        entry_point="0x1a00",
        parameters=[
            {
                "name": "count",
                "data_type": "long",
                "size": 8,
                "is_signed": False,
                "storage": storage.to_dict(),
            },
        ],
        returns=[
            ReturnInfo(
                address="0x1a00",
                conditions=[],
                value=_binary("INT_AND", count, _const(0xFFFFFFFF, 8), 8),
            ),
        ],
    )

    by_index = infer_parameter_semantics(analysis)
    by_identity = infer_parameter_semantics_by_identity(analysis)

    assert by_index == {}
    hint = by_identity[("parameter_storage", storage.storage_identity_key())]
    assert hint.narrow_bits == 32
    assert hint.signedness == "unknown"
    assert hint.signedness_source == "width_only"


def test_hint_objects_by_name_refuses_duplicate_parameter_names():
    left = _param("dup", 8, index=0)
    right = _param("dup", 8, index=1)
    analysis = FunctionReturnAnalysis(
        function_name="duplicate_name_hints",
        entry_point="0x1b00",
        parameters=[
            {"name": "dup", "data_type": "long", "size": 8, "index": 0, "is_signed": False},
            {"name": "dup", "data_type": "long", "size": 8, "index": 1, "is_signed": False},
        ],
        returns=[
            ReturnInfo(
                address="0x1b00",
                conditions=[],
                value=_binary(
                    "INT_OR",
                    _binary("INT_AND", left, _const(0xFFFFFFFF, 8), 8),
                    _binary("INT_AND", right, _const(0xFFFFFFFF, 8), 8),
                    8,
                ),
            ),
        ],
    )

    assert hint_objects_by_name(analysis) == {}


def test_hint_objects_by_name_counts_duplicate_names_without_hint_evidence():
    hinted = _param("dup", 8, index=0)
    analysis = FunctionReturnAnalysis(
        function_name="duplicate_name_partial_hint",
        entry_point="0x1c00",
        parameters=[
            {"name": "dup", "data_type": "long", "size": 8, "index": 0, "is_signed": False},
            {"name": "dup", "data_type": "long", "size": 8, "index": 1, "is_signed": False},
        ],
        returns=[
            ReturnInfo(
                address="0x1c00",
                conditions=[],
                value=_binary("INT_AND", hinted, _const(0xFFFFFFFF, 8), 8),
            ),
        ],
    )

    assert hint_objects_by_name(analysis) == {}


def test_infer_parameter_semantics_does_not_resolve_weighted_direct_signedness_conflict():
    hints = infer_parameter_semantics(_analysis_with_same_width_signedness_conflict())

    assert hints == {}


def test_infer_parameter_semantics_uses_storage_backed_narrow_width():
    hints = infer_parameter_semantics(_analysis_with_storage_backed_narrowing())

    assert hints[0].narrow_bits == 32
    assert hints[0].signedness == "unknown"
    assert hints[0].signedness_source == "width_only"


def test_infer_parameter_semantics_prefers_direct_signedness_for_narrowed_params():
    hints = infer_parameter_semantics(_analysis_with_narrowed_direct_unsigned_and_composite_signed())

    assert hints[0].narrow_bits == 32
    assert hints[0].signedness == "unsigned"
    assert hints[0].signedness_source == "explicit"


def test_infer_parameter_semantics_does_not_promote_same_width_composite_signed_test():
    hints = infer_parameter_semantics(_analysis_with_same_width_composite_signed_test())

    assert hints == {}


def test_infer_parameter_semantics_does_not_treat_zext_wrapped_compare_as_direct_signedness():
    hints = infer_parameter_semantics(_analysis_with_zext_wrapped_signed_compare())

    assert hints == {}


def test_infer_parameter_semantics_keeps_zext_wrapped_narrowing_as_width_only():
    hints = infer_parameter_semantics(
        _analysis_with_storage_narrowing_and_zext_wrapped_signed_compare()
    )

    assert hints[0].narrow_bits == 32
    assert hints[0].signedness == "unknown"
    assert hints[0].signedness_source == "width_only"


def test_infer_parameter_semantics_keeps_pure_composite_narrowing_as_width_only():
    hints = infer_parameter_semantics(
        _analysis_with_storage_narrowing_and_pure_composite_signed_compare()
    )

    assert hints[0].narrow_bits == 32
    assert hints[0].signedness == "unknown"
    assert hints[0].signedness_source == "width_only"


def test_infer_parameter_semantics_requires_direct_evidence_for_winning_signedness():
    hints = infer_parameter_semantics(
        _analysis_with_mixed_direct_unsigned_and_composite_signed_test()
    )

    assert hints == {}


def test_infer_parameter_semantics_does_not_let_composite_break_direct_ties():
    hints = infer_parameter_semantics(
        _analysis_with_direct_tie_and_composite_signed_tiebreak()
    )

    assert hints == {}


def test_formula_builder_emits_signed_semantic_constraints_for_or_guard():
    builder = FormulaBuilder(debug=False)
    analysis = _analysis_with_guard(_or_guard_condition("param_1", "param_2"))

    formula = builder.build_equivalence_formula_extended(analysis, analysis).formula

    assert "; param_1_1: constrain to signed 32-bit semantic value" not in formula
    assert "; param_2_1: constrain to signed 32-bit semantic value" not in formula
    assert "; param_1_1: constrain to unsigned 32-bit semantic value" not in formula
    assert "; param_2_1: constrain to unsigned 32-bit semantic value" not in formula


def test_formula_builder_does_not_emit_signedness_constraints_for_width_only_hint():
    builder = FormulaBuilder(debug=False)
    analysis = _analysis_with_storage_backed_narrowing()

    formula = builder.build_equivalence_formula_extended(analysis, analysis).formula

    assert "; count_1: constrain to signed 32-bit semantic value" not in formula
    assert "; count_1: constrain to unsigned 32-bit semantic value" not in formula


def test_mips64_spurious_detection_uses_signed_or_guard_evidence():
    handler = MIPS64Handler(debug=True)

    analysis_wide = create_mock_analysis(
        function_name="branch_multi_guard_like",
        parameters=[
            {"name": "param_1", "data_type": "long", "size": 8, "index": 0},
            {"name": "param_2", "data_type": "long", "size": 8, "index": 1},
        ],
        returns=[
            ReturnInfo(
                address="0x1000",
                conditions=[_or_guard_condition("param_1", "param_2", index1=0, index2=1)],
                value=_binary(
                    "INT_OR",
                    _mask32("param_1", index=0),
                    _mask32("param_2", index=1),
                    8,
                ),
            )
        ],
    )
    analysis_narrow = create_mock_analysis(
        function_name="branch_multi_guard_like",
        parameters=[
            {"name": "param_1", "data_type": "uint", "size": 4, "index": 0},
            {"name": "param_2", "data_type": "uint", "size": 4, "index": 1},
        ],
    )

    counterexample = {
        "param_1_1": 0x0000000080000000,
        "param_1_2": 0x80000000,
        "param_2_1": 0x0,
        "param_2_2": 0x0,
    }

    constraints = handler.detect_spurious_counterexample(
        counterexample,
        analysis_wide,
        analysis_narrow,
        is_mips64_1=True,
        is_mips64_2=False,
    )

    assert constraints == {}


def test_mips64_type_mismatch_uses_counterpart_semantic_width_hint_even_when_both_types_are_long():
    handler = MIPS64Handler(debug=True)

    mips_analysis = create_mock_analysis(
        function_name="fc_widen_then_bias_like",
        parameters=[
            {"name": "param_2", "data_type": "long", "size": 8, "index": 0},
        ],
    )
    hinted_peer = create_mock_analysis(
        function_name="fc_widen_then_bias_like",
        parameters=[
            {"name": "param_2", "data_type": "long", "size": 8, "index": 0},
        ],
        returns=[
            ReturnInfo(
                address="0x1000",
                conditions=[
                    Condition(
                        _binary("INT_NOTEQUAL", _mask32("param_2", index=0), _const(0, 8), 1),
                        negated=False,
                    )
                ],
                value=_mask32("param_2", index=0),
            )
        ],
    )

    override_map = handler.detect_param_type_mismatch(mips_analysis, hinted_peer)

    assert 0 in override_map
    assert override_map[0].type_name == "unsigned int"


def test_readonly_sum_runtime_ref_provides_signed_count_hint():
    hints = infer_parameter_semantics(_analysis_with_readonly_sum_signed_counter())

    assert 1 in hints
    assert hints[1].signedness == "signed"
    assert hints[1].signedness_source == "explicit"
    assert hints[1].narrow_bits == 64


def test_readonly_sum_signed_count_hint_drives_param_signedness_override():
    fixer = ParamSignednessFixer(TypeFixerConfig(), debug=False)

    overrides = fixer.detect_param_signedness_mismatch(_analysis_with_readonly_sum_signed_counter())

    assert 1 in overrides
    assert overrides[1].is_signed is True
    assert overrides[1].size_bytes == 8

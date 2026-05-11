# -*- coding: utf-8 -*-

import re
from unittest.mock import Mock

import pytest

from scripts.function_tracer_pcode.analysis import ReturnAnalyzer
from scripts.function_tracer_pcode.analysis.condition.smt_oracle import ConditionSMTOracle
from scripts.function_tracer_pcode.analysis.effect_summary import EffectSummary, StoreEffect
from scripts.function_tracer_pcode.equivalence.formula import builder as formula_builder_module
from scripts.function_tracer_pcode.analysis.tracer import PcodeTracer
from scripts.function_tracer_pcode.equivalence.formula.builder import FormulaBuilder
from scripts.function_tracer_pcode.equivalence.formula.types import ExtraVariableInfo, ParameterInfo
from scripts.function_tracer_pcode.equivalence.semantic_width import RETURN_EXTENSION_SURFACE_SOURCE
from scripts.function_tracer_pcode.equivalence.strategies import monolithic as monolithic_module
from scripts.function_tracer_pcode.equivalence.strategies.monolithic import MonolithicStrategy
from scripts.function_tracer_pcode.equivalence.strategies.pairwise import PairwiseStrategy
from scripts.function_tracer_pcode.equivalence.strategies.pairwise_query_builder import (
    _ParameterMetadataRewriter,
    build_pair_query,
    extract_return_cases,
)
from scripts.function_tracer_pcode.model import (
    CanonicalLocation,
    CallTargetRef,
    Condition,
    ComparisonSurface,
    DeferredCallRef,
    Expression,
    LocationBaseRef,
    LoopSideEffectProfileRef,
    LoopSummaryRef,
    LoopTermDescriptorRef,
    READONLY_SUM_OPCODE,
    ReductionAccumulatorProof,
    ReadonlyReductionRef,
    ReadonlyReductionTermRef,
    ReadonlyReductionWitness,
    ReturnInfo,
    StorageInfo,
    UnknownValueRef,
)
from scripts.function_tracer_pcode.model.render_smt import (
    collect_intrinsic_smt_declarations,
    collect_unknown_smt_declarations,
)
from scripts.function_tracer_pcode.tests.conftest import create_mock_analysis


def test_expression_unknown_uses_object_centric_runtime_identity_for_smt():
    expr = Expression.unknown("call_out_of_scope:ptr_dispatch_callback")

    assert getattr(expr.runtime_ref, "kind", None) == "opaque_unknown"

    declarations = collect_unknown_smt_declarations(expr)
    assert declarations == [(expr.to_smt(), 32)]
    assert expr.to_smt().startswith("rtunk_")
    assert expr.to_smt() != "unknown"


def test_unresolved_parameter_runtime_unknowns_do_not_share_smt_identity():
    left = Expression.unknown(
        "unresolved_parameter_value",
        runtime_ref=LocationBaseRef.parameter("left", index=None),
    )
    right = Expression.unknown(
        "unresolved_parameter_value",
        runtime_ref=LocationBaseRef.parameter("right", index=None),
    )
    expr = Expression.binary_op("INT_XOR", left, right)

    declarations = collect_unknown_smt_declarations(expr)
    names = [name for name, _bits in declarations]

    assert len(names) == 2
    assert left.to_smt() in names
    assert right.to_smt() in names
    assert left.to_smt() != right.to_smt()


def test_pairwise_query_declares_runtime_unknown_symbols():
    unknown_expr = Expression.unknown("call_out_of_scope:ptr_call_chain")
    analysis1 = create_mock_analysis(
        "left",
        parameters=[{"name": "param_1", "size": 4, "data_type": "int"}],
        returns=[ReturnInfo(address="0x1000", value=unknown_expr, conditions=[], branch_index=0)],
    )
    analysis2 = create_mock_analysis(
        "right",
        parameters=[{"name": "param_1", "size": 4, "data_type": "int"}],
        returns=[ReturnInfo(address="0x1000", value=Expression.constant(0, 4), conditions=[], branch_index=0)],
    )

    builder = FormulaBuilder()
    base_ctx = builder.build_base_context(analysis1, analysis2)
    query = build_pair_query(
        base_ctx,
        extract_return_cases(analysis1)[0],
        extract_return_cases(analysis2)[0],
        lambda expr: expr.to_smt(),
        lambda expr: expr.to_smt(),
        "0,0",
    )

    declared_symbol, bit_width = base_ctx["runtime_unknown_declarations"][0]
    assert bit_width == 32
    assert declared_symbol == unknown_expr.to_smt()
    assert f"(declare-const {declared_symbol} (_ BitVec 32))" in "\n".join(base_ctx["header_lines"])
    assert f"(declare-const {declared_symbol} (_ BitVec 32))" in query
    assert " unknown" not in query


def test_formula_builder_declares_object_centric_readonly_reduction_functions():
    reduction_expr = Expression.intrinsic(
        "READONLY_SUM",
        [
            Expression.parameter("param_1", index=0, data_type="int *", size=8),
            Expression.parameter("param_2", index=1, data_type="int", size=4),
        ],
        size=4,
        runtime_ref=ReadonlyReductionRef(
            reduction_kind="readonly_sum",
            pointer_base_ref=LocationBaseRef.parameter("param_1", index=0),
            count_parameter_name="param_2",
            count_parameter_index=1,
            stride=4,
            element_size=4,
            result_size=4,
            signed_counter=True,
        ),
        opcode=READONLY_SUM_OPCODE,
    )
    analysis1 = create_mock_analysis(
        "left",
        parameters=[
            {"name": "param_1", "size": 8, "data_type": "int *"},
            {"name": "param_2", "size": 4, "data_type": "int"},
        ],
        returns=[ReturnInfo(address="0x1000", value=reduction_expr, conditions=[], branch_index=0)],
    )
    analysis2 = create_mock_analysis(
        "right",
        parameters=[
            {"name": "param_1", "size": 8, "data_type": "int *"},
            {"name": "param_2", "size": 4, "data_type": "int"},
        ],
        returns=[ReturnInfo(address="0x1000", value=Expression.constant(0, 4), conditions=[], branch_index=0)],
    )

    declarations = collect_intrinsic_smt_declarations(reduction_expr)
    declared_name = re.search(r"\(declare-fun ([^ ]+)", declarations[0]).group(1)
    assert declarations == [
        f"(declare-fun {declared_name} ((_ BitVec 64) (_ BitVec 32)) (_ BitVec 32))"
    ]

    builder = FormulaBuilder()
    base_ctx = builder.build_base_context(analysis1, analysis2)
    header_text = "\n".join(base_ctx["header_lines"])

    assert "Intrinsic function declarations" in header_text
    assert declared_name in header_text


def test_formula_builder_adds_readonly_reduction_finite_witness_axioms():
    base = Expression.parameter("param_1", index=0, data_type="int *", size=8)
    count = Expression.parameter("param_2", index=1, data_type="int", size=4)
    proof = ReductionAccumulatorProof(
        reduction_kind="memory_sum",
        pointer_base_ref=LocationBaseRef.parameter("param_1", index=0),
        count_parameter_name="param_2",
        count_parameter_index=1,
        limit_expr=count,
        result_size=4,
        stride=4,
        element_size=4,
        start_offset=0,
        start_index=0,
        index_step=1,
        index_scale=4,
        exact_return_witnesses=(
            ReadonlyReductionWitness(
                exact_count=1,
                terms=(ReadonlyReductionTermRef(byte_offset=0, access_size=4),),
            ),
        ),
        return_region_value_proven=True,
    )
    reduction_ref = proof.to_readonly_reduction_ref()
    assert reduction_ref is not None
    reduction_expr = Expression.intrinsic(
        "READONLY_SUM",
        [base, count],
        size=4,
        runtime_ref=reduction_ref,
        opcode=READONLY_SUM_OPCODE,
    )
    analysis1 = create_mock_analysis(
        "left",
        parameters=[
            {"name": "param_1", "size": 8, "data_type": "int *", "index": 0},
            {"name": "param_2", "size": 4, "data_type": "int", "index": 1},
        ],
        returns=[ReturnInfo(address="0x1000", value=reduction_expr, conditions=[], branch_index=0)],
    )
    analysis2 = create_mock_analysis(
        "right",
        parameters=[
            {"name": "param_1", "size": 8, "data_type": "int *", "index": 0},
            {"name": "param_2", "size": 4, "data_type": "int", "index": 1},
        ],
        returns=[ReturnInfo(address="0x1004", value=Expression.constant(0, 4), conditions=[], branch_index=0)],
    )

    base_ctx = FormulaBuilder().build_base_context(analysis1, analysis2)
    header_text = "\n".join(base_ctx["header_lines"])

    assert "(declare-const mem32 (Array (_ BitVec 64) (_ BitVec 32)))" in header_text
    assert "Readonly reduction finite witness axioms" in header_text
    assert "Readonly reduction contract equality axioms" not in header_text
    assert "(=> (= param_2_1 (_ bv1 32))" in header_text
    assert "(select mem32 param_1_1)" in header_text


def test_formula_builder_keeps_finite_witness_axioms_without_contract_key():
    base = Expression.parameter("param_1", index=0, data_type="int *", size=8)
    count = Expression.parameter("param_2", index=1, data_type="int", size=4)
    proof = ReductionAccumulatorProof(
        reduction_kind="memory_sum",
        pointer_base_ref=LocationBaseRef.parameter("param_1", index=0),
        count_parameter_name="param_2",
        count_parameter_index=1,
        limit_expr=Expression.variable("unresolved_limit_tmp", size=4),
        result_size=4,
        stride=4,
        element_size=4,
        start_offset=0,
        start_index=0,
        index_step=1,
        index_scale=4,
        exact_return_witnesses=(
            ReadonlyReductionWitness(
                exact_count=1,
                terms=(ReadonlyReductionTermRef(byte_offset=0, access_size=4),),
            ),
        ),
        return_region_value_proven=True,
    )
    reduction_ref = proof.to_readonly_reduction_ref()
    assert reduction_ref is not None
    assert reduction_ref.readonly_term_sequence_contract_key() is None
    reduction_expr = Expression.intrinsic(
        "READONLY_SUM",
        [base, count],
        size=4,
        runtime_ref=reduction_ref,
        opcode=READONLY_SUM_OPCODE,
    )
    analysis1 = create_mock_analysis(
        "left",
        parameters=[
            {"name": "param_1", "size": 8, "data_type": "int *", "index": 0},
            {"name": "param_2", "size": 4, "data_type": "int", "index": 1},
        ],
        returns=[ReturnInfo(address="0x1000", value=reduction_expr, conditions=[], branch_index=0)],
    )
    analysis2 = create_mock_analysis(
        "right",
        parameters=[
            {"name": "param_1", "size": 8, "data_type": "int *", "index": 0},
            {"name": "param_2", "size": 4, "data_type": "int", "index": 1},
        ],
        returns=[ReturnInfo(address="0x1004", value=Expression.constant(0, 4), conditions=[], branch_index=0)],
    )

    base_ctx = FormulaBuilder().build_base_context(analysis1, analysis2)
    header_text = "\n".join(base_ctx["header_lines"])

    assert "Readonly reduction finite witness axioms" in header_text
    assert "Readonly reduction contract equality axioms" not in header_text
    assert "(=> (= param_2_1 (_ bv1 32))" in header_text
    assert "(select mem32 param_1_1)" in header_text


def test_formula_builder_removes_readonly_global_contract_equality_even_when_contracts_match():
    base = Expression.parameter("param_1", index=0, data_type="int *", size=8)
    count = Expression.parameter("param_2", index=1, data_type="int", size=4)
    pointer_ref = LocationBaseRef.parameter("param_1", index=0)

    def _readonly_expr() -> Expression:
        proof = ReductionAccumulatorProof(
            reduction_kind="memory_sum",
            pointer_base_ref=pointer_ref,
            count_parameter_name="param_2",
            count_parameter_index=1,
            limit_expr=count,
            result_size=4,
            stride=4,
            element_size=4,
            start_offset=0,
            start_index=0,
            index_step=1,
            index_scale=4,
            loop_body_witnesses=(
                ReadonlyReductionWitness(
                    exact_count=1,
                    terms=(ReadonlyReductionTermRef(byte_offset=0, access_size=4),),
                ),
            ),
            return_region_value_proven=True,
        )
        reduction_ref = proof.to_readonly_reduction_ref()
        assert reduction_ref is not None
        assert reduction_ref.readonly_term_sequence_contract_key() is not None
        return Expression.intrinsic(
            "READONLY_SUM",
            [base, count],
            size=4,
            runtime_ref=reduction_ref,
            opcode=READONLY_SUM_OPCODE,
        )

    analysis1 = create_mock_analysis(
        "left",
        parameters=[
            {"name": "param_1", "size": 8, "data_type": "int *", "index": 0},
            {"name": "param_2", "size": 4, "data_type": "int", "index": 1},
        ],
        returns=[ReturnInfo(address="0x1000", value=_readonly_expr(), conditions=[], branch_index=0)],
    )
    analysis2 = create_mock_analysis(
        "right",
        parameters=[
            {"name": "param_1", "size": 8, "data_type": "int *", "index": 0},
            {"name": "param_2", "size": 4, "data_type": "int", "index": 1},
        ],
        returns=[ReturnInfo(address="0x1004", value=_readonly_expr(), conditions=[], branch_index=0)],
    )

    base_ctx = FormulaBuilder().build_base_context(analysis1, analysis2)
    header_lines = base_ctx["header_lines"]
    header_text = "\n".join(header_lines)

    assert "Readonly reduction finite witness axioms" in header_text
    assert "Readonly reduction contract equality axioms" not in header_text
    assert not any(line.startswith("(assert (= (") for line in header_lines)


def test_formula_builder_guards_readonly_finite_witness_axioms_with_case_and_proof_conditions():
    base = Expression.parameter("param_1", index=0, data_type="int *", size=8)
    count = Expression.parameter("param_2", index=1, data_type="int", size=4)
    case_guard = Condition(
        Expression.binary_op("INT_SLESS", Expression.constant(0, size=4), count)
    )
    proof_guard = Condition(
        Expression.binary_op("INT_SLESS", Expression.constant(3, size=4), count)
    )
    proof = ReductionAccumulatorProof(
        reduction_kind="memory_sum",
        pointer_base_ref=LocationBaseRef.parameter("param_1", index=0),
        count_parameter_name="param_2",
        count_parameter_index=1,
        limit_expr=count,
        result_size=4,
        stride=4,
        element_size=4,
        start_offset=0,
        start_index=0,
        index_step=1,
        index_scale=4,
        exact_return_witnesses=(
            ReadonlyReductionWitness(
                exact_count=1,
                terms=(ReadonlyReductionTermRef(byte_offset=0, access_size=4),),
            ),
        ),
        guard_constraints=(proof_guard,),
        return_region_value_proven=True,
    )
    reduction_ref = proof.to_readonly_reduction_ref()
    assert reduction_ref is not None
    reduction_expr = Expression.intrinsic(
        "READONLY_SUM",
        [base, count],
        size=4,
        runtime_ref=reduction_ref,
        opcode=READONLY_SUM_OPCODE,
    )
    analysis1 = create_mock_analysis(
        "left",
        parameters=[
            {"name": "param_1", "size": 8, "data_type": "int *", "index": 0},
            {"name": "param_2", "size": 4, "data_type": "int", "index": 1},
        ],
        returns=[
            ReturnInfo(
                address="0x1000",
                value=reduction_expr,
                conditions=[case_guard],
                branch_index=0,
            )
        ],
    )
    analysis2 = create_mock_analysis(
        "right",
        parameters=[
            {"name": "param_1", "size": 8, "data_type": "int *", "index": 0},
            {"name": "param_2", "size": 4, "data_type": "int", "index": 1},
        ],
        returns=[ReturnInfo(address="0x1004", value=Expression.constant(0, 4), conditions=[], branch_index=0)],
    )

    base_ctx = FormulaBuilder().build_base_context(analysis1, analysis2)
    header_text = "\n".join(base_ctx["header_lines"])

    assert "Readonly reduction finite witness axioms" in header_text
    assert "(assert (=> (and (= param_2_1 (_ bv1 32))" in header_text
    assert "(bvslt (_ bv0 32) param_2_1)" in header_text
    assert "(bvslt (_ bv3 32) param_2_1)" in header_text
    assert "(assert (=> (= param_2_1 (_ bv1 32))" not in header_text


def test_formula_builder_skips_readonly_finite_witness_axioms_for_unlowerable_proof_guard():
    base = Expression.parameter("param_1", index=0, data_type="int *", size=8)
    count = Expression.parameter("param_2", index=1, data_type="int", size=4)
    proof = ReductionAccumulatorProof(
        reduction_kind="memory_sum",
        pointer_base_ref=LocationBaseRef.parameter("param_1", index=0),
        count_parameter_name="param_2",
        count_parameter_index=1,
        limit_expr=count,
        result_size=4,
        stride=4,
        element_size=4,
        start_offset=0,
        start_index=0,
        index_step=1,
        index_scale=4,
        exact_return_witnesses=(
            ReadonlyReductionWitness(
                exact_count=1,
                terms=(ReadonlyReductionTermRef(byte_offset=0, access_size=4),),
            ),
        ),
        guard_constraints=("count > 3",),
        return_region_value_proven=True,
    )
    reduction_ref = proof.to_readonly_reduction_ref()
    assert reduction_ref is not None
    reduction_expr = Expression.intrinsic(
        "READONLY_SUM",
        [base, count],
        size=4,
        runtime_ref=reduction_ref,
        opcode=READONLY_SUM_OPCODE,
    )
    analysis1 = create_mock_analysis(
        "left",
        parameters=[
            {"name": "param_1", "size": 8, "data_type": "int *", "index": 0},
            {"name": "param_2", "size": 4, "data_type": "int", "index": 1},
        ],
        returns=[ReturnInfo(address="0x1000", value=reduction_expr, conditions=[], branch_index=0)],
    )
    analysis2 = create_mock_analysis(
        "right",
        parameters=[
            {"name": "param_1", "size": 8, "data_type": "int *", "index": 0},
            {"name": "param_2", "size": 4, "data_type": "int", "index": 1},
        ],
        returns=[ReturnInfo(address="0x1004", value=Expression.constant(0, 4), conditions=[], branch_index=0)],
    )

    base_ctx = FormulaBuilder().build_base_context(analysis1, analysis2)
    header_text = "\n".join(base_ctx["header_lines"])

    assert "Readonly reduction finite witness axioms" not in header_text
    assert "(assert (=> (= param_2_1 (_ bv1 32))" not in header_text


def test_formula_builder_readonly_witness_axioms_accept_storage_backed_operands():
    base_storage = StorageInfo(
        is_register=True,
        space_name="register",
        register_name="a0",
        base_register_name="a0",
        size=8,
        size_bits=64,
    )
    count_storage = StorageInfo(
        is_register=True,
        space_name="register",
        register_name="a1",
        base_register_name="a1",
        size=4,
        size_bits=32,
    )
    base = Expression.parameter("renamed_base", data_type="int *", size=8, storage_info=base_storage)
    count = Expression.parameter("renamed_count", data_type="int", size=4, storage_info=count_storage)
    proof = ReductionAccumulatorProof(
        reduction_kind="memory_sum",
        pointer_base_ref=LocationBaseRef.storage(
            space_id=0,
            space_name="register",
            offset=base_storage.base_register_offset,
            size=8,
            storage_identity_key=base_storage.storage_identity_key(),
            display_hint="a0",
        ),
        count_parameter_name="renamed_count",
        count_parameter_index=None,
        count_parameter_storage_identity_key=count_storage.storage_identity_key(),
        limit_expr=count,
        result_size=4,
        stride=4,
        element_size=4,
        start_offset=0,
        start_index=0,
        index_step=1,
        index_scale=4,
        exact_return_witnesses=(
            ReadonlyReductionWitness(
                exact_count=1,
                terms=(ReadonlyReductionTermRef(byte_offset=0, access_size=4),),
            ),
        ),
        return_region_value_proven=True,
    )
    reduction_ref = proof.to_readonly_reduction_ref()
    assert reduction_ref is not None
    reduction_expr = Expression.intrinsic(
        "READONLY_SUM",
        [base, count],
        size=4,
        runtime_ref=reduction_ref,
        opcode=READONLY_SUM_OPCODE,
    )
    analysis1 = create_mock_analysis(
        "left",
        parameters=[
            {"name": "renamed_base", "size": 8, "data_type": "int *", "storage": base_storage},
            {"name": "renamed_count", "size": 4, "data_type": "int", "storage": count_storage},
        ],
        returns=[ReturnInfo(address="0x1000", value=reduction_expr, conditions=[], branch_index=0)],
    )
    analysis2 = create_mock_analysis(
        "right",
        parameters=[
            {"name": "renamed_base", "size": 8, "data_type": "int *", "storage": base_storage},
            {"name": "renamed_count", "size": 4, "data_type": "int", "storage": count_storage},
        ],
        returns=[ReturnInfo(address="0x1004", value=Expression.constant(0, 4), conditions=[], branch_index=0)],
    )

    base_ctx = FormulaBuilder().build_base_context(analysis1, analysis2)
    header_text = "\n".join(base_ctx["header_lines"])

    assert "Readonly reduction finite witness axioms" in header_text
    assert "(=> (= renamed_count_1 (_ bv1 32))" in header_text
    assert "(select mem32 renamed_base_1)" in header_text


def test_formula_builder_refuses_readonly_witness_axioms_when_operands_do_not_match_ref():
    wrong_base = Expression.parameter("other_base", index=2, data_type="int *", size=8)
    count = Expression.parameter("param_2", index=1, data_type="int", size=4)
    proof = ReductionAccumulatorProof(
        reduction_kind="memory_sum",
        pointer_base_ref=LocationBaseRef.parameter("param_1", index=0),
        count_parameter_name="param_2",
        count_parameter_index=1,
        limit_expr=count,
        result_size=4,
        stride=4,
        element_size=4,
        start_offset=0,
        start_index=0,
        index_step=1,
        index_scale=4,
        exact_return_witnesses=(
            ReadonlyReductionWitness(
                exact_count=1,
                terms=(ReadonlyReductionTermRef(byte_offset=0, access_size=4),),
            ),
        ),
        return_region_value_proven=True,
    )
    reduction_ref = proof.to_readonly_reduction_ref()
    assert reduction_ref is not None
    malformed_expr = Expression.intrinsic(
        "READONLY_SUM",
        [wrong_base, count],
        size=4,
        runtime_ref=reduction_ref,
        opcode=READONLY_SUM_OPCODE,
    )
    analysis1 = create_mock_analysis(
        "left",
        parameters=[
            {"name": "param_1", "size": 8, "data_type": "int *", "index": 0},
            {"name": "param_2", "size": 4, "data_type": "int", "index": 1},
            {"name": "other_base", "size": 8, "data_type": "int *", "index": 2},
        ],
        returns=[ReturnInfo(address="0x1000", value=malformed_expr, conditions=[], branch_index=0)],
    )
    analysis2 = create_mock_analysis(
        "right",
        parameters=[],
        returns=[ReturnInfo(address="0x1004", value=Expression.constant(0, 4), conditions=[], branch_index=0)],
    )

    base_ctx = FormulaBuilder().build_base_context(analysis1, analysis2)
    header_text = "\n".join(base_ctx["header_lines"])

    assert "Readonly reduction finite witness axioms" not in header_text
    assert "(=> (= param_2_1 (_ bv1 32))" not in header_text


def test_formula_builder_rejects_monolithic_return_width_overlap_assertion():
    analysis1 = create_mock_analysis(
        "wide_return",
        return_type="ulong",
        returns=[
            ReturnInfo(address="0x1000", value=Expression.constant(0x1_0000_0001, 8), conditions=[]),
        ],
    )
    analysis2 = create_mock_analysis(
        "narrow_return",
        return_type="uint",
        returns=[
            ReturnInfo(address="0x2000", value=Expression.constant(1, 4), conditions=[]),
        ],
    )

    with pytest.raises(ValueError, match="return width mismatch"):
        FormulaBuilder().build_equivalence_formula(analysis1, analysis2)


def test_monolithic_strategy_returns_unknown_for_unbridged_return_width_mismatch():
    analysis1 = create_mock_analysis(
        "wide_return",
        return_type="ulong",
        returns=[
            ReturnInfo(address="0x1000", value=Expression.constant(0x1_0000_0001, 8), conditions=[]),
        ],
    )
    analysis2 = create_mock_analysis(
        "narrow_return",
        return_type="uint",
        returns=[
            ReturnInfo(address="0x2000", value=Expression.constant(1, 4), conditions=[]),
        ],
    )

    class _NoSolver:
        def run_parallel(self, _formula):
            raise AssertionError("solver must not run for unbridged return width mismatch")

        def run_sequential(self, _formula):
            raise AssertionError("solver must not run for unbridged return width mismatch")

    result = MonolithicStrategy(
        FormulaBuilder(),
        _NoSolver(),
        debug=False,
    ).check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.smt_formula is None
    assert result.pairwise_debug_stats == {"return_width_bridge_missing": 1}


def test_formula_builder_rejects_width_mismatch_overlap_readonly_contract_axioms():
    base = Expression.parameter("param_1", index=0, data_type="int *", size=8)
    count = Expression.parameter("param_2", index=1, data_type="int", size=4)
    pointer_ref = LocationBaseRef.parameter("param_1", index=0)

    narrow_summary = LoopSummaryRef(
        start_expr=Expression.constant(0, size=4),
        limit_expr=count,
        step_expr=Expression.constant(1, size=4),
        term_descriptor=LoopTermDescriptorRef(
            kind="memory_load",
            reduction_kind="sum",
            location_base_ref=pointer_ref,
            start_offset=0,
            stride=4,
            element_size=4,
            result_size=4,
        ),
        side_effect_profile=LoopSideEffectProfileRef(profile="pure_memory_read", memory_reads=True),
    )
    wide_summary = LoopSummaryRef(
        start_expr=Expression.constant(0, size=4),
        limit_expr=count,
        step_expr=Expression.constant(1, size=4),
        term_descriptor=LoopTermDescriptorRef(
            kind="memory_load",
            reduction_kind="sum",
            location_base_ref=pointer_ref,
            start_offset=0,
            stride=4,
            element_size=4,
            result_size=8,
        ),
        side_effect_profile=LoopSideEffectProfileRef(profile="pure_memory_read", memory_reads=True),
    )
    narrow_expr = Expression.intrinsic(
        "READONLY_SUM",
        [base, count],
        size=4,
        runtime_ref=ReadonlyReductionRef(
            reduction_kind="memory_sum",
            pointer_base_ref=pointer_ref,
            count_parameter_name="param_2",
            count_parameter_index=1,
            stride=4,
            element_size=4,
            result_size=4,
            signed_counter=True,
            loop_summary=narrow_summary,
        ),
        opcode=READONLY_SUM_OPCODE,
    )
    wide_expr = Expression.intrinsic(
        "READONLY_SUM",
        [base, count],
        size=8,
        runtime_ref=ReadonlyReductionRef(
            reduction_kind="memory_sum",
            pointer_base_ref=pointer_ref,
            count_parameter_name="param_2",
            count_parameter_index=1,
            stride=4,
            element_size=4,
            result_size=8,
            signed_counter=True,
            loop_summary=wide_summary,
        ),
        opcode=READONLY_SUM_OPCODE,
    )
    analysis1 = create_mock_analysis(
        "left",
        parameters=[
            {"name": "param_1", "size": 8, "data_type": "int *", "index": 0},
            {"name": "param_2", "size": 4, "data_type": "int", "index": 1},
        ],
        returns=[ReturnInfo(address="0x1000", value=narrow_expr, conditions=[], branch_index=0)],
    )
    analysis2 = create_mock_analysis(
        "right",
        parameters=[
            {"name": "param_1", "size": 8, "data_type": "int *", "index": 0},
            {"name": "param_2", "size": 4, "data_type": "int", "index": 1},
        ],
        returns=[ReturnInfo(address="0x1004", value=wide_expr, conditions=[], branch_index=0)],
    )

    base_ctx = FormulaBuilder().build_base_context(analysis1, analysis2)
    header_text = "\n".join(base_ctx["header_lines"])

    assert "Readonly reduction contract equality axioms" not in header_text
    assert not re.search(r"\(assert \(= .*extract 31 0.*rt_memory_sum_", header_text)


def test_formula_builder_does_not_globalize_readonly_low_bit_equality_from_aligned_return_surface():
    base = Expression.parameter("param_1", index=0, data_type="int *", size=8)
    count = Expression.parameter("param_2", index=1, data_type="int", size=4)
    pointer_ref = LocationBaseRef.parameter("param_1", index=0)

    def _proof(constant_bias: int) -> ReductionAccumulatorProof:
        return ReductionAccumulatorProof(
            reduction_kind="memory_sum",
            pointer_base_ref=pointer_ref,
            count_parameter_name="param_2",
            count_parameter_index=1,
            limit_expr=count,
            result_size=8,
            stride=4,
            element_size=4,
            start_offset=0,
            start_index=0,
            index_step=1,
            index_scale=4,
            seed_terms=(),
            loop_body_witnesses=(
                ReadonlyReductionWitness(
                    exact_count=1,
                    terms=(ReadonlyReductionTermRef(byte_offset=0, access_size=4),),
                ),
            ),
            side_effect_profile=LoopSideEffectProfileRef(profile="pure_memory_read", memory_reads=True),
            constant_bias=constant_bias,
            return_region_value_proven=True,
        )

    def _readonly_expr(constant_bias: int) -> Expression:
        proof = _proof(constant_bias)
        return Expression.intrinsic(
            "READONLY_SUM",
            [base, count],
            size=8,
            runtime_ref=ReadonlyReductionRef(
                reduction_kind="memory_sum",
                pointer_base_ref=pointer_ref,
                count_parameter_name="param_2",
                count_parameter_index=1,
                stride=4,
                element_size=4,
                result_size=8,
                signed_counter=True,
                accumulator_proof=proof,
                constant_bias=constant_bias,
            ),
            opcode=READONLY_SUM_OPCODE,
        )

    surface = ComparisonSurface(
        kind="return_value",
        explicit_bit_width=32,
        use_sign_extension=False,
        evidence={
            "source": RETURN_EXTENSION_SURFACE_SOURCE,
            "extension_surface_bit_width": 32,
            "return_width_sign_artifact": True,
            "extension_surface_coercion": "equal_width_or_object_proven_extract",
            "extension_surface_extension_kind": "INT_ZEXT",
            "extension_surface_source_bit_widths": (32,),
        },
    )
    analysis1 = create_mock_analysis(
        "left",
        parameters=[
            {"name": "param_1", "size": 8, "data_type": "int *", "index": 0},
            {"name": "param_2", "size": 4, "data_type": "int", "index": 1},
        ],
        returns=[ReturnInfo(address="0x1000", value=_readonly_expr(0), conditions=[], branch_index=0)],
    )
    analysis2 = create_mock_analysis(
        "right",
        parameters=[
            {"name": "param_1", "size": 8, "data_type": "int *", "index": 0},
            {"name": "param_2", "size": 4, "data_type": "int", "index": 1},
        ],
        returns=[ReturnInfo(address="0x1004", value=_readonly_expr(0x100000000), conditions=[], branch_index=0)],
    )
    analysis1.comparison_surface = surface
    analysis2.comparison_surface = surface

    base_ctx = FormulaBuilder().build_base_context(analysis1, analysis2)
    header_text = "\n".join(base_ctx["header_lines"])

    assert "Readonly reduction contract equality axioms" not in header_text
    assert not re.search(r"\(assert \(= .*extract 31 0.*rt_memory_sum_", header_text)


def test_formula_builder_does_not_globalize_readonly_low_bit_equality_from_active_overlap():
    base = Expression.parameter("param_1", index=0, data_type="int *", size=8)
    count = Expression.parameter("param_2", index=1, data_type="int", size=4)
    pointer_ref = LocationBaseRef.parameter("param_1", index=0)

    def _proof(constant_bias: int) -> ReductionAccumulatorProof:
        return ReductionAccumulatorProof(
            reduction_kind="memory_sum",
            pointer_base_ref=pointer_ref,
            count_parameter_name="param_2",
            count_parameter_index=1,
            limit_expr=count,
            result_size=8,
            stride=4,
            element_size=4,
            start_offset=0,
            start_index=0,
            index_step=1,
            index_scale=4,
            loop_body_witnesses=(
                ReadonlyReductionWitness(
                    exact_count=1,
                    terms=(ReadonlyReductionTermRef(byte_offset=0, access_size=4),),
                ),
            ),
            side_effect_profile=LoopSideEffectProfileRef(profile="pure_memory_read", memory_reads=True),
            constant_bias=constant_bias,
            return_region_value_proven=True,
        )

    def _readonly_expr(constant_bias: int) -> Expression:
        proof = _proof(constant_bias)
        return Expression.intrinsic(
            "READONLY_SUM",
            [base, count],
            size=8,
            runtime_ref=ReadonlyReductionRef(
                reduction_kind="memory_sum",
                pointer_base_ref=pointer_ref,
                count_parameter_name="param_2",
                count_parameter_index=1,
                stride=4,
                element_size=4,
                result_size=8,
                signed_counter=True,
                accumulator_proof=proof,
                constant_bias=constant_bias,
            ),
            opcode=READONLY_SUM_OPCODE,
        )

    analysis1 = create_mock_analysis(
        "left",
        parameters=[
            {"name": "param_1", "size": 8, "data_type": "int *", "index": 0},
            {"name": "param_2", "size": 4, "data_type": "int", "index": 1},
        ],
        returns=[ReturnInfo(address="0x1000", value=_readonly_expr(0), conditions=[], branch_index=0)],
    )
    analysis2 = create_mock_analysis(
        "right",
        parameters=[
            {"name": "param_1", "size": 8, "data_type": "int *", "index": 0},
            {"name": "param_2", "size": 4, "data_type": "int", "index": 1},
        ],
        returns=[ReturnInfo(address="0x1004", value=_readonly_expr(0x100000000), conditions=[], branch_index=0)],
    )
    analysis1.comparison_surface = ComparisonSurface(
        kind="return_value",
        explicit_bit_width=64,
        use_sign_extension=False,
    )
    analysis2.comparison_surface = ComparisonSurface(
        kind="return_value",
        explicit_bit_width=32,
        use_sign_extension=False,
    )

    base_ctx = FormulaBuilder().build_base_context(analysis1, analysis2)
    header_text = "\n".join(base_ctx["header_lines"])

    assert base_ctx["return_size1"] == 64
    assert base_ctx["return_size2"] == 32
    assert "Readonly reduction contract equality axioms" not in header_text
    assert not re.search(r"\(assert \(= .*extract 31 0.*rt_memory_sum_", header_text)


def test_formula_builder_refuses_width_projected_readonly_axiom_when_operands_do_not_match_ref():
    base = Expression.parameter("param_1", index=0, data_type="int *", size=8)
    wrong_base = Expression.parameter("other_base", index=2, data_type="int *", size=8)
    count = Expression.parameter("param_2", index=1, data_type="int", size=4)
    pointer_ref = LocationBaseRef.parameter("param_1", index=0)

    def _summary(result_size: int) -> LoopSummaryRef:
        return LoopSummaryRef(
            start_expr=Expression.constant(0, size=4),
            limit_expr=count,
            step_expr=Expression.constant(1, size=4),
            term_descriptor=LoopTermDescriptorRef(
                kind="memory_load",
                reduction_kind="sum",
                location_base_ref=pointer_ref,
                start_offset=0,
                stride=4,
                element_size=4,
                result_size=result_size,
            ),
            side_effect_profile=LoopSideEffectProfileRef(profile="pure_memory_read", memory_reads=True),
        )

    narrow_expr = Expression.intrinsic(
        "READONLY_SUM",
        [base, count],
        size=4,
        runtime_ref=ReadonlyReductionRef(
            reduction_kind="memory_sum",
            pointer_base_ref=pointer_ref,
            count_parameter_name="param_2",
            count_parameter_index=1,
            stride=4,
            element_size=4,
            result_size=4,
            signed_counter=True,
            loop_summary=_summary(4),
        ),
        opcode=READONLY_SUM_OPCODE,
    )
    malformed_wide_expr = Expression.intrinsic(
        "READONLY_SUM",
        [wrong_base, count],
        size=8,
        runtime_ref=ReadonlyReductionRef(
            reduction_kind="memory_sum",
            pointer_base_ref=pointer_ref,
            count_parameter_name="param_2",
            count_parameter_index=1,
            stride=4,
            element_size=4,
            result_size=8,
            signed_counter=True,
            loop_summary=_summary(8),
        ),
        opcode=READONLY_SUM_OPCODE,
    )
    analysis1 = create_mock_analysis(
        "left",
        parameters=[
            {"name": "param_1", "size": 8, "data_type": "int *", "index": 0},
            {"name": "param_2", "size": 4, "data_type": "int", "index": 1},
        ],
        returns=[ReturnInfo(address="0x1000", value=narrow_expr, conditions=[], branch_index=0)],
    )
    analysis2 = create_mock_analysis(
        "right",
        parameters=[
            {"name": "param_1", "size": 8, "data_type": "int *", "index": 0},
            {"name": "param_2", "size": 4, "data_type": "int", "index": 1},
            {"name": "other_base", "size": 8, "data_type": "int *", "index": 2},
        ],
        returns=[ReturnInfo(address="0x1004", value=malformed_wide_expr, conditions=[], branch_index=0)],
    )

    base_ctx = FormulaBuilder().build_base_context(analysis1, analysis2)
    header_text = "\n".join(base_ctx["header_lines"])

    assert "Readonly reduction contract equality axioms" not in header_text


def test_extract_return_cases_rewrites_parameter_metadata_by_index_before_name():
    stale_name_param = Expression.parameter("count", index=1, data_type="long", size=8)
    analysis = create_mock_analysis(
        "index_wins",
        parameters=[
            {"name": "count", "index": 0, "size": 8, "data_type": "long"},
            {"name": "actual_count", "index": 1, "size": 4, "data_type": "int"},
        ],
        returns=[
            ReturnInfo(
                address="0x1000",
                value=Expression.constant(0, 4),
                conditions=[
                    Condition(
                        Expression.binary_op(
                            "INT_EQUAL",
                            stale_name_param,
                            Expression.constant(0, size=4),
                        )
                    )
                ],
                branch_index=0,
            )
        ],
    )

    case = extract_return_cases(analysis)[0]
    rewritten_param = case.conditions[0].expression.operands[0]

    assert rewritten_param.value == 1
    assert rewritten_param.size == 4
    assert rewritten_param.data_type == "int"


def test_pairwise_parameter_metadata_rewriter_does_not_infer_index_from_position():
    stale_index_param = Expression.parameter("stale_count", index=1, data_type="short", size=2)
    rewriter = _ParameterMetadataRewriter(
        [
            {"name": "base", "size": 8, "data_type": "int *"},
            {"name": "count", "size": 4, "data_type": "int"},
        ]
    )

    rewritten_param = rewriter.rewrite(stale_index_param)

    assert rewritten_param.value == 1
    assert rewritten_param.name == "stale_count"
    assert rewritten_param.size == 2
    assert rewritten_param.data_type == "short"


def test_pairwise_parameter_metadata_rewriter_does_not_rewrite_indexed_expr_by_name():
    stale_index_param = Expression.parameter("count", index=7, data_type="long", size=8)
    rewriter = _ParameterMetadataRewriter(
        [
            {"name": "count", "size": 4, "data_type": "int"},
        ]
    )

    rewritten_param = rewriter.rewrite(stale_index_param)

    assert rewritten_param.value == 7
    assert rewritten_param.name == "count"
    assert rewritten_param.size == 8
    assert rewritten_param.data_type == "long"


def test_pairwise_parameter_metadata_rewriter_does_not_rewrite_no_index_expr_by_name():
    name_only_param = Expression.parameter("count", data_type="long", size=8)
    rewriter = _ParameterMetadataRewriter(
        [
            {"name": "count", "index": 0, "size": 4, "data_type": "int"},
        ]
    )

    rewritten_param = rewriter.rewrite(name_only_param)

    assert rewritten_param.value == -1
    assert rewritten_param.name == "count"
    assert rewritten_param.size == 8
    assert rewritten_param.data_type == "long"


def test_pairwise_parameter_metadata_rewriter_rewrites_no_index_expr_by_storage_identity():
    storage = StorageInfo(
        is_register=True,
        space_name="register",
        register_name="a0",
        base_register_name="a0",
        size=8,
        size_bits=64,
    )
    storage_param = Expression.parameter("stale_count", data_type="long", size=8, storage_info=storage)
    rewriter = _ParameterMetadataRewriter(
        [
            {
                "name": "count",
                "index": 0,
                "size": 4,
                "data_type": "int",
                "storage": storage.to_dict(),
            },
        ]
    )

    rewritten_param = rewriter.rewrite(storage_param)

    assert rewritten_param.value == 0
    assert rewritten_param.name == "stale_count"
    assert rewritten_param.size == 4
    assert rewritten_param.data_type == "int"


def test_pairwise_auxiliary_loop_proof_refuses_name_only_parameter_symbols():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    case = Mock(
        parameters=[
            {"name": "count", "size": 4, "data_type": "int"},
        ]
    )
    name_only_param = Expression.parameter("count", data_type="int", size=4)

    specs = strategy._collect_intrinsic_parameter_specs(case, case, name_only_param)

    assert specs is None


def test_pairwise_auxiliary_loop_proof_renders_duplicate_names_by_object_identity():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    case = Mock(
        parameters=[
            {"name": "count", "index": 0, "size": 4, "data_type": "int"},
            {"name": "count", "index": 1, "size": 4, "data_type": "int"},
        ]
    )
    left = Expression.binary_op(
        "INT_ADD",
        Expression.parameter("count", index=0, data_type="int", size=4),
        Expression.parameter("count", index=1, data_type="int", size=4),
    )
    right = Expression.binary_op(
        "INT_ADD",
        Expression.parameter("count", index=1, data_type="int", size=4),
        Expression.parameter("count", index=0, data_type="int", size=4),
    )

    specs = strategy._collect_intrinsic_parameter_specs(case, case, left, right)
    query = strategy._build_intrinsic_equivalence_query(left, right, [], specs)

    assert specs is not None
    assert [spec["identity"] for spec in specs] == [
        ("parameter_index", 0),
        ("parameter_index", 1),
    ]
    assert "(declare-const aux_param_0 (_ BitVec 32))" in query
    assert "(declare-const aux_param_1 (_ BitVec 32))" in query
    assert "count_aux" not in query


def test_pairwise_auxiliary_loop_proof_extracts_narrow_occurrence_from_canonical_symbol():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    case = Mock(
        parameters=[
            {"name": "count", "index": 0, "size": 8, "data_type": "long"},
        ]
    )
    narrow_count = Expression.parameter("count", index=0, data_type="int", size=4)

    specs = strategy._collect_intrinsic_parameter_specs(case, case, narrow_count)
    query = strategy._build_intrinsic_equivalence_query(narrow_count, narrow_count, [], specs)

    assert specs is not None
    assert specs[0]["size"] == 8
    assert "(declare-const aux_param_0 (_ BitVec 64))" in query
    assert "((_ extract 31 0) aux_param_0)" in query


def test_reduction_count_bit_width_uses_index_before_name_collision():
    count_expr = Expression.parameter("actual_count", index=1, data_type="int", size=4)
    proof = ReductionAccumulatorProof(
        reduction_kind="memory_sum",
        pointer_base_ref=LocationBaseRef.parameter("base", index=0),
        count_parameter_name="count",
        count_parameter_index=1,
        limit_expr=count_expr,
        result_size=4,
        stride=4,
        element_size=4,
        start_offset=0,
        start_index=0,
        index_step=1,
        index_scale=4,
    )
    analysis = create_mock_analysis(
        "count_width_index_wins",
        parameters=[
            {"name": "base", "index": 0, "size": 8, "data_type": "int *"},
            {"name": "count", "index": 2, "size": 8, "data_type": "long"},
            {"name": "actual_count", "index": 1, "size": 4, "data_type": "int"},
        ],
        returns=[ReturnInfo(address="0x1000", value=Expression.constant(0, 4), conditions=[], branch_index=0)],
    )
    case = extract_return_cases(analysis)[0]

    assert PairwiseStrategy(None, None)._case_reduction_count_bit_width(case, proof) == 32


def test_return_definition_orders_guard_specific_readonly_summary_before_broad_overlap():
    base = Expression.parameter("param_1", index=0, data_type="int *", size=8)
    count = Expression.parameter("param_2", index=1, data_type="int", size=4)
    pointer_ref = LocationBaseRef.parameter("param_1", index=0)

    broad_proof = ReductionAccumulatorProof(
        reduction_kind="memory_sum",
        pointer_base_ref=pointer_ref,
        count_parameter_name="param_2",
        count_parameter_index=1,
        limit_expr=count,
        result_size=4,
        stride=4,
        element_size=4,
        start_index=0,
        index_scale=4,
        return_region_value_proven=True,
    )
    specific_proof = ReductionAccumulatorProof(
        reduction_kind="memory_sum",
        pointer_base_ref=pointer_ref,
        count_parameter_name="param_2",
        count_parameter_index=1,
        limit_expr=count,
        result_size=4,
        stride=4,
        element_size=4,
        start_index=2,
        index_scale=4,
        seed_terms=(ReadonlyReductionTermRef(byte_offset=0, access_size=4),),
        return_region_value_proven=True,
    )
    broad_ref = ReadonlyReductionRef(
        reduction_kind="memory_sum",
        pointer_base_ref=pointer_ref,
        count_parameter_name="param_2",
        count_parameter_index=1,
        stride=4,
        element_size=4,
        result_size=4,
        signed_counter=True,
        accumulator_proof=broad_proof,
    )
    specific_ref = ReadonlyReductionRef(
        reduction_kind="memory_sum",
        pointer_base_ref=pointer_ref,
        count_parameter_name="param_2",
        count_parameter_index=1,
        stride=4,
        element_size=4,
        result_size=4,
        signed_counter=True,
        accumulator_proof=specific_proof,
    )
    broad_expr = Expression.intrinsic(
        "READONLY_SUM",
        [base, count],
        size=4,
        runtime_ref=broad_ref,
        opcode=READONLY_SUM_OPCODE,
    )
    specific_expr = Expression.intrinsic(
        "READONLY_SUM",
        [base, count],
        size=4,
        runtime_ref=specific_ref,
        opcode=READONLY_SUM_OPCODE,
    )

    def _gt(value: int) -> Condition:
        return Condition(Expression.binary_op("INT_SLESS", Expression.constant(value, 4), count))

    def _ne(value: int) -> Condition:
        return Condition(Expression.binary_op("INT_EQUAL", count, Expression.constant(value, 4)), negated=True)

    analysis1 = create_mock_analysis(
        "left",
        parameters=[
            {"name": "param_1", "size": 8, "data_type": "int *", "index": 0},
            {"name": "param_2", "size": 4, "data_type": "int", "index": 1},
        ],
        returns=[
            ReturnInfo(
                address="0x1000",
                value=broad_expr,
                conditions=[_gt(0), _ne(1), _ne(2), _ne(3), _ne(4)],
                branch_index=0,
            ),
            ReturnInfo(
                address="0x1004",
                value=specific_expr,
                conditions=[_gt(3)],
                branch_index=1,
            ),
            ReturnInfo(
                address="0x1008",
                value=Expression.constant(0, 4),
                conditions=[],
                branch_index=2,
            ),
        ],
    )
    analysis2 = create_mock_analysis(
        "right",
        parameters=[
            {"name": "param_1", "size": 8, "data_type": "int *", "index": 0},
            {"name": "param_2", "size": 4, "data_type": "int", "index": 1},
        ],
        returns=[ReturnInfo(address="0x2000", value=Expression.constant(0, 4), conditions=[], branch_index=0)],
    )

    formula, _, _ = FormulaBuilder().build_equivalence_formula(analysis1, analysis2)
    return_block = formula.split("; Return value for left", 1)[1].split("; Return value for right", 1)[0]
    broad_symbol = re.match(r"\(([^ ]+)", broad_expr.to_smt()).group(1)
    specific_symbol = re.match(r"\(([^ ]+)", specific_expr.to_smt()).group(1)

    assert specific_symbol != broad_symbol
    assert return_block.index(broad_symbol) < return_block.index(specific_symbol)


def test_pairwise_return_cases_subtract_prior_guard_specific_readonly_summary_region():
    base = Expression.parameter("param_1", index=0, data_type="int *", size=8)
    count = Expression.parameter("param_2", index=1, data_type="int", size=4)
    pointer_ref = LocationBaseRef.parameter("param_1", index=0)
    broad_proof = ReductionAccumulatorProof(
        reduction_kind="memory_sum",
        pointer_base_ref=pointer_ref,
        count_parameter_name="param_2",
        count_parameter_index=1,
        limit_expr=count,
        result_size=4,
        stride=4,
        element_size=4,
        start_index=0,
        index_scale=4,
        return_region_value_proven=True,
    )
    specific_proof = ReductionAccumulatorProof(
        reduction_kind="memory_sum",
        pointer_base_ref=pointer_ref,
        count_parameter_name="param_2",
        count_parameter_index=1,
        limit_expr=count,
        result_size=4,
        stride=4,
        element_size=4,
        start_index=2,
        index_scale=4,
        seed_terms=(ReadonlyReductionTermRef(byte_offset=0, access_size=4),),
        return_region_value_proven=True,
    )
    broad_expr = Expression.intrinsic(
        "READONLY_SUM",
        [base, count],
        size=4,
        runtime_ref=ReadonlyReductionRef(
            reduction_kind="memory_sum",
            pointer_base_ref=pointer_ref,
            count_parameter_name="param_2",
            count_parameter_index=1,
            stride=4,
            element_size=4,
            result_size=4,
            signed_counter=True,
            accumulator_proof=broad_proof,
        ),
        opcode=READONLY_SUM_OPCODE,
    )
    specific_expr = Expression.intrinsic(
        "READONLY_SUM",
        [base, count],
        size=4,
        runtime_ref=ReadonlyReductionRef(
            reduction_kind="memory_sum",
            pointer_base_ref=pointer_ref,
            count_parameter_name="param_2",
            count_parameter_index=1,
            stride=4,
            element_size=4,
            result_size=4,
            signed_counter=True,
            accumulator_proof=specific_proof,
        ),
        opcode=READONLY_SUM_OPCODE,
    )
    gt0 = Condition(Expression.binary_op("INT_SLESS", Expression.constant(0, 4), count))
    gt3 = Condition(Expression.binary_op("INT_SLESS", Expression.constant(3, 4), count))
    broad_conditions = [
        gt0,
        Condition(Expression.binary_op("INT_EQUAL", count, Expression.constant(1, 4)), negated=True),
        Condition(Expression.binary_op("INT_EQUAL", count, Expression.constant(2, 4)), negated=True),
        Condition(Expression.binary_op("INT_EQUAL", count, Expression.constant(3, 4)), negated=True),
        Condition(Expression.binary_op("INT_EQUAL", count, Expression.constant(4, 4)), negated=True),
    ]
    analysis = create_mock_analysis(
        "left",
        parameters=[
            {"name": "param_1", "size": 8, "data_type": "int *", "index": 0},
            {"name": "param_2", "size": 4, "data_type": "int", "index": 1},
        ],
        returns=[
            ReturnInfo(address="0x1000", value=broad_expr, conditions=broad_conditions, branch_index=0),
            ReturnInfo(address="0x1004", value=specific_expr, conditions=[gt3], branch_index=1),
            ReturnInfo(address="0x1008", value=Expression.constant(0, 4), conditions=[], branch_index=2),
        ],
    )

    cases = extract_return_cases(analysis)
    specific_case = next(case for case in cases if case.value_expr is specific_expr)
    broad_case = next((case for case in cases if case.value_expr is broad_expr), None)

    if broad_case is not None:
        assert cases.index(broad_case) < cases.index(specific_case)
        assert ConditionSMTOracle.conjunction_is_unsat(
            list(specific_case.conditions) + list(broad_case.conditions)
        ) is True


def test_return_definition_keeps_unrelated_readonly_summaries_in_condition_order():
    base = Expression.parameter("param_1", index=0, data_type="int *", size=8)
    other_base = Expression.parameter("param_3", index=2, data_type="int *", size=8)
    count = Expression.parameter("param_2", index=1, data_type="int", size=4)
    broad_ref = ReadonlyReductionRef(
        reduction_kind="memory_sum",
        pointer_base_ref=LocationBaseRef.parameter("param_1", index=0),
        count_parameter_name="param_2",
        count_parameter_index=1,
        stride=4,
        element_size=4,
        result_size=4,
        signed_counter=True,
    )
    unrelated_ref = ReadonlyReductionRef(
        reduction_kind="memory_sum",
        pointer_base_ref=LocationBaseRef.parameter("param_3", index=2),
        count_parameter_name="param_2",
        count_parameter_index=1,
        stride=4,
        element_size=4,
        result_size=4,
        signed_counter=True,
    )
    broad_expr = Expression.intrinsic(
        "READONLY_SUM",
        [base, count],
        size=4,
        runtime_ref=broad_ref,
        opcode=READONLY_SUM_OPCODE,
    )
    unrelated_expr = Expression.intrinsic(
        "READONLY_SUM",
        [other_base, count],
        size=4,
        runtime_ref=unrelated_ref,
        opcode=READONLY_SUM_OPCODE,
    )
    broad_conditions = [
        Condition(Expression.binary_op("INT_SLESS", Expression.constant(0, 4), count)),
        Condition(Expression.binary_op("INT_EQUAL", count, Expression.constant(1, 4)), negated=True),
    ]
    unrelated_conditions = [
        Condition(Expression.binary_op("INT_SLESS", Expression.constant(0, 4), count)),
    ]
    analysis1 = create_mock_analysis(
        "left",
        parameters=[
            {"name": "param_1", "size": 8, "data_type": "int *", "index": 0},
            {"name": "param_2", "size": 4, "data_type": "int", "index": 1},
            {"name": "param_3", "size": 8, "data_type": "int *", "index": 2},
        ],
        returns=[
            ReturnInfo(address="0x1000", value=broad_expr, conditions=broad_conditions, branch_index=0),
            ReturnInfo(address="0x1004", value=unrelated_expr, conditions=unrelated_conditions, branch_index=1),
            ReturnInfo(address="0x1008", value=Expression.constant(0, 4), conditions=[], branch_index=2),
        ],
    )
    analysis2 = create_mock_analysis(
        "right",
        parameters=[
            {"name": "param_1", "size": 8, "data_type": "int *", "index": 0},
            {"name": "param_2", "size": 4, "data_type": "int", "index": 1},
            {"name": "param_3", "size": 8, "data_type": "int *", "index": 2},
        ],
        returns=[ReturnInfo(address="0x2000", value=Expression.constant(0, 4), conditions=[], branch_index=0)],
    )

    formula, _, _ = FormulaBuilder().build_equivalence_formula(analysis1, analysis2)
    return_block = formula.split("; Return value for left", 1)[1].split("; Return value for right", 1)[0]
    broad_symbol = re.match(r"\(([^ ]+)", broad_expr.to_smt()).group(1)
    unrelated_symbol = re.match(r"\(([^ ]+)", unrelated_expr.to_smt()).group(1)

    assert return_block.index(broad_symbol) < return_block.index(unrelated_symbol)


def test_formula_builder_declares_intrinsics_introduced_by_render_analysis(monkeypatch):
    reduction_expr = Expression.intrinsic(
        "READONLY_SUM",
        [
            Expression.parameter("param_1", index=0, data_type="int *", size=8),
            Expression.parameter("param_2", index=1, data_type="int", size=8),
        ],
        size=4,
        runtime_ref=ReadonlyReductionRef(
            reduction_kind="memory_sum",
            pointer_base_ref=LocationBaseRef.parameter("param_1", index=0),
            count_parameter_name="param_2",
            count_parameter_index=1,
            stride=4,
            element_size=4,
            result_size=4,
            signed_counter=True,
        ),
        opcode=READONLY_SUM_OPCODE,
    )
    raw_analysis1 = create_mock_analysis(
        "left",
        parameters=[
            {"name": "param_1", "size": 8, "data_type": "int *"},
            {"name": "param_2", "size": 4, "data_type": "int"},
        ],
        returns=[ReturnInfo(address="0x1000", value=Expression.constant(0, 4), conditions=[], branch_index=0)],
    )
    render_analysis1 = create_mock_analysis(
        "left",
        parameters=[
            {"name": "param_1", "size": 8, "data_type": "int *"},
            {"name": "param_2", "size": 8, "data_type": "long"},
        ],
        returns=[ReturnInfo(address="0x1000", value=reduction_expr, conditions=[], branch_index=0)],
    )
    analysis2 = create_mock_analysis(
        "right",
        parameters=[
            {"name": "param_1", "size": 8, "data_type": "int *"},
            {"name": "param_2", "size": 4, "data_type": "int"},
        ],
        returns=[ReturnInfo(address="0x1000", value=Expression.constant(0, 4), conditions=[], branch_index=0)],
    )
    original_normalize = formula_builder_module.normalize_analysis_semantic_width

    def _fake_normalize_analysis(analysis, semantic_hints, extra_vars=None):
        if extra_vars is not None and analysis.function_name == "left":
            return render_analysis1
        return original_normalize(analysis, semantic_hints, extra_vars)

    monkeypatch.setattr(
        formula_builder_module,
        "normalize_analysis_semantic_width",
        _fake_normalize_analysis,
    )

    declared_name = re.search(
        r"\(declare-fun ([^ ]+)",
        collect_intrinsic_smt_declarations(reduction_expr)[0],
    ).group(1)
    base_ctx = FormulaBuilder().build_base_context(raw_analysis1, analysis2)
    header_text = "\n".join(base_ctx["header_lines"])

    assert f"(declare-fun {declared_name} ((_ BitVec 64) (_ BitVec 64)) (_ BitVec 32))" in header_text


def test_monolithic_counterexample_validation_uses_render_analysis_cases(monkeypatch):
    old_reduction = Expression.intrinsic(
        "READONLY_SUM",
        [
            Expression.parameter("param_1", index=0, data_type="int *", size=8),
            Expression.parameter("param_2", index=1, data_type="long", size=8),
        ],
        size=4,
        runtime_ref=ReadonlyReductionRef(
            reduction_kind="memory_sum",
            pointer_base_ref=LocationBaseRef.parameter("param_1", index=0),
            count_parameter_name="param_2",
            count_parameter_index=1,
            stride=4,
            element_size=4,
            result_size=4,
            signed_counter=True,
        ),
        opcode=READONLY_SUM_OPCODE,
    )
    new_reduction = Expression.intrinsic(
        "READONLY_SUM",
        [
            Expression.parameter("param_1", index=0, data_type="int *", size=8),
            Expression.parameter("param_2", index=1, data_type="int", size=4),
        ],
        size=4,
        runtime_ref=old_reduction.runtime_ref,
        opcode=READONLY_SUM_OPCODE,
    )
    raw_analysis = create_mock_analysis(
        "left",
        parameters=[
            {"name": "param_1", "size": 8, "data_type": "int *"},
            {"name": "param_2", "size": 8, "data_type": "long"},
        ],
        returns=[ReturnInfo(address="0x1000", value=old_reduction, conditions=[], branch_index=0)],
    )
    render_analysis = create_mock_analysis(
        "left",
        parameters=[
            {"name": "param_1", "size": 8, "data_type": "int *"},
            {"name": "param_2", "size": 4, "data_type": "int"},
        ],
        returns=[ReturnInfo(address="0x1000", value=new_reduction, conditions=[], branch_index=0)],
    )
    right_analysis = create_mock_analysis(
        "right",
        parameters=[
            {"name": "param_1", "size": 8, "data_type": "int *"},
            {"name": "param_2", "size": 4, "data_type": "int"},
        ],
        returns=[ReturnInfo(address="0x1000", value=Expression.constant(0, 4), conditions=[], branch_index=0)],
    )
    captured = {}

    class _FormulaBuilder:
        def build_base_context(self, _analysis1, _analysis2):
            return {
                "header_lines": [],
                "params1": [
                    ParameterInfo("param_1", "param_1_1", 64, 0),
                    ParameterInfo("param_2", "param_2_1", 32, 1),
                ],
                "params2": [
                    ParameterInfo("param_1", "param_1_2", 64, 0),
                    ParameterInfo("param_2", "param_2_2", 32, 1),
                ],
                "extra_vars1": [ExtraVariableInfo("fragment", "fragment_1", 32)],
                "extra_vars2": [],
                "runtime_unknown_declarations": [],
                "return_size1": 32,
                "return_size2": 32,
            }

    def _fake_normalize(analysis, _hints, extra_vars=None):
        if analysis is raw_analysis and extra_vars:
            return render_analysis
        return analysis

    def _capture_validate(_strategy, _base_ctx, cases1, _cases2, *_args):
        captured["value_smt"] = cases1[0].get_value_smt(lambda expr: expr.to_smt())
        return True

    monkeypatch.setattr(monolithic_module, "normalize_analysis_semantic_width", _fake_normalize)
    monkeypatch.setattr(monolithic_module, "validate_counterexample_globally", _capture_validate)

    strategy = MonolithicStrategy(_FormulaBuilder(), solver_runner=Mock(), debug=False)

    assert strategy._counterexample_is_decisive_across_case_split(
        raw_analysis,
        right_analysis,
        {"param_1_1": 1},
    )
    assert "_64_32_32" in captured["value_smt"]
    assert "_64_64_32" not in captured["value_smt"]


def test_tracer_promotes_unresolved_direct_call_to_deferred_call_runtime_object():
    class _FakeVarnode:
        def __init__(self, name):
            self.name = name

    class _FakeCallOp:
        def __init__(self, inputs):
            self._inputs = inputs

        def getMnemonic(self):
            return "CALL"

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

        def getOutput(self):
            return None

    tracer = PcodeTracer(program=Mock(), high_function=Mock(), debug=False)
    target = _FakeVarnode("target")
    arg0 = _FakeVarnode("arg0")
    arg1 = _FakeVarnode("arg1")
    call_op = _FakeCallOp([target, arg0, arg1])
    recorded = {}

    tracer.resolve_call_target_ref = lambda *_args, **_kwargs: CallTargetRef.from_name("callee")
    tracer.trace_varnode = lambda varnode, depth=0, use_cache=True: {
        target: Expression.constant(0x401000, 8),
        arg0: Expression.parameter("param_1", index=0, size=8),
        arg1: Expression.parameter("param_2", index=1, size=4),
    }[varnode]

    def _record_deferred_call(target_ref, args, call_target_expr=None):
        recorded["target_ref"] = target_ref
        recorded["args"] = [arg.to_string() for arg in args]
        recorded["target_expr"] = None if call_target_expr is None else call_target_expr.to_string()
        return UnknownValueRef.deferred_call(
            deferred_call_ref=DeferredCallRef(
                target_ref=target_ref,
                sequence=7,
            ),
            target_ref=target_ref,
        )

    tracer.record_deferred_call = _record_deferred_call

    result = tracer._trace_pcode_op_internal(call_op, depth=0, use_cache=False)

    assert result.expr_type.name == "UNKNOWN"
    assert getattr(result.runtime_ref, "kind", None) == "deferred_call"
    assert recorded["target_ref"] == CallTargetRef.from_name("callee")
    assert recorded["args"] == ["param_1", "param_2"]
    assert recorded["target_expr"] == "4198400"


def test_effect_sensitive_wrapper_collapse_keeps_non_identity_binary_wrappers():
    analyzer = ReturnAnalyzer(program=None, debug=False)
    analyzer._current_parameters = [
        {"name": "param_1", "index": 0, "size": 8},
        {"name": "param_2", "index": 1, "size": 4},
    ]
    original = Expression.binary_op(
        "INT_SUB",
        Expression.memory(Expression.parameter("param_1", index=0, size=8), size=4),
        Expression.parameter("param_2", index=1, size=4),
    )
    rewritten = Expression.binary_op(
        "INT_SUB",
        Expression.constant(7, 4),
        Expression.parameter("param_2", index=1, size=4),
    )
    effect_summary = EffectSummary(
        parameter_names=["param_1", "param_2"],
        effects=[
            StoreEffect(
                location=CanonicalLocation("param_1", 0, 4),
                value=Expression.constant(7, 4),
                conditions=[],
                order_key=0,
            )
        ],
    )

    collapsed = analyzer._collapse_effect_sensitive_case_wrapper(
        original,
        rewritten,
        [],
        effect_summary,
    )

    assert collapsed.to_string() == rewritten.to_string()

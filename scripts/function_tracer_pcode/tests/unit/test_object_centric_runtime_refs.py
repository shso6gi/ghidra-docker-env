# -*- coding: utf-8 -*-

from scripts.function_tracer_pcode.analysis.effect_summary import (
    CanonicalLocation,
    post_state_read_expression_for_location,
)
from scripts.function_tracer_pcode.model import (
    CallTargetRef,
    DeferredCallInfo,
    CountedLoopSummaryRef,
    LocationBaseRef,
    LoopSummaryRef,
    LoopTermDescriptorRef,
    PostStateReadRef,
    PostStateSnapshotRef,
    ReadonlyReductionRef,
    StorageInfo,
    coerce_call_target_ref,
    compare_loop_summaries,
)
from scripts.function_tracer_pcode.tests.conftest import create_mock_analysis


def test_coerce_call_target_ref_rejects_raw_strings():
    assert coerce_call_target_ref("callee") is None


def test_loop_summary_comparator_interface_is_explicitly_unknown():
    summary = LoopSummaryRef(
        start_expr=0,
        limit_expr="n",
        step_expr=1,
        term_descriptor=LoopTermDescriptorRef(kind="memory_load", stride=4, element_size=4),
    )

    result = compare_loop_summaries(summary, summary)

    assert result.status == "unknown"
    assert result.is_equivalent() is None


def test_loop_summary_unkeyable_refs_disable_pairwise_exact_shortcut():
    unkeyable_summary = LoopSummaryRef(
        start_expr=object(),
        limit_expr="n",
        step_expr=1,
        term_descriptor=LoopTermDescriptorRef(kind="memory_load", stride=4, element_size=4),
    )
    readonly_ref = ReadonlyReductionRef(
        reduction_kind="memory_sum",
        pointer_base_ref=LocationBaseRef.parameter("ptr", index=0),
        count_parameter_name="n",
        count_parameter_index=1,
        stride=4,
        element_size=4,
        result_size=4,
        loop_summary=unkeyable_summary,
    )
    counted_ref = CountedLoopSummaryRef(
        induction_step=1,
        result_size=4,
        signed_loop=True,
        residue_cases=((1, 0, 1, 0),),
        loop_summary=unkeyable_summary,
    )

    assert unkeyable_summary.stable_key() is None
    assert readonly_ref.pairwise_exact_key() is None
    assert counted_ref.pairwise_exact_key() is None


def test_function_analysis_normalizes_deferred_calls_to_deferred_call_refs():
    info = DeferredCallInfo(
        placeholder_name="call_out_of_scope:callee#2",
        target_ref=CallTargetRef.from_name("callee"),
        sequence=2,
    )
    analysis = create_mock_analysis("wrapper")
    analysis.deferred_calls = {"legacy_placeholder": info}

    analysis.normalize_deferred_calls()

    assert list(analysis.deferred_calls) == [info.deferred_call_ref.stable_key()]


def test_location_base_parameter_identity_uses_index_not_name():
    left = LocationBaseRef.parameter("lhs", index=1)
    right = LocationBaseRef.parameter("rhs", index=1)

    assert left == right
    assert left.stable_key() == right.stable_key()


def test_location_base_parameter_identity_is_scoped_by_function_when_available():
    caller = LocationBaseRef.parameter(
        "param_2",
        index=1,
        owner_program_id=100,
        owner_entry_offset=0x401000,
    )
    callee = LocationBaseRef.parameter(
        "param_2",
        index=1,
        owner_program_id=100,
        owner_entry_offset=0x402000,
    )

    assert caller != callee
    assert caller.stable_key() != callee.stable_key()


def test_storage_info_register_identity_uses_numeric_base_metadata():
    left = StorageInfo(
        is_register=True,
        space_name="register",
        space_id=3,
        offset=0x10,
        size=4,
        size_bits=32,
        register_name="w0",
        register_offset=0x10,
        register_size=4,
        register_size_bits=32,
        base_register_name="x0",
        base_register_offset=0x10,
        base_register_size=8,
        base_register_size_bits=64,
        bit_offset_in_base=0,
    )
    right = StorageInfo(
        is_register=True,
        space_name="register",
        space_id=3,
        offset=0x10,
        size=4,
        size_bits=32,
        register_name="arg0_low",
        register_offset=0x10,
        register_size=4,
        register_size_bits=32,
        base_register_name="param_alias",
        base_register_offset=0x10,
        base_register_size=8,
        base_register_size_bits=64,
        bit_offset_in_base=0,
    )

    assert left.shares_base_register_with(right) is True
    assert left.register_identity_key() == right.register_identity_key()


def test_storage_info_matches_base_register_by_name_when_numeric_offsets_differ():
    synthetic = StorageInfo(
        is_register=True,
        space_name="register",
        space_id=0,
        size=8,
        size_bits=64,
        register_name="v0",
        base_register_name="v0",
        base_register_offset=StorageInfo._synthetic_register_offset("v0"),
        base_register_size=8,
        base_register_size_bits=64,
        bit_offset_in_base=0,
    )
    concrete = StorageInfo(
        is_register=True,
        space_name="register",
        space_id=548,
        offset=0x10,
        size=8,
        size_bits=64,
        register_name="v0",
        register_offset=0x10,
        register_size=8,
        register_size_bits=64,
        base_register_name="v0",
        base_register_offset=0x10,
        base_register_size=8,
        base_register_size_bits=64,
        bit_offset_in_base=0,
    )

    assert synthetic.base_register_offset != concrete.base_register_offset
    assert synthetic.shares_base_register_with(concrete) is True


def test_post_state_symbolic_locations_bind_parameter_indices():
    parameters = [{"name": "trace", "index": 0, "size": 8}]
    expr = post_state_read_expression_for_location(
        CanonicalLocation("trace", 4, 4),
        parameters,
        symbolic=True,
    )

    runtime_ref = expr.runtime_ref
    assert isinstance(runtime_ref, PostStateReadRef)
    assert runtime_ref.location.base_ref == LocationBaseRef.parameter("trace", index=0)
    assert runtime_ref.snapshot_ref == PostStateSnapshotRef.function_return()

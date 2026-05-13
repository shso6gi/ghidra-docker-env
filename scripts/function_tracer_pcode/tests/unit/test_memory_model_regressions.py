# -*- coding: utf-8 -*-

from typing import Optional
from conftest import resolve_mock_data_type

from scripts.function_tracer_pcode.analysis.memory_resolver import (
    collect_memory_bit_widths_from_analysis,
    concretize_readonly_loads,
)
from scripts.function_tracer_pcode.analysis.effect_summary import (
    CallArgumentEvidence,
    CallArgumentWidthEvidence,
    CanonicalLocation,
    LocationStep,
    StoreEffect,
    _additive_signature,
    _build_parameter_replacements,
    _enumerate_call_argument_variants,
    _resolve_call_target_ref,
    _resolve_call_target_name,
    _resolve_parameter_name,
    _storage_matches_parameter,
    subtract_implied_conditions,
    is_call_effect_summary_allowed,
    build_void_effect_summary_expr,
    canonicalize_location,
    canonicalize_param_location,
    canonicalize_post_state_subexpressions,
    collapse_post_state_expr_to_canonical_memory,
    collapse_pruned_post_state_memory_leaf_to_canonical_memory,
    expression_contains_post_state_reads,
    expression_matches_stale_post_state_replay,
    lower_post_state_expression_for_smt,
    memory_expression_for_location,
    normalize_post_state_expression,
    post_state_read_expression_for_location,
    promote_observed_loads_to_post_state_reads,
    rewrite_loads_from_effects,
    rewrite_location_read_from_effects,
    rewrite_observed_loads_from_effects,
    summarize_store_effects,
    substitute_condition,
    substitute_location,
    _choose_effect_substitution_args,
    _find_block_info_for_pcode_op,
    _recover_call_argument_expressions,
    _recover_call_argument_from_storage,
    _merge_call_argument_evidence,
    _record_call_argument_evidence,
    _resolve_call_argument_expression,
    _normalize_call_argument_expression,
    _call_argument_semantic_rank,
    _call_arguments_width_safe_for_callee_analysis,
    _call_evidence_callee_param_identities,
    _coerce_argument_to_callee_parameter,
    _coerce_callee_parameter_ref,
    _find_matching_effect_value,
    _parameter_base_ref_matches_descriptor,
    EffectSummary,
)
from scripts.function_tracer_pcode.model import (
    AddressValueRef,
    CallTargetRef,
    DeferredCallRef,
    DeferredCallInfo,
    LocationBaseRef,
    ObservedMemoryReadRef,
    PostStateReadRef,
    PostStateSnapshotRef,
    PostStateValueRef,
    PcodeOpRef,
)
from scripts.function_tracer_pcode.analysis.analyzer import ReturnAnalyzer
from scripts.function_tracer_pcode.analysis.phi_resolver import ExpandedBranch as PhiExpandedBranch, PhiHandler
from scripts.function_tracer_pcode.analysis.tracer import PcodeTracer
from scripts.function_tracer_pcode.equivalence.typing.fixer import TypeFixer, TypeFixerConfig
from scripts.function_tracer_pcode.equivalence.arch.mips64 import MIPS64Handler
from scripts.function_tracer_pcode.equivalence.formula.builder import FormulaBuilder
from scripts.function_tracer_pcode.equivalence.param_semantics import ParameterSemanticHint
from scripts.function_tracer_pcode.equivalence.normalize.core import normalize_expression
from scripts.function_tracer_pcode.model import Condition, Expression, ExpressionType, FunctionReturnAnalysis, ReturnInfo
from scripts.function_tracer_pcode.model.storage import StorageInfo
from scripts.function_tracer_pcode.transform.expander import ExpressionExpander, ExpandedValue


def _param(
    name: str,
    size: int = 4,
    is_signed: bool = True,
    index: int = 0,
    storage=None,
    data_type: Optional[str] = None,
    data_type_obj=None,
):
    result = {"name": name, "size": size, "is_signed": is_signed, "index": index}
    if storage is not None:
        result["storage"] = storage
    if data_type is not None:
        result["data_type"] = data_type
    if data_type_obj is not None:
        result["data_type_obj"] = data_type_obj
    return result


def _runtime_location(expr):
    runtime_ref = getattr(expr, "runtime_ref", None)
    if isinstance(runtime_ref, CanonicalLocation):
        return runtime_ref
    return getattr(runtime_ref, "location", None)


def _runtime_snapshot(expr):
    runtime_ref = getattr(expr, "runtime_ref", None)
    return getattr(runtime_ref, "snapshot_ref", None)


_LEGACY_TEST_PARAM_INDEX = {
    "a": 0,
    "b": 1,
    "box": 0,
    "bias": 2,
    "delta": 1,
    "dst": 0,
    "guard": 0,
    "lhs": 1,
    "limit": 2,
    "negate": 2,
    "out": 1,
    "pick_right": 1,
    "ptr": 0,
    "rhs": 2,
    "selector": 0,
    "slot": 0,
    "src": 1,
    "start": 1,
    "trace": 0,
    "value": 0,
}


def _loc(name: str, offset: int = 0, size: int = 0, steps=()):
    if name in {"stackframe", "__locbase__stackframe"}:
        return CanonicalLocation(name, offset, size, steps=steps)
    if name.startswith("param_"):
        try:
            index = int(name.split("_", 1)[1]) - 1
        except Exception:
            index = None
    else:
        index = _LEGACY_TEST_PARAM_INDEX.get(name)
    return CanonicalLocation(
        base_ref=LocationBaseRef.parameter(name, index=index),
        offset=offset,
        size=size,
        steps=steps,
    )


def _observed_read(
    name: str,
    *,
    index: int,
    size: int,
    order_key: int,
):
    return ObservedMemoryReadRef(
        order_key=order_key,
        location=_loc(name, 0, size),
        pcode_op_ref=PcodeOpRef(
            address_offset=0x1000 + order_key,
            seq_time=order_key,
            seq_order=order_key & 0xFF,
            block_index=index,
            mnemonic="LOAD",
        ),
    )


def _reg_storage(base_name: str, size_bytes: int = 8, register_name: Optional[str] = None):
    register_name = register_name or base_name
    return {
        "is_register": True,
        "space_name": "register",
        "offset": 0,
        "size": size_bytes,
        "size_bits": size_bytes * 8,
        "register_name": register_name,
        "base_register_name": base_name,
        "base_register_offset": 0,
        "base_register_size": size_bytes,
        "base_register_size_bits": size_bytes * 8,
        "bit_offset_in_base": 0,
    }


def _stack_storage(offset: int, size_bytes: int = 4):
    return {
        "is_register": False,
        "space_name": "stack",
        "offset": offset,
        "size": size_bytes,
        "size_bits": size_bytes * 8,
    }


def _addr_var(name: str, address_offset: int, size: int = 8) -> Expression:
    return Expression.variable(
        name,
        size=size,
        runtime_ref=AddressValueRef(
            address_offset=address_offset,
            display_hint=name,
            symbol_name=name,
            is_initialized=True,
            can_read=True,
            can_write=False,
            is_volatile=False,
        ),
    )


def test_enumerate_call_argument_variants_dedup_does_not_require_to_string(monkeypatch):
    shared = Expression.parameter("param_1", index=0, size=4)
    phi_expr = Expression.phi(
        [
            (Condition(Expression.binary_op("INT_EQUAL", shared, Expression.constant(0, 4))), shared),
            (Condition(Expression.binary_op("INT_EQUAL", shared, Expression.constant(0, 4))), shared),
        ]
    )

    def _boom_expr(_self, simplify=True):
        raise AssertionError("variant dedup should not depend on Expression.to_string")

    def _boom_cond(_self):
        raise AssertionError("variant dedup should not depend on Condition.to_string")

    monkeypatch.setattr(Expression, "to_string", _boom_expr)
    monkeypatch.setattr(Condition, "to_string", _boom_cond)

    variants = _enumerate_call_argument_variants([phi_expr])

    assert len(variants) == 1
    assert variants[0][1][0].structural_key(normalize_commutative=True) == shared.structural_key(
        normalize_commutative=True
    )


def test_normalize_expression_preserves_memory_identity_metadata():
    location = _loc("trace", 0, 4)
    traced_load = Expression.memory(
        Expression.parameter("trace", 0, size=8),
        size=4,
        read_order_key=42,
        runtime_ref=location,
    )
    expr = Expression.binary_op("INT_ADD", traced_load, Expression.constant(1, 4))

    normalized = normalize_expression(expr)
    normalized_memory = next(
        operand for operand in normalized.operands if operand.expr_type == ExpressionType.MEMORY
    )

    assert normalized_memory.read_order_key == 42
    assert getattr(normalized_memory, "runtime_ref", None) == location


def test_concretize_readonly_loads_preserves_unresolved_memory_identity_metadata():
    location = _loc("trace", 0, 4)
    expr = Expression.memory(
        Expression.parameter("trace", 0, size=8),
        size=4,
        read_order_key=17,
        runtime_ref=location,
    )

    rewritten = concretize_readonly_loads(
        expr,
        [],
        [_param("trace", size=8, is_signed=False)],
        lambda *_args: None,
    )

    assert rewritten.read_order_key == 17
    assert getattr(rewritten, "runtime_ref", None) == location


def test_additive_signature_does_not_require_to_string(monkeypatch):
    shared = Expression.parameter("param_1", index=0, size=4)
    expr = Expression.binary_op("INT_ADD", shared, Expression.constant(4, 4))
    expr.size = 4

    def _boom_expr(_self, simplify=True):
        raise AssertionError("additive signature should not depend on Expression.to_string")

    monkeypatch.setattr(Expression, "to_string", _boom_expr)

    signature = _additive_signature(expr)

    assert signature is not None
    constant, terms, width = signature
    assert constant == 4
    assert len(terms) == 1
    assert width == 4


def test_call_argument_semantic_rank_uses_pointer_datatype_object_not_name():
    class MockPointerType:
        def isPointer(self):
            return True

    rank = _call_argument_semantic_rank(
        Expression.constant(0, size=8),
        caller_parameters=[],
        callee_param={
            "name": "param_1",
            "size": 8,
            "data_type": "opaque_alias",
            "data_type_obj": MockPointerType(),
        },
    )

    assert rank == 3


def test_formula_builder_declares_memory_arrays_for_memory_returns():
    analysis1 = FunctionReturnAnalysis(
        function_name="f1",
        entry_point="0x0",
        parameters=[_param("p", size=8)],
        returns=[
            ReturnInfo(
                address="0x1",
                conditions=[],
                value=Expression.memory(Expression.parameter("p", 0, size=8), size=4),
            )
        ],
        return_type="int",
    )
    analysis2 = FunctionReturnAnalysis(
        function_name="f2",
        entry_point="0x0",
        parameters=[_param("q", size=8)],
        returns=[
            ReturnInfo(
                address="0x2",
                conditions=[],
                value=Expression.memory(Expression.parameter("q", 0, size=8), size=4),
            )
        ],
        return_type="int",
    )

    builder = FormulaBuilder(debug=False, exclude_ub=False)
    formula = builder.build_equivalence_formula_extended(analysis1, analysis2).formula

    assert "(declare-const mem32 (Array (_ BitVec 64) (_ BitVec 32)))" in formula
    assert "(select mem32 p_1)" in formula
    assert "(select mem32 q_2)" in formula
    assert collect_memory_bit_widths_from_analysis(analysis1) == [32]


def test_mips64_handler_detects_spurious_same_pattern_extension_violation():
    handler = MIPS64Handler(debug=False)
    counterexample = {"param_1_1": 0x400000000002, "param_1_2": 0x400000000002}
    analysis1 = FunctionReturnAnalysis(
        function_name="f1",
        entry_point="0x0",
        parameters=[{"name": "param_1", "data_type": "long", "size": 8, "index": 0, "is_signed": True}],
        returns=[],
    )
    analysis2 = FunctionReturnAnalysis(
        function_name="f2",
        entry_point="0x0",
        parameters=[{"name": "param_1", "data_type": "long", "size": 8, "index": 0, "is_signed": True}],
        returns=[],
    )

    handler._analyze_parameter_usage = lambda analysis: {
        ("parameter_index", 0): ParameterSemanticHint(narrow_bits=32, signedness="signed")
    }

    constraints = handler.detect_spurious_counterexample(
        counterexample,
        analysis1,
        analysis2,
        is_mips64_1=True,
        is_mips64_2=True,
    )

    assert constraints == {"param_1_1": ("signed", 32), "param_1_2": ("signed", 32)}


def test_memory_resolver_concretizes_small_readonly_jump_table():
    param = Expression.parameter("param_1", 0, size=8)
    index_expr = Expression.unary_op(
        "INT_SEXT",
        Expression.binary_op("SUBPIECE", param, Expression.constant(0, 4)),
    )
    index_expr.size = 8
    address_expr = Expression.binary_op(
        "INT_ADD",
        _addr_var("PTR_00112058", 0x00112058, size=8),
        Expression.binary_op(
            "INT_ADD",
            Expression.binary_op("INT_MULT", index_expr, Expression.constant(4, 8)),
            Expression.constant(5024, 8),
        ),
    )
    load_expr = Expression.memory(address_expr, size=4)
    cond = Condition(
        Expression.binary_op("INT_LESS", param, Expression.constant(4, 8)),
        False,
    )

    table = {
        0x00112058 + 5024 + 0: 1,
        0x00112058 + 5024 + 4: 1,
        0x00112058 + 5024 + 8: 2,
        0x00112058 + 5024 + 12: 2,
    }

    resolved = concretize_readonly_loads(
        load_expr,
        [cond],
        [_param("param_1", size=8, is_signed=False)],
        lambda addr, size: table.get(addr),
        debug=False,
    )

    assert resolved.expr_type.name == "PHI"
    values = [branch_value.value for _, branch_value in resolved.value[:-1]]
    assert values == [1, 1, 2, 2]


def test_memory_resolver_concretizes_direct_readonly_pointer_slot():
    load_expr = Expression.memory(
        _addr_var("PTR_ptr_op_add_00113090", 0x00113090, size=8),
        size=8,
    )

    table = {
        0x00113090: 0x401120,
    }

    resolved = concretize_readonly_loads(
        load_expr,
        [],
        [],
        lambda addr, size: table.get(addr),
        debug=False,
    )

    assert resolved.expr_type.name == "CONSTANT"
    assert resolved.value == 0x401120


def test_memory_resolver_concretizes_direct_readonly_scalar_symbol_in_value_position():
    expr = Expression.binary_op(
        "INT_ADD",
        _addr_var("DAT_00113090", 0x00113090, size=8),
        Expression.constant(1, 8),
    )

    table = {
        0x00113090: 0x401120,
    }

    resolved = concretize_readonly_loads(
        expr,
        [],
        [],
        lambda addr, size: table.get(addr),
        debug=False,
    )

    assert resolved.expr_type.name == "BINARY_OP"
    assert resolved.operands[0].expr_type.name == "CONSTANT"
    assert resolved.operands[0].value == 0x401120
    assert resolved.operands[1].expr_type.name == "CONSTANT"
    assert resolved.operands[1].value == 1


def test_memory_resolver_concretizes_direct_unknown_symbol_when_readable():
    expr = Expression.binary_op(
        "INT_ADD",
        _addr_var("UNK_00113090", 0x00113090, size=8),
        Expression.constant(1, 8),
    )

    table = {
        0x00113090: 0x401120,
    }

    resolved = concretize_readonly_loads(
        expr,
        [],
        [],
        lambda addr, size: table.get(addr),
        debug=False,
    )

    assert resolved.expr_type.name == "BINARY_OP"
    assert resolved.operands[0].expr_type.name == "CONSTANT"
    assert resolved.operands[0].value == 0x401120
    assert resolved.operands[1].expr_type.name == "CONSTANT"
    assert resolved.operands[1].value == 1


def test_memory_resolver_concretizes_jump_table_when_additive_index_is_wrapped_by_mul_one():
    param = Expression.parameter("param_1", 0, size=8)
    subpiece = Expression.binary_op("SUBPIECE", param, Expression.constant(0, 4))
    subpiece.size = 4
    index_expr = Expression.unary_op("INT_SEXT", subpiece)
    index_expr.size = 8
    address_expr = Expression.binary_op(
        "INT_ADD",
        _addr_var("PTR_00112058", 0x00112058, size=8),
        Expression.binary_op(
            "INT_MULT",
            Expression.constant(1, 8),
            Expression.binary_op(
                "INT_ADD",
                Expression.constant(5024, 8),
                Expression.binary_op("INT_MULT", index_expr, Expression.constant(4, 8)),
            ),
        ),
    )
    load_expr = Expression.memory(address_expr, size=4)
    cond = Condition(
        Expression.binary_op("INT_LESS", param, Expression.constant(4, 8)),
        False,
    )

    table = {
        0x00112058 + 5024 + 0: 1,
        0x00112058 + 5024 + 4: 1,
        0x00112058 + 5024 + 8: 2,
        0x00112058 + 5024 + 12: 2,
    }

    resolved = concretize_readonly_loads(
        load_expr,
        [cond],
        [_param("param_1", size=8, is_signed=False)],
        lambda addr, size: table.get(addr),
        debug=False,
    )

    assert resolved.expr_type.name == "PHI"
    values = [branch_value.value for _, branch_value in resolved.value[:-1]]
    assert values == [1, 1, 2, 2]


def test_memory_resolver_concretizes_mips_pic_jump_table_using_image_base_fallback():
    param = Expression.parameter("param_1", 0, size=8)
    subpiece = Expression.binary_op("SUBPIECE", param, Expression.constant(0, 4))
    subpiece.size = 4
    index_expr = Expression.unary_op("INT_SEXT", subpiece)
    index_expr.size = 8
    address_expr = Expression.binary_op(
        "INT_ADD",
        _addr_var("PTR_00112058", 0x00112058, size=8),
        Expression.binary_op(
            "INT_MULT",
            Expression.binary_op(
                "INT_ADD",
                Expression.binary_op("INT_MULT", index_expr, Expression.constant(4, 8)),
                Expression.constant(0x13A0, 8),
            ),
            Expression.constant(1, 8),
        ),
    )
    load_expr = Expression.memory(address_expr, size=4)
    cond = Condition(
        Expression.binary_op("INT_LESS", param, Expression.constant(4, 8)),
        False,
    )

    image_base = 0x00100000
    table = {
        image_base + 0x13A0 + 0: 1,
        image_base + 0x13A0 + 4: 1,
        image_base + 0x13A0 + 8: 2,
        image_base + 0x13A0 + 12: 2,
    }

    resolved = concretize_readonly_loads(
        load_expr,
        [cond],
        [_param("param_1", size=8, is_signed=False)],
        lambda addr, size: table.get(addr),
        image_base=image_base,
        debug=False,
    )

    assert resolved.expr_type.name == "PHI"
    values = [branch_value.value for _, branch_value in resolved.value[:-1]]
    assert values == [1, 1, 2, 2]


def test_memory_resolver_accepts_unsigned_lessequal_range_conditions():
    param = Expression.parameter("param_1", 0, size=4)
    address_expr = Expression.binary_op(
        "INT_ADD",
        Expression.binary_op("INT_ADD", Expression.constant(0, 8), Expression.constant(0x1009EC, 8)),
        Expression.binary_op(
            "INT_MULT",
            Expression.binary_op("INT_MULT", Expression.unary_op("INT_ZEXT", param), Expression.constant(1, 8)),
            Expression.constant(4, 8),
        ),
    )
    load_expr = Expression.memory(address_expr, size=4)
    cond = Condition(
        Expression.binary_op("INT_LESSEQUAL", param, Expression.constant(5, 4)),
        False,
    )

    table = {
        0x1009EC + 0: 5,
        0x1009EC + 4: 7,
        0x1009EC + 8: 11,
        0x1009EC + 12: 13,
        0x1009EC + 16: 17,
        0x1009EC + 20: 19,
    }

    resolved = concretize_readonly_loads(
        load_expr,
        [cond],
        [_param("param_1", size=4, is_signed=False)],
        lambda addr, size: table.get(addr),
        debug=False,
    )

    assert resolved.expr_type.name == "PHI"
    values = [branch_value.value for _, branch_value in resolved.value[:-1]]
    assert values == [5, 7, 11, 13, 17, 19]


def test_memory_resolver_accepts_cast_wrapped_parameter_range_conditions():
    param = Expression.parameter("param_1", 0, size=4)
    index = Expression.unary_op("INT_ZEXT", param)
    index.size = 8
    address_expr = Expression.binary_op(
        "INT_ADD",
        Expression.binary_op("INT_ADD", Expression.constant(0, 8), Expression.constant(0x1009EC, 8)),
        Expression.binary_op(
            "INT_MULT",
            Expression.binary_op("INT_MULT", index, Expression.constant(1, 8)),
            Expression.constant(4, 8),
        ),
    )
    load_expr = Expression.memory(address_expr, size=4)
    widened_param = Expression.unary_op("INT_ZEXT", param)
    widened_param.size = 8
    cond = Condition(
        Expression.binary_op("INT_LESS", widened_param, Expression.constant(4, 8)),
        False,
    )

    table = {
        0x1009EC + 0: 5,
        0x1009EC + 4: 7,
        0x1009EC + 8: 11,
        0x1009EC + 12: 13,
    }

    resolved = concretize_readonly_loads(
        load_expr,
        [cond],
        [_param("param_1", size=4, is_signed=False)],
        lambda addr, size: table.get(addr),
        debug=False,
    )

    assert resolved.expr_type.name == "PHI"
    values = [branch_value.value for _, branch_value in resolved.value[:-1]]
    assert values == [5, 7, 11, 13]


def test_memory_resolver_accepts_cast_then_zext_parameter_range_conditions():
    param = Expression.parameter("param_1", 0, size=4)
    cast_param = Expression.unary_op("CAST", param)
    cast_param.size = 4
    index = Expression.unary_op("INT_ZEXT", cast_param)
    index.size = 8
    address_expr = Expression.binary_op(
        "INT_ADD",
        Expression.binary_op("INT_ADD", Expression.constant(0, 8), Expression.constant(0x1009EC, 8)),
        Expression.binary_op(
            "INT_MULT",
            Expression.binary_op("INT_MULT", index, Expression.constant(1, 8)),
            Expression.constant(4, 8),
        ),
    )
    load_expr = Expression.memory(address_expr, size=4)
    cond = Condition(
        Expression.binary_op("INT_LESS", index, Expression.constant(4, 8)),
        False,
    )

    table = {
        0x1009EC + 0: 5,
        0x1009EC + 4: 7,
        0x1009EC + 8: 11,
        0x1009EC + 12: 13,
    }

    resolved = concretize_readonly_loads(
        load_expr,
        [cond],
        [_param("param_1", size=4, is_signed=False)],
        lambda addr, size: table.get(addr),
        debug=False,
    )

    assert resolved.expr_type.name == "PHI"
    values = [branch_value.value for _, branch_value in resolved.value[:-1]]
    assert values == [5, 7, 11, 13]


def test_memory_resolver_accepts_cast_then_zext_for_signed_parameter_indices():
    param = Expression.parameter("param_1", 0, size=4)
    cast_param = Expression.unary_op("CAST", param)
    cast_param.size = 4
    index = Expression.unary_op("INT_ZEXT", cast_param)
    index.size = 8
    address_expr = Expression.binary_op(
        "INT_ADD",
        Expression.binary_op("INT_ADD", Expression.constant(0, 8), Expression.constant(0x1009EC, 8)),
        Expression.binary_op(
            "INT_MULT",
            Expression.binary_op("INT_MULT", index, Expression.constant(1, 8)),
            Expression.constant(4, 8),
        ),
    )
    load_expr = Expression.memory(address_expr, size=4)
    cond = Condition(
        Expression.binary_op("INT_LESS", index, Expression.constant(4, 8)),
        False,
    )

    table = {
        0x1009EC + 0: 5,
        0x1009EC + 4: 7,
        0x1009EC + 8: 11,
        0x1009EC + 12: 13,
    }

    resolved = concretize_readonly_loads(
        load_expr,
        [cond],
        [_param("param_1", size=4, is_signed=True)],
        lambda addr, size: table.get(addr),
        debug=False,
    )

    assert resolved.expr_type.name == "PHI"
    values = [branch_value.value for _, branch_value in resolved.value[:-1]]
    assert values == [5, 7, 11, 13]


def test_memory_resolver_accepts_negated_less_condition_as_upper_bound():
    param = Expression.parameter("param_1", 0, size=4)
    index = Expression.unary_op("INT_ZEXT", param)
    index.size = 8
    address_expr = Expression.binary_op(
        "INT_ADD",
        Expression.binary_op("INT_ADD", Expression.constant(0, 8), Expression.constant(0x1009EC, 8)),
        Expression.binary_op(
            "INT_MULT",
            Expression.binary_op("INT_MULT", index, Expression.constant(1, 8)),
            Expression.constant(4, 8),
        ),
    )
    load_expr = Expression.memory(address_expr, size=4)
    cond = Condition(
        Expression.binary_op("INT_LESS", Expression.constant(5, 4), param),
        True,
    )

    table = {
        0x1009EC + 0: 5,
        0x1009EC + 4: 7,
        0x1009EC + 8: 11,
        0x1009EC + 12: 13,
        0x1009EC + 16: 17,
        0x1009EC + 20: 19,
    }

    resolved = concretize_readonly_loads(
        load_expr,
        [cond],
        [_param("param_1", size=4, is_signed=False)],
        lambda addr, size: table.get(addr),
        debug=False,
    )

    assert resolved.expr_type.name == "PHI"
    values = [branch_value.value for _, branch_value in resolved.value[:-1]]
    assert values == [5, 7, 11, 13, 17, 19]


def test_memory_resolver_concretizes_mips_got_base_symbol_with_address_suffix():
    param = Expression.parameter("param_1", 0, size=8)
    address_expr = Expression.binary_op(
        "INT_ADD",
        _addr_var("PTR___DT_MIPS_BASE_ADDRESS_120011050", 0x120011050, size=8),
        Expression.binary_op(
            "INT_MULT",
            Expression.binary_op(
                "INT_ADD",
                Expression.binary_op("INT_MULT", param, Expression.constant(4, 8)),
                Expression.constant(0xF00, 8),
            ),
            Expression.constant(1, 8),
        ),
    )
    load_expr = Expression.memory(address_expr, size=4)
    cond = Condition(
        Expression.binary_op("INT_LESS", param, Expression.constant(6, 8)),
        False,
    )

    got_slot = 0x120011050
    image_base = 0x120000000
    table = {
        got_slot: image_base,
        image_base + 0xF00 + 0: 5,
        image_base + 0xF00 + 4: 7,
        image_base + 0xF00 + 8: 11,
        image_base + 0xF00 + 12: 13,
        image_base + 0xF00 + 16: 17,
        image_base + 0xF00 + 20: 19,
    }

    resolved = concretize_readonly_loads(
        load_expr,
        [cond],
        [_param("param_1", size=8, is_signed=False)],
        lambda addr, size: table.get(addr),
        debug=False,
    )

    assert resolved.expr_type.name == "PHI"
    values = [branch_value.value for _, branch_value in resolved.value[:-1]]
    assert values == [5, 7, 11, 13, 17, 19]


def test_memory_resolver_splits_load_of_phi_address_into_phi_of_loads():
    base = Expression.parameter("param_1", 0, size=8)
    addr_phi = Expression.phi(
        [
            (
                Condition(
                    Expression.binary_op(
                        "INT_NOTEQUAL",
                        Expression.parameter("pick_right", 1, size=4),
                        Expression.constant(0, 4),
                    ),
                    False,
                ),
                Expression.binary_op("INT_ADD", base, Expression.constant(4, 8)),
            ),
            (None, base),
        ]
    )
    addr_phi.size = 8
    load_expr = Expression.memory(addr_phi, size=4)

    resolved = concretize_readonly_loads(
        load_expr,
        [],
        [_param("param_1", size=8, is_signed=False), _param("pick_right", size=4)],
        lambda addr, size: None,
        debug=False,
    )

    assert resolved.expr_type.name == "PHI"
    assert resolved.value[0][1].expr_type.name == "MEMORY"
    assert resolved.value[1][1].expr_type.name == "MEMORY"


def test_memory_resolver_splits_bool_scaled_offset_load_into_two_loads():
    base = Expression.parameter("param_1", 0, size=8)
    cond_expr = Expression.binary_op(
        "INT_NOTEQUAL",
        Expression.parameter("pick_right", 1, size=4),
        Expression.constant(0, 4),
    )
    addr_expr = Expression.binary_op(
        "INT_ADD",
        base,
        Expression.binary_op("INT_MULT", cond_expr, Expression.constant(4, 8)),
    )
    load_expr = Expression.memory(addr_expr, size=4)

    resolved = concretize_readonly_loads(
        load_expr,
        [],
        [_param("param_1", size=8, is_signed=False), _param("pick_right", size=4)],
        lambda addr, size: None,
        debug=False,
    )

    assert resolved.expr_type.name == "PHI"
    first_addr = resolved.value[0][1].operands[0]
    second_addr = resolved.value[1][1].operands[0]
    assert first_addr.to_string() == "(param_1 + 4)"
    assert second_addr.to_string() == "param_1"


def test_effect_summary_rewrites_load_from_prior_store_under_same_path():
    ptr = Expression.parameter("ptr", 0, size=8)
    value = Expression.parameter("value", 1, size=4)
    original = Expression.binary_op(
        "INT_ADD",
        Expression.memory(ptr, size=4),
        Expression.constant(0xFFFFFFFF, 4),
    )
    effect = StoreEffect(
        location=_loc("ptr", 0, 4),
        value=Expression.binary_op("INT_ADD", value, Expression.constant(3, 4)),
        conditions=[
            Condition(
                Expression.binary_op("INT_NOTEQUAL", ptr, Expression.constant(0, 8)),
                False,
            )
        ],
        order_key=1,
    )

    rewritten = rewrite_loads_from_effects(
        original,
        effect.conditions,
        [effect],
        [_param("ptr", size=8, is_signed=False), _param("value", size=4, index=1)],
    )

    assert rewritten.to_string() == "((value + 3) + 4294967295)"


def test_effect_summary_builds_synthetic_expr_for_void_writes():
    ptr = Expression.parameter("ptr", 0, size=8)
    value = Expression.parameter("value", 1, size=4)
    positive = Condition(
        Expression.binary_op("INT_SLESS", Expression.constant(0, 4), value),
        False,
    )
    non_positive = positive.negate()
    effects = [
        StoreEffect(
            location=_loc("ptr", 0, 4),
            value=value,
            conditions=[positive],
            order_key=2,
        ),
        StoreEffect(
            location=_loc("ptr", 0, 4),
            value=Expression.unary_op("INT_2COMP", value),
            conditions=[non_positive],
            order_key=1,
        ),
    ]

    summary = build_void_effect_summary_expr(effects)

    assert summary is not None
    assert summary.expr_type.name == "BINARY_OP"
    assert summary.operator == "PIECE"


def test_effect_summary_accepts_variable_based_parameter_addresses():
    addr_expr = Expression.parameter("ptr", 0, size=8)

    location = canonicalize_param_location(
        addr_expr,
        [_param("ptr", size=8, is_signed=False)],
        size=4,
    )

    assert location == _loc("ptr", 0, 4)


def test_effect_summary_accepts_variable_plus_constant_parameter_addresses():
    addr_expr = Expression.binary_op(
        "INT_ADD",
        Expression.parameter("box", 0, size=8),
        Expression.constant(4, 8),
    )

    location = canonicalize_param_location(
        addr_expr,
        [_param("box", size=8, is_signed=False)],
        size=4,
    )

    assert location == _loc("box", 4, 4)


def test_effect_summary_accepts_register_alias_parameter_addresses():
    addr_expr = Expression.variable(
        "saved_arg",
        size=8,
        storage_info=StorageInfo(
            is_register=True,
            space_name="register",
            register_name="A0",
            base_register_name="A0",
            size=8,
            size_bits=64,
            base_register_size=8,
            base_register_size_bits=64,
            bit_offset_in_base=0,
        ),
    )

    location = canonicalize_param_location(
        addr_expr,
        [_param("param_1", size=8, is_signed=False, storage=_reg_storage("A0"))],
        size=4,
    )

    assert location == _loc("param_1", 0, 4)


def test_effect_summary_accepts_double_indirect_parameter_addresses():
    addr_expr = Expression.memory(
        Expression.parameter("slot", 0, size=8),
        size=8,
    )

    location = canonicalize_param_location(
        addr_expr,
        [_param("slot", size=8, is_signed=False)],
        size=4,
    )

    assert location == CanonicalLocation(
        base_ref=LocationBaseRef.parameter("slot", index=0),
        offset=0,
        size=4,
        steps=(LocationStep("deref", 8),),
    )


def test_memory_expression_for_location_reconstructs_double_indirect_location():
    expr = memory_expression_for_location(
        CanonicalLocation(
            base_ref=LocationBaseRef.parameter("slot", index=0),
            offset=0,
            size=4,
            steps=(LocationStep("deref", 8),),
        ),
        [_param("slot", size=8, is_signed=False)],
    )

    assert expr is not None
    assert expr.to_string() == "MEM[MEM[slot]]"


def test_substitute_location_accepts_register_alias_call_arguments():
    call_args = [
        Expression.variable(
            "arg_a",
            size=8,
            storage_info=StorageInfo(
                is_register=True,
                space_name="register",
                register_name="A0",
                base_register_name="A0",
                size=8,
                size_bits=64,
                base_register_size=8,
                base_register_size_bits=64,
                bit_offset_in_base=0,
            ),
        ),
        Expression.variable(
            "arg_b",
            size=8,
            storage_info=StorageInfo(
                is_register=True,
                space_name="register",
                register_name="A1",
                base_register_name="A1",
                size=8,
                size_bits=64,
                base_register_size=8,
                base_register_size_bits=64,
                bit_offset_in_base=0,
            ),
        ),
    ]

    substituted = substitute_location(
        _loc("a", 0, 4),
        [{"name": "a", "index": 0}, {"name": "b", "index": 1}],
        call_args,
        [
            _param("param_1", size=8, is_signed=False, storage=_reg_storage("A0")),
            _param("param_2", size=8, is_signed=False, index=1, storage=_reg_storage("A1")),
        ],
    )

    assert substituted == _loc("param_1", 0, 4)


def test_substitute_location_accepts_stack_local_call_arguments():
    caller_params = [_param("param_1", size=8, is_signed=False)]
    local_out = Expression.variable(
        "local_out",
        size=8,
        storage_info=StorageInfo(**_stack_storage(24, size_bytes=4)),
    )

    substituted = substitute_location(
        _loc("out", 0, 4),
        [{"name": "in", "index": 0}, {"name": "out", "index": 1}],
        [Expression.parameter("param_1", 0, size=8), local_out],
        caller_params,
    )

    assert substituted == canonicalize_location(local_out, caller_params, size=4)


def test_substitute_location_accepts_storage_only_callee_effect_base():
    callee_storage = StorageInfo(**_reg_storage("a0", size_bytes=8))
    callee_location = CanonicalLocation(
        base_ref=LocationBaseRef.storage(
            space_id=callee_storage.space_id,
            space_name=callee_storage.space_name,
            offset=callee_storage.offset,
            size=callee_storage.size,
            storage_identity_key=callee_storage.storage_identity_key(),
        ),
        offset=0,
        size=4,
    )
    actual_dst = Expression.parameter("dst", 0, size=8, data_type="int *")

    substituted = substitute_location(
        callee_location,
        [{"name": "callee_dst", "size": 8, "storage": _reg_storage("a0", size_bytes=8)}],
        [actual_dst],
        [_param("dst", size=8, index=0, data_type="int *")],
    )

    assert substituted == _loc("dst", 0, 4)


def test_canonicalize_location_accepts_stack_pointer_relative_address_expression():
    params = [_param("param_1", size=8, is_signed=False)]
    sp = Expression.variable(
        "sp",
        size=8,
        storage_info=StorageInfo(
            is_register=True,
            space_name="register",
            register_name="sp",
            base_register_name="sp",
            size=8,
            size_bits=64,
            base_register_size=8,
            base_register_size_bits=64,
            bit_offset_in_base=0,
        ),
    )
    addr_expr = Expression.binary_op("INT_ADD", sp, Expression.constant(-0x1C, 8))

    location = canonicalize_location(addr_expr, params, size=4)

    assert location == _loc("__locbase__stackframe", -0x1C, 4)


def test_canonicalize_location_accepts_foldable_subpiece_constant_ptradd_index():
    params = [_param("param_1", size=8, is_signed=False)]
    pointer = Expression.parameter("param_1", index=0, size=8)
    masked_one = Expression.binary_op(
        "INT_AND",
        Expression.constant(1, size=8),
        Expression.constant(0xFFFFFFFF, size=8),
    )
    index = Expression.binary_op("SUBPIECE", masked_one, Expression.constant(0, size=4))
    index.size = 4
    address = Expression.intrinsic(
        "PTRADD",
        [pointer, Expression.unary_op("INT_ZEXT", index), Expression.constant(4, size=8)],
        size=8,
    )

    location = canonicalize_location(address, params, size=4)

    assert location == _loc("param_1", 4, 4)


def test_substitute_condition_simplifies_stack_local_nonnull_guard():
    params = [_param("param_1", size=8, is_signed=False)]
    sp = Expression.variable(
        "sp",
        size=8,
        storage_info=StorageInfo(
            is_register=True,
            space_name="register",
            register_name="sp",
            base_register_name="sp",
            size=8,
            size_bits=64,
            base_register_size=8,
            base_register_size_bits=64,
            bit_offset_in_base=0,
        ),
    )
    local_addr = Expression.binary_op("INT_ADD", sp, Expression.constant(-0x1C, 8))
    guard = Condition(
        Expression.binary_op(
            "INT_NOTEQUAL",
            Expression.parameter("out", 1, size=8),
            Expression.constant(0, 8),
        ),
        False,
    )

    substituted = substitute_condition(
        guard,
        _build_parameter_replacements([{"name": "out", "index": 1}], [local_addr]),
        params,
    )

    assert substituted.expression.expr_type.name == "CONSTANT"
    assert substituted.expression.value == 1


def test_effect_summary_rewrites_stack_local_post_state_reads_in_arithmetic_expression():
    a = Expression.parameter("a", 0, size=4)
    b = Expression.parameter("b", 1, size=4)
    sum_slot = Expression.variable(
        "sum_slot",
        size=4,
        storage_info=StorageInfo(**_stack_storage(24, size_bytes=4)),
    )
    diff_slot = Expression.variable(
        "diff_slot",
        size=4,
        storage_info=StorageInfo(**_stack_storage(28, size_bytes=4)),
    )
    sum_location = canonicalize_location(sum_slot, [_param("a", size=4), _param("b", size=4, index=1)], size=4)
    diff_location = canonicalize_location(diff_slot, [_param("a", size=4), _param("b", size=4, index=1)], size=4)
    assert sum_location is not None
    assert diff_location is not None

    expr = Expression.binary_op(
        "INT_ADD",
        Expression.binary_op("INT_MULT", memory_expression_for_location(sum_location, []), Expression.constant(4, 4)),
        memory_expression_for_location(diff_location, []),
    )

    rewritten = rewrite_loads_from_effects(
        expr,
        [],
        [
            StoreEffect(
                location=sum_location,
                value=Expression.binary_op("INT_ADD", a, b),
                conditions=[],
                order_key=1,
            ),
            StoreEffect(
                location=diff_location,
                value=Expression.binary_op("INT_SUB", a, b),
                conditions=[],
                order_key=2,
            ),
        ],
        [_param("a", size=4), _param("b", size=4, index=1)],
    )

    assert rewritten.to_string() == "(((a + b) * 4) + (a - b))"


def test_rewrite_location_read_from_effects_drops_stack_local_nonnull_phi_guard():
    params = [_param("a", size=4), _param("b", size=4, index=1)]
    location = _loc("__locbase__stackframe", -0x1C, 4)
    raw_guard = Condition(
        Expression.binary_op(
            "INT_NOTEQUAL",
            Expression.parameter("out", 2, size=8),
            Expression.constant(0, 8),
        ),
        False,
    )
    cond = substitute_condition(
        raw_guard,
        _build_parameter_replacements(
            [{"name": "out", "index": 2}],
            [
                Expression.binary_op(
                    "INT_ADD",
                    Expression.variable(
                        "sp",
                        size=8,
                        storage_info=StorageInfo(
                            is_register=True,
                            space_name="register",
                            register_name="sp",
                            base_register_name="sp",
                            size=8,
                            size_bits=64,
                            base_register_size=8,
                            base_register_size_bits=64,
                            bit_offset_in_base=0,
                        ),
                    ),
                    Expression.constant(-0x1C, 8),
                ),
            ],
        ),
        params,
    )

    rewritten = rewrite_location_read_from_effects(
        location,
        Expression.constant(0, 4),
        [],
        [
            StoreEffect(
                location=location,
                value=Expression.binary_op(
                    "INT_ADD",
                    Expression.parameter("a", 0, size=4),
                    Expression.parameter("b", 1, size=4),
                ),
                conditions=[cond],
                order_key=1,
            ),
        ],
        params,
    )

    assert rewritten.to_string() == "(a + b)"


def test_return_analyzer_preserves_symbolic_post_state_reads_until_smt_lowering():
    analyzer = ReturnAnalyzer(program=object(), debug=False)
    analyzer._current_parameters = [
        _param("param_1", size=4, is_signed=False, index=0),
        _param("param_2", size=4, is_signed=False, index=1),
    ]
    analyzer._current_effect_summary = EffectSummary(
        parameter_names=["param_1", "param_2"],
        effects=[
            StoreEffect(
                location=_loc("__locbase__stackframe", -32, 4),
                value=Expression.binary_op(
                    "INT_SUB",
                    Expression.parameter("param_1", 0, size=4),
                    Expression.parameter("param_2", 1, size=4),
                ),
                conditions=[],
                order_key=1,
            ),
            StoreEffect(
                location=_loc("__locbase__stackframe", -28, 4),
                value=Expression.binary_op(
                    "INT_ADD",
                    Expression.parameter("param_1", 0, size=4),
                    Expression.parameter("param_2", 1, size=4),
                ),
                conditions=[],
                order_key=2,
            ),
        ],
    )

    expr = Expression.binary_op(
        "INT_ADD",
        memory_expression_for_location(_loc("__locbase__stackframe", -32, 4), []),
        Expression.binary_op(
            "INT_MULT",
            memory_expression_for_location(_loc("__locbase__stackframe", -28, 4), []),
            Expression.constant(4, 4),
        ),
    )

    normalized = analyzer._normalize_expanded_return_value(expr, [])

    assert expression_contains_post_state_reads(normalized)
    assert "__locread__" not in normalized.to_string()

    lowered = lower_post_state_expression_for_smt(
        normalized,
        [],
        analyzer._current_effect_summary.effects,
        analyzer._current_parameters,
    )

    assert lowered.to_string() == "((param_1 - param_2) + ((param_1 + param_2) * 4))"


def test_return_analyzer_promotes_stale_effect_value_wrapper_to_object_centric_post_state():
    dst = Expression.parameter("dst", 0, size=8)
    src = Expression.parameter("src", 1, size=8)
    delta = Expression.parameter("delta", 2, size=4)
    dst_nonnull = Condition(
        Expression.binary_op("INT_NOTEQUAL", dst, Expression.constant(0, 8)),
        False,
    )
    src_nonnull = Condition(
        Expression.binary_op("INT_NOTEQUAL", src, Expression.constant(0, 8)),
        False,
    )
    alias_cond = Condition(
        Expression.binary_op("INT_EQUAL", dst, src),
        False,
    )

    analyzer = ReturnAnalyzer(program=object(), debug=False)
    analyzer._current_parameters = [
        _param("dst", size=8, is_signed=False),
        _param("src", size=8, is_signed=False, index=1),
        _param("delta", size=4, index=2),
    ]
    analyzer._current_effect_summary = EffectSummary(
        parameter_names=["dst", "src", "delta"],
        effects=[
            StoreEffect(
                location=_loc("dst", 0, 4),
                value=Expression.binary_op("INT_ADD", Expression.memory(dst, size=4), delta),
                conditions=[dst_nonnull, src_nonnull],
                order_key=10,
            ),
            StoreEffect(
                location=_loc("src", 0, 4),
                value=Expression.binary_op(
                    "INT_ADD",
                    Expression.memory(src, size=4),
                    Expression.constant(4294967295, 4),
                ),
                conditions=[dst_nonnull, src_nonnull],
                order_key=20,
            ),
        ],
    )

    original = Expression.binary_op(
        "INT_ADD",
        Expression.memory(dst, size=4),
        Expression.constant(0, 4),
    )
    rewritten = Expression.binary_op(
        "INT_ADD",
        Expression.binary_op("INT_ADD", Expression.memory(dst, size=4), delta),
        Expression.constant(0, 4),
    )

    collapsed = analyzer._collapse_effect_sensitive_case_wrapper(
        original,
        rewritten,
        [dst_nonnull, src_nonnull, alias_cond],
        analyzer._current_effect_summary,
    )

    assert collapsed is not None
    assert expression_contains_post_state_reads(collapsed)
    assert collapsed.to_string() == "MEM[dst]"


def test_return_analyzer_keeps_stale_effect_value_wrapper_when_alias_is_not_definite():
    dst = Expression.parameter("dst", 0, size=8)
    src = Expression.parameter("src", 1, size=8)
    delta = Expression.parameter("delta", 2, size=4)
    dst_nonnull = Condition(
        Expression.binary_op("INT_NOTEQUAL", dst, Expression.constant(0, 8)),
        False,
    )
    src_nonnull = Condition(
        Expression.binary_op("INT_NOTEQUAL", src, Expression.constant(0, 8)),
        False,
    )
    alias_cond = Condition(
        Expression.binary_op("INT_EQUAL", dst, src),
        False,
    )

    analyzer = ReturnAnalyzer(program=object(), debug=False)
    analyzer._current_parameters = [
        _param("dst", size=8, is_signed=False),
        _param("src", size=8, is_signed=False, index=1),
        _param("delta", size=4, index=2),
    ]
    analyzer._current_effect_summary = EffectSummary(
        parameter_names=["dst", "src", "delta"],
        effects=[
            StoreEffect(
                location=_loc("dst", 0, 4),
                value=Expression.binary_op("INT_ADD", Expression.memory(dst, size=4), delta),
                conditions=[dst_nonnull, src_nonnull, alias_cond],
                order_key=10,
            ),
            StoreEffect(
                location=_loc("src", 0, 4),
                value=Expression.binary_op(
                    "INT_ADD",
                    Expression.memory(src, size=4),
                    Expression.constant(4294967295, 4),
                ),
                conditions=[dst_nonnull, src_nonnull, alias_cond],
                order_key=20,
            ),
        ],
    )

    original = Expression.binary_op(
        "INT_ADD",
        Expression.memory(dst, size=4),
        Expression.constant(0, 4),
    )
    rewritten = Expression.binary_op(
        "INT_ADD",
        Expression.binary_op("INT_ADD", Expression.memory(dst, size=4), delta),
        Expression.constant(0, 4),
    )

    collapsed = analyzer._collapse_effect_sensitive_case_wrapper(
        original,
        rewritten,
        [dst_nonnull, src_nonnull],
        analyzer._current_effect_summary,
    )

    assert collapsed is not None
    assert not expression_contains_post_state_reads(collapsed)
    assert collapsed.to_string() == "(MEM[dst] + delta)"


def test_return_analyzer_rejects_no_rank_rewrite_that_drops_composite_location_wrapper():
    ptr = Expression.parameter("ptr", 0, size=8)
    delta = Expression.parameter("delta", 1, size=4)
    ptr_nonnull = Condition(
        Expression.binary_op("INT_NOTEQUAL", ptr, Expression.constant(0, 8)),
        False,
    )

    analyzer = ReturnAnalyzer(program=object(), debug=False)
    analyzer._current_parameters = [
        _param("ptr", size=8, is_signed=False, index=0),
        _param("delta", size=4, index=1),
    ]
    analyzer._current_effect_summary = EffectSummary(
        parameter_names=["ptr", "delta"],
        effects=[
            StoreEffect(
                location=_loc("ptr", 0, 4),
                value=Expression.memory(ptr, size=4),
                conditions=[ptr_nonnull],
                order_key=10,
            ),
        ],
    )

    original = Expression.binary_op(
        "INT_SUB",
        Expression.memory(ptr, size=4),
        delta,
    )
    rewritten = Expression.memory(ptr, size=4)

    accepted = analyzer._accept_effect_rewrite_without_rank_gain(
        original,
        rewritten,
        [ptr_nonnull],
        analyzer._current_effect_summary,
    )

    assert accepted is False


def test_return_analyzer_keeps_object_centric_post_state_for_observed_stale_wrapper():
    ptr = Expression.parameter("ptr", 0, size=8)
    alias = Expression.parameter("alias", 1, size=8)
    delta = Expression.parameter("delta", 2, size=4)
    ptr_nonnull = Condition(
        Expression.binary_op("INT_NOTEQUAL", ptr, Expression.constant(0, 8)),
        False,
    )
    alias_nonnull = Condition(
        Expression.binary_op("INT_NOTEQUAL", alias, Expression.constant(0, 8)),
        False,
    )
    alias_cond = Condition(
        Expression.binary_op("INT_EQUAL", ptr, alias),
        False,
    )
    observed = Expression.memory(ptr, size=4, read_order_key=42)
    wrapped = Expression.binary_op(
        "INT_ADD",
        Expression.binary_op("INT_ADD", observed, delta),
        Expression.constant(0, 4),
    )

    analyzer = ReturnAnalyzer(program=object(), debug=False)
    analyzer._current_parameters = [
        _param("ptr", size=8, is_signed=False),
        _param("alias", size=8, is_signed=False, index=1),
        _param("delta", size=4, index=2),
    ]
    analyzer._current_effect_summary = EffectSummary(
        parameter_names=["ptr", "alias", "delta"],
        effects=[
            StoreEffect(
                location=_loc("ptr", 0, 4),
                value=Expression.binary_op("INT_ADD", observed, delta),
                conditions=[ptr_nonnull, alias_nonnull, alias_cond],
                order_key=10,
            ),
        ],
    )

    normalized = analyzer._normalize_expanded_return_value(
        wrapped,
        [ptr_nonnull, alias_nonnull, alias_cond],
    )

    assert normalized is not None
    assert expression_contains_post_state_reads(normalized)
    assert normalized.to_string() == "MEM[ptr]"


def test_find_matching_effect_value_uses_effect_guard_for_location_alias():
    left = Expression.parameter("param_1", 0, size=8)
    right = Expression.parameter("param_2", 1, size=8)
    read_from_right = Expression.memory(right, size=4)
    alias_cond = Condition(
        Expression.binary_op("INT_EQUAL", left, right),
        False,
    )

    match = _find_matching_effect_value(
        read_from_right,
        _loc("param_2", 0, 4),
        [],
        [
            StoreEffect(
                location=_loc("param_1", 0, 4),
                value=read_from_right,
                conditions=[alias_cond],
                order_key=17,
            )
        ],
        [
            _param("param_1", size=8, index=0),
            _param("param_2", size=8, index=1),
        ],
    )

    assert match is not None
    assert match[0] == 17


def test_canonicalize_post_state_subexpressions_does_not_promote_memory_address_parameter():
    param_1 = Expression.parameter("param_1", 0, size=8)
    param_2 = Expression.parameter("param_2", 1, size=8)
    param_3 = Expression.parameter("param_3", 2, size=4)
    nonnull_1 = Condition(
        Expression.binary_op("INT_NOTEQUAL", param_1, Expression.constant(0, 8)),
        False,
    )
    nonnull_2 = Condition(
        Expression.binary_op("INT_NOTEQUAL", param_2, Expression.constant(0, 8)),
        False,
    )
    alias_cond = Condition(
        Expression.binary_op("INT_EQUAL", param_1, param_2),
        False,
    )
    observed_1 = Expression.memory(
        param_1,
        size=4,
        read_order_key=100,
        runtime_ref=ObservedMemoryReadRef(
            order_key=100,
            location=_loc("param_1", 0, 4),
            source="ghidra_load",
        ),
    )
    observed_2 = Expression.memory(
        param_2,
        size=4,
        read_order_key=101,
        runtime_ref=ObservedMemoryReadRef(
            order_key=101,
            location=_loc("param_2", 0, 4),
            source="ghidra_load",
        ),
    )

    normalized = canonicalize_post_state_subexpressions(
        observed_1,
        [nonnull_1, nonnull_2, alias_cond],
        [
            StoreEffect(
                location=_loc("param_1", 0, 4),
                value=Expression.binary_op("INT_ADD", observed_1, param_3),
                conditions=[nonnull_1, nonnull_2],
                order_key=10,
            ),
            StoreEffect(
                location=_loc("param_2", 0, 4),
                value=Expression.binary_op(
                    "INT_ADD",
                    observed_2,
                    Expression.constant(4294967295, 4),
                ),
                conditions=[nonnull_1, nonnull_2],
                order_key=20,
            ),
        ],
        [
            _param("param_1", size=8, is_signed=False),
            _param("param_2", size=8, is_signed=False, index=1),
            _param("param_3", size=4, index=2),
        ],
        symbolic_post_state=True,
        allow_memory_leaf_collapse=False,
    )

    assert normalized is not None
    assert normalized.to_string() == "MEM[param_1]"


def test_normalize_post_state_expression_promotes_observed_alias_wrapper_with_interdependent_effects():
    param_1 = Expression.parameter("param_1", 0, size=8)
    param_2 = Expression.parameter("param_2", 1, size=8)
    param_3 = Expression.parameter("param_3", 2, size=4)
    nonnull_1 = Condition(
        Expression.binary_op("INT_NOTEQUAL", param_1, Expression.constant(0, 8)),
        False,
    )
    nonnull_2 = Condition(
        Expression.binary_op("INT_NOTEQUAL", param_2, Expression.constant(0, 8)),
        False,
    )
    alias_cond = Condition(
        Expression.binary_op("INT_EQUAL", param_1, param_2),
        False,
    )
    observed_1 = Expression.memory(
        param_1,
        size=4,
        read_order_key=100,
        runtime_ref=ObservedMemoryReadRef(
            order_key=100,
            location=_loc("param_1", 0, 4),
            source="ghidra_load",
        ),
    )
    observed_2 = Expression.memory(
        param_2,
        size=4,
        read_order_key=101,
        runtime_ref=ObservedMemoryReadRef(
            order_key=101,
            location=_loc("param_2", 0, 4),
            source="ghidra_load",
        ),
    )
    wrapped = Expression.binary_op(
        "INT_ADD",
        Expression.binary_op("INT_ADD", observed_1, param_3),
        Expression.constant(0, 4),
    )

    normalized = normalize_post_state_expression(
        wrapped,
        [nonnull_1, nonnull_2, alias_cond],
        [
            StoreEffect(
                location=_loc("param_1", 0, 4),
                value=Expression.binary_op("INT_ADD", observed_1, param_3),
                conditions=[nonnull_1, nonnull_2],
                order_key=10,
            ),
            StoreEffect(
                location=_loc("param_2", 0, 4),
                value=Expression.binary_op(
                    "INT_ADD",
                    observed_2,
                    Expression.constant(4294967295, 4),
                ),
                conditions=[nonnull_1, nonnull_2],
                order_key=20,
            ),
        ],
        [
            _param("param_1", size=8, is_signed=False),
            _param("param_2", size=8, is_signed=False, index=1),
            _param("param_3", size=4, index=2),
        ],
        prefer_canonical_post_state=True,
        symbolic_post_state=True,
    )

    assert normalized is not None
    assert expression_contains_post_state_reads(normalized)
    assert normalized.to_string() == "MEM[param_1]"


def test_effect_summary_falls_back_to_pre_state_value_for_unwritten_stack_local_read():
    params = [_param("guard", size=8, is_signed=False)]
    slot_expr = Expression.variable(
        "local_guard",
        size=8,
        storage_info=StorageInfo(**_stack_storage(8, size_bytes=8)),
    )
    location = canonicalize_location(slot_expr, params, size=8)
    assert location is not None
    fallback = Expression.variable("guard_before_call", size=8)

    rewritten = rewrite_location_read_from_effects(
        location,
        fallback,
        [],
        [
            StoreEffect(
                location=_loc("guard", 0, 8),
                value=Expression.constant(1, 8),
                conditions=[],
                order_key=1,
            )
        ],
        params,
    )

    assert rewritten.to_string() == "guard_before_call"


def test_recover_call_argument_from_storage_prefers_exact_register_match_for_pointer_arg():
    class FakeAddress:
        def __init__(self, offset, space_name="register"):
            self._offset = offset
            self._space_name = space_name

        def getOffset(self):
            return self._offset

        def getAddressSpace(self):
            return self

        def getName(self):
            return self._space_name

    class FakeSeqnum:
        def __init__(self, offset, order):
            self._target = FakeAddress(offset, "ram")
            self._order = order

        def getTarget(self):
            return self._target

        def getOrder(self):
            return self._order

    class FakeVarnode:
        def __init__(self, storage, size=8):
            self.storage = storage
            self._size = size

        def getSize(self):
            return self._size

        def getDef(self):
            return None

        def getAddress(self):
            return FakeAddress(self.storage.offset, self.storage.space_name)

        def getOffset(self):
            return self.storage.offset

        def getHigh(self):
            return None

    class FakeOp:
        def __init__(self, output, offset, order):
            self._output = output
            self._seqnum = FakeSeqnum(offset, order)

        def getOutput(self):
            return self._output

        def getMnemonic(self):
            return "COPY"

        def getNumInputs(self):
            return 0

        def getSeqnum(self):
            return self._seqnum

    class FakeTracer:
        def __init__(self, traced_values, ops):
            self._traced_values = traced_values
            self._ops = ops

        def get_all_pcode_ops(self):
            return self._ops

        def _get_storage_info_from_varnode(self, varnode):
            return getattr(varnode, "storage", None)

        def trace_varnode(self, varnode, use_cache=False, depth=0):
            return self._traced_values[varnode]

    partial_output = FakeVarnode(
        StorageInfo(
            is_register=True,
            space_name="register",
            offset=0,
            size=4,
            size_bits=32,
            register_name="a2_lo",
            base_register_name="a2",
            base_register_size=8,
            base_register_size_bits=64,
            bit_offset_in_base=0,
        ),
        size=4,
    )
    exact_output = FakeVarnode(StorageInfo(**_reg_storage("a2")), size=8)
    tracer = FakeTracer(
        {
            partial_output: Expression.parameter("param_1", 0, size=4),
            exact_output: Expression.binary_op(
                "INT_ADD",
                Expression.variable(
                    "sp",
                    size=8,
                    storage_info=StorageInfo(
                        is_register=True,
                        space_name="register",
                        register_name="sp",
                        base_register_name="sp",
                        size=8,
                        size_bits=64,
                        base_register_size=8,
                        base_register_size_bits=64,
                        bit_offset_in_base=0,
                    ),
                ),
                Expression.constant(-0x30, 8),
            ),
        },
        [
            FakeOp(partial_output, 0x1000, 1),
            FakeOp(exact_output, 0x1000, 2),
        ],
    )
    call_op = FakeOp(None, 0x1000, 3)
    call_block = type("FakeBlock", (), {"pcode_ops": tracer.get_all_pcode_ops() + [call_op]})()

    class FakeConditionTracker:
        block_by_index = {0: call_block}

        def get_all_valid_block_paths_to_block(self, _block):
            return [([call_block], [])]

    recovered = _recover_call_argument_from_storage(
        call_op,
        tracer,
        [_param("param_1", size=4, is_signed=False, index=0)],
        {"storage": _reg_storage("a2"), "size": 8},
        condition_tracker=FakeConditionTracker(),
    )

    assert recovered is not None
    assert recovered.to_string() == "(sp + (-48))"


def test_recover_call_argument_from_storage_prefers_pointer_compatible_candidate_over_later_scalar_copy():
    class FakeAddress:
        def __init__(self, offset, space_name="register"):
            self._offset = offset
            self._space_name = space_name

        def getOffset(self):
            return self._offset

        def getAddressSpace(self):
            return self

        def getName(self):
            return self._space_name

    class FakeSeqnum:
        def __init__(self, offset, order):
            self._target = FakeAddress(offset, "ram")
            self._order = order

        def getTarget(self):
            return self._target

        def getOrder(self):
            return self._order

    class FakeVarnode:
        def __init__(self, storage, size=8):
            self.storage = storage
            self._size = size

        def getSize(self):
            return self._size

        def getAddress(self):
            return FakeAddress(self.storage.offset, self.storage.space_name)

        def getOffset(self):
            return self.storage.offset

        def getDef(self):
            return None

        def getHigh(self):
            return None

    class FakeOp:
        def __init__(self, output, offset, order):
            self._output = output
            self._seqnum = FakeSeqnum(offset, order)

        def getOutput(self):
            return self._output

        def getMnemonic(self):
            return "COPY"

        def getNumInputs(self):
            return 0

        def getSeqnum(self):
            return self._seqnum

    class FakeTracer:
        def __init__(self, traced_values, ops):
            self._traced_values = traced_values
            self._ops = ops

        def get_all_pcode_ops(self):
            return self._ops

        def _get_storage_info_from_varnode(self, varnode):
            return getattr(varnode, "storage", None)

        def trace_varnode(self, varnode, use_cache=False, depth=0):
            return self._traced_values[varnode]

    class MockPointerType:
        def isPointer(self):
            return True

    pointer_output = FakeVarnode(StorageInfo(**_reg_storage("a2")), size=8)
    scalar_output = FakeVarnode(StorageInfo(**_reg_storage("a2")), size=8)
    local_addr = Expression.binary_op(
        "INT_ADD",
        Expression.variable(
            "sp",
            size=8,
            storage_info=StorageInfo(
                is_register=True,
                space_name="register",
                register_name="sp",
                base_register_name="sp",
                size=8,
                size_bits=64,
                base_register_size=8,
                base_register_size_bits=64,
                bit_offset_in_base=0,
            ),
        ),
        Expression.constant(-0x30, 8),
    )
    tracer = FakeTracer(
        {
            pointer_output: local_addr,
            scalar_output: Expression.parameter("param_1", 0, size=4),
        },
        [
            FakeOp(pointer_output, 0x1000, 1),
            FakeOp(scalar_output, 0x1000, 2),
        ],
    )
    call_op = FakeOp(None, 0x1000, 3)
    call_block = type("FakeBlock", (), {"pcode_ops": tracer.get_all_pcode_ops() + [call_op]})()

    class FakeConditionTracker:
        block_by_index = {0: call_block}

        def get_all_valid_block_paths_to_block(self, _block):
            return [([call_block], [])]

    recovered = _recover_call_argument_from_storage(
        call_op,
        tracer,
        [_param("param_1", size=4, is_signed=False, index=0, storage=_reg_storage("a0_lo", size_bytes=4, register_name="a0_lo"))],
        {
            "storage": _reg_storage("a2"),
            "size": 8,
            "data_type": "int *",
            "data_type_obj": MockPointerType(),
        },
        condition_tracker=FakeConditionTracker(),
    )

    assert recovered is not None
    assert recovered.to_string() == "(sp + (-48))"


def test_recover_call_argument_from_storage_refuses_no_tracker_global_scan():
    class FakeAddress:
        def __init__(self, offset, space_name="ram"):
            self._offset = offset
            self._space_name = space_name

        def getOffset(self):
            return self._offset

        def getAddressSpace(self):
            return self

        def getName(self):
            return self._space_name

    class FakeSeqnum:
        def __init__(self, offset, order):
            self._target = FakeAddress(offset)
            self._order = order

        def getTarget(self):
            return self._target

        def getOrder(self):
            return self._order

    class FakeVarnode:
        def __init__(self, name, storage, expr):
            self.name = name
            self.storage = storage
            self.expr = expr

        def getDef(self):
            return None

        def getSize(self):
            return 4

    class FakeOp:
        def __init__(self, output, order):
            self._output = output
            self._seqnum = FakeSeqnum(0x1000, order)

        def getMnemonic(self):
            return "CALL" if self._output is None else "COPY"

        def getOutput(self):
            return self._output

        def getNumInputs(self):
            return 0

        def getSeqnum(self):
            return self._seqnum

    class FakeTracer:
        def __init__(self, ops):
            self._ops = list(ops)

        def get_all_pcode_ops(self):
            return self._ops

        def _get_storage_info_from_varnode(self, varnode):
            return getattr(varnode, "storage", None)

        def trace_varnode(self, varnode, use_cache=False, depth=0):
            return getattr(varnode, "expr", None)

    storage = StorageInfo(**_reg_storage("a0", size_bytes=4))
    reaching_output = FakeVarnode(
        "a0_def",
        storage,
        Expression.parameter("param_1", 0, size=4),
    )
    reaching_def = FakeOp(reaching_output, 1)
    call_op = FakeOp(None, 10)

    recovered = _recover_call_argument_from_storage(
        call_op,
        FakeTracer([reaching_def]),
        [_param("param_1", size=4, is_signed=False, index=0, storage=_reg_storage("a0", size_bytes=4))],
        {"name": "x", "index": 0, "size": 4, "storage": _reg_storage("a0", size_bytes=4)},
    )

    assert recovered is None


def test_recover_call_argument_expressions_does_not_fabricate_formal_storage_argument():
    class FakeAddress:
        def __init__(self, offset, space_name="ram"):
            self._offset = offset
            self._space_name = space_name

        def getOffset(self):
            return self._offset

        def getAddressSpace(self):
            return self

        def getName(self):
            return self._space_name

    class FakeSeqnum:
        def getTarget(self):
            return FakeAddress(0x1000)

        def getOrder(self):
            return 1

    class FakeCallOp:
        def getSeqnum(self):
            return FakeSeqnum()

    class FakeTracer:
        def get_all_pcode_ops(self):
            return []

        def _get_storage_info_from_varnode(self, varnode):
            return getattr(varnode, "storage", None)

    args = _recover_call_argument_expressions(
        FakeCallOp(),
        FakeTracer(),
        [_param("caller_value", size=8, is_signed=False, storage=_reg_storage("a0"))],
        [{"name": "callee_value", "index": 0, "size": 8, "storage": _reg_storage("a0")}],
        [],
    )

    assert args == []


def test_recover_call_argument_from_storage_requires_all_compatible_paths():
    class FakeAddress:
        def __init__(self, offset, space_name="ram"):
            self._offset = offset
            self._space_name = space_name

        def getOffset(self):
            return self._offset

        def getAddressSpace(self):
            return self

        def getName(self):
            return self._space_name

    class FakeSeqnum:
        def __init__(self, offset, order):
            self._target = FakeAddress(offset)
            self._order = order

        def getTarget(self):
            return self._target

        def getOrder(self):
            return self._order

    class FakeVarnode:
        def __init__(self, name, storage=None, expr=None, size=4):
            self.name = name
            self.storage = storage
            self.expr = expr
            self._size = size

        def getDef(self):
            return None

        def getSize(self):
            return self._size

    class FakeOp:
        def __init__(self, mnemonic, output, offset, order):
            self._mnemonic = mnemonic
            self._output = output
            self._seqnum = FakeSeqnum(offset, order)

        def getMnemonic(self):
            return self._mnemonic

        def getOutput(self):
            return self._output

        def getNumInputs(self):
            return 0

        def getSeqnum(self):
            return self._seqnum

    class FakeBlock:
        def __init__(self, ops):
            self.pcode_ops = list(ops)

    class FakeConditionTracker:
        def __init__(self, call_block, paths):
            self.block_by_index = {0: call_block}
            self._paths = paths

        def get_all_valid_block_paths_to_block(self, _block):
            return [(path, []) for path in self._paths]

    class FakeTracer:
        def __init__(self, ops):
            self._ops = ops

        def get_all_pcode_ops(self):
            return self._ops

        def _get_storage_info_from_varnode(self, varnode):
            return getattr(varnode, "storage", None)

        def trace_varnode(self, varnode, use_cache=False, depth=0):
            return getattr(varnode, "expr", None) or Expression.variable(varnode.name, size=varnode.getSize())

    storage = StorageInfo(**_reg_storage("a0", size_bytes=4))
    output = FakeVarnode(
        "a0_def",
        storage=storage,
        expr=Expression.parameter("param_1", 0, size=4),
    )
    reaching_def = FakeOp("COPY", output, 0x1000, 1)
    call_op = FakeOp("CALL", None, 0x1000, 10)
    path_with_def = FakeBlock([reaching_def])
    path_without_def = FakeBlock([])
    call_block = FakeBlock([call_op])

    recovered = _recover_call_argument_from_storage(
        call_op,
        FakeTracer([reaching_def]),
        [_param("param_1", size=4, is_signed=False, index=0, storage=_reg_storage("a1", size_bytes=4))],
        {"name": "x", "index": 0, "size": 4, "storage": _reg_storage("a0", size_bytes=4)},
        condition_tracker=FakeConditionTracker(
            call_block,
            [
                [path_with_def, call_block],
                [path_without_def, call_block],
            ],
        ),
    )

    assert recovered is None


def test_recover_call_argument_from_storage_accepts_unmodified_live_in_on_all_paths():
    class FakeAddress:
        def __init__(self, offset, space_name="ram"):
            self._offset = offset
            self._space_name = space_name

        def getOffset(self):
            return self._offset

        def getAddressSpace(self):
            return self

        def getName(self):
            return self._space_name

    class FakeSeqnum:
        def __init__(self, offset, order):
            self._target = FakeAddress(offset)
            self._order = order

        def getTarget(self):
            return self._target

        def getOrder(self):
            return self._order

    class FakeOp:
        def __init__(self, mnemonic, offset, order):
            self._mnemonic = mnemonic
            self._seqnum = FakeSeqnum(offset, order)

        def getMnemonic(self):
            return self._mnemonic

        def getOutput(self):
            return None

        def getNumInputs(self):
            return 0

        def getSeqnum(self):
            return self._seqnum

    class FakeBlock:
        def __init__(self, ops):
            self.pcode_ops = list(ops)

    class FakeConditionTracker:
        def __init__(self, call_block, paths):
            self.block_by_index = {0: call_block}
            self._paths = paths

        def get_all_valid_block_paths_to_block(self, _block):
            return [(path, []) for path in self._paths]

    class FakeTracer:
        def get_all_pcode_ops(self):
            return []

        def _get_storage_info_from_varnode(self, _varnode):
            return None

    call_op = FakeOp("CALL", 0x1000, 10)
    call_block = FakeBlock([call_op])

    recovered = _recover_call_argument_from_storage(
        call_op,
        FakeTracer(),
        [_param("param_1", size=4, is_signed=False, index=0, storage=_reg_storage("a0", size_bytes=4))],
        {"name": "x", "index": 0, "size": 4, "storage": _reg_storage("a0", size_bytes=4)},
        condition_tracker=FakeConditionTracker(
            call_block,
            [
                [FakeBlock([]), call_block],
                [FakeBlock([]), call_block],
            ],
        ),
    )

    assert recovered is not None
    assert recovered.to_string() == "param_1"


def test_recover_call_argument_from_storage_marks_unknown_full_register_live_in_fragment_partial():
    class FakeAddress:
        def __init__(self, offset, space_name="ram"):
            self._offset = offset
            self._space_name = space_name

        def getOffset(self):
            return self._offset

        def getAddressSpace(self):
            return self

        def getName(self):
            return self._space_name

    class FakeSeqnum:
        def __init__(self, offset, order):
            self._target = FakeAddress(offset)
            self._order = order

        def getTarget(self):
            return self._target

        def getOrder(self):
            return self._order

    class FakeOp:
        def __init__(self, mnemonic, offset, order):
            self._mnemonic = mnemonic
            self._seqnum = FakeSeqnum(offset, order)

        def getMnemonic(self):
            return self._mnemonic

        def getOutput(self):
            return None

        def getNumInputs(self):
            return 0

        def getSeqnum(self):
            return self._seqnum

    class FakeBlock:
        def __init__(self, ops):
            self.pcode_ops = list(ops)

    class FakeConditionTracker:
        def __init__(self, call_block, paths):
            self.block_by_index = {0: call_block}
            self._paths = paths

        def get_all_valid_block_paths_to_block(self, _block):
            return [(path, []) for path in self._paths]

    class FakeTracer:
        def get_all_pcode_ops(self):
            return []

        def _get_storage_info_from_varnode(self, _varnode):
            return None

    def reg_storage(
        register_name: str,
        base_name: str,
        *,
        offset: int,
        size_bits: int,
        bit_offset_in_base: int,
    ) -> dict:
        return {
            "is_register": True,
            "space_name": "register",
            "space_id": 0,
            "offset": offset,
            "size": max(1, size_bits // 8),
            "size_bits": size_bits,
            "register_name": register_name,
            "base_register_name": base_name,
            "base_register_offset": 0x30,
            "base_register_size": 8,
            "base_register_size_bits": 64,
            "bit_offset_in_base": bit_offset_in_base,
        }

    call_op = FakeOp("CALL", 0x1000, 10)
    call_block = FakeBlock([call_op])

    recovered = _recover_call_argument_from_storage(
        call_op,
        FakeTracer(),
        [
            _param(
                "param_3",
                size=4,
                is_signed=True,
                index=2,
                storage=reg_storage(
                    "a2_lo",
                    "a2",
                    offset=0x34,
                    size_bits=32,
                    bit_offset_in_base=32,
                ),
            )
        ],
        {
            "name": "callee_b",
            "index": 2,
            "size": 8,
            "storage": reg_storage(
                "a2",
                "a2",
                offset=0x30,
                size_bits=64,
                bit_offset_in_base=0,
            ),
        },
        condition_tracker=FakeConditionTracker(
            call_block,
            [
                [FakeBlock([]), call_block],
                [FakeBlock([]), call_block],
            ],
        ),
    )

    assert recovered is not None
    assert recovered.to_string() == "param_3"
    assert recovered.size == 4
    evidence = getattr(recovered, "call_argument_width_evidence", None)
    assert evidence is not None
    assert evidence.is_partial() is True
    assert evidence.source_bits == 32
    assert evidence.target_bits == 64


def test_partial_live_in_argument_rejects_full_width_callee_return_use():
    arg = Expression.parameter("param_3", 2, size=4).clone_with(
        call_argument_width_evidence=CallArgumentWidthEvidence(
            source_bits=32,
            target_bits=64,
        )
    )
    callee_analysis = FunctionReturnAnalysis(
        function_name="callee",
        entry_point="0x1000",
        parameters=[
            {
                "name": "param_3",
                "index": 2,
                "size": 8,
                "data_type": "undefined8",
                "storage": _reg_storage("a2", size_bytes=8),
            }
        ],
        returns=[
            ReturnInfo(
                address="0x1000",
                value=Expression.parameter("param_3", 2, size=8),
                conditions=[],
                branch_index=0,
            )
        ],
    )

    assert _call_arguments_width_safe_for_callee_analysis(callee_analysis, [arg]) is False


def test_partial_live_in_argument_allows_low_subpiece_callee_return_use():
    arg = Expression.parameter("param_3", 2, size=4).clone_with(
        call_argument_width_evidence=CallArgumentWidthEvidence(
            source_bits=32,
            target_bits=64,
        )
    )
    callee_param = Expression.parameter("param_3", 2, size=8)
    low_piece = Expression.binary_op(
        "SUBPIECE",
        callee_param,
        Expression.constant(0, size=8),
    )
    low_piece.size = 4
    callee_analysis = FunctionReturnAnalysis(
        function_name="callee",
        entry_point="0x1000",
        parameters=[
            {
                "name": "param_3",
                "index": 2,
                "size": 8,
                "data_type": "undefined8",
                "storage": _reg_storage("a2", size_bytes=8),
            }
        ],
        returns=[
            ReturnInfo(
                address="0x1000",
                value=low_piece,
                conditions=[],
                branch_index=0,
            )
        ],
    )

    assert _call_arguments_width_safe_for_callee_analysis(callee_analysis, [arg]) is True


def _summarize_partial_width_effect_call(effect_value: Expression) -> EffectSummary:
    class FakeVarnode:
        def __init__(self, key, size):
            self.key = key
            self._size = size

        def getSize(self):
            return self._size

        def getDef(self):
            return None

    class FakeCallOp:
        def __init__(self):
            self._inputs = [
                FakeVarnode("target", 8),
                FakeVarnode("slot", 8),
                FakeVarnode("arg", 4),
            ]

        def getMnemonic(self):
            return "CALL"

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

        def getSeqnum(self):
            return None

    class FakeBlockInfo:
        def __init__(self, op):
            self.pcode_ops = [op]

    class FakeCoverage:
        status = "complete"
        condition_paths = [[]]

    class FakeConditionTracker:
        def get_path_coverage_to_block(self, _block):
            return FakeCoverage()

    class FakeTracer:
        def resolve_call_target_ref(self, _varnode, **_kwargs):
            return CallTargetRef.from_name("callee")

        def _get_storage_info_from_varnode(self, _varnode):
            return None

        def trace_varnode(self, varnode, use_cache=False):
            if varnode.key == "slot":
                return Expression.parameter("slot", 0, size=8)
            if varnode.key == "arg":
                return Expression.variable("arg_fragment", size=4).clone_with(
                    call_argument_width_evidence=CallArgumentWidthEvidence(
                        source_bits=32,
                        target_bits=64,
                    )
                )
            return Expression.constant(0, max(1, varnode.getSize()))

    def direct_call_summary(_target_ref, _args):
        return EffectSummary(
            parameter_names=["slot", "arg"],
            parameter_refs=[
                LocationBaseRef.parameter("slot", index=0),
                LocationBaseRef.parameter("arg", index=1),
            ],
            effects=[
                StoreEffect(
                    location=_loc("slot", 0, 4),
                    value=effect_value,
                    conditions=[],
                    order_key=1,
                )
            ],
        )

    return summarize_store_effects(
        [FakeBlockInfo(FakeCallOp())],
        FakeTracer(),
        FakeConditionTracker(),
        [
            _param("slot", size=8, index=0, storage=_reg_storage("x0", register_name="x0")),
        ],
        direct_call_summary=direct_call_summary,
        resolve_callee_parameters=lambda _target_ref: [
            _param("slot", size=8, index=0, storage=_reg_storage("x0", register_name="x0")),
            _param("arg", size=8, index=1, storage=_reg_storage("x1", register_name="x1")),
        ],
        debug=False,
    )


def test_partial_live_in_argument_allows_low_subpiece_callee_effect_use():
    callee_arg = Expression.parameter("arg", 1, size=8)
    low_piece = Expression.binary_op(
        "SUBPIECE",
        callee_arg,
        Expression.constant(0, size=8),
    )
    low_piece.size = 4

    summary = _summarize_partial_width_effect_call(low_piece)

    assert summary.has_unsupported_call is False
    assert len(summary.effects) == 1


def test_partial_live_in_argument_rejects_full_width_callee_effect_use():
    summary = _summarize_partial_width_effect_call(
        Expression.parameter("arg", 1, size=8)
    )

    assert summary.effects == []
    assert summary.has_unsupported_call is True


def test_coerce_argument_to_unknown_callee_param_preserves_fragment_width():
    arg = Expression.parameter("param_3", 2, size=4)

    coerced = _coerce_argument_to_callee_parameter(
        arg,
        {
            "name": "callee_b",
            "index": 2,
            "size": 8,
            "data_type": "undefined8",
        },
    )

    assert coerced is not None
    assert coerced.expr_type == ExpressionType.PARAMETER
    assert coerced.size == 4
    assert coerced.to_string() == "param_3"


def test_recover_call_argument_from_storage_refuses_pointer_live_in_from_integer_fragment():
    class FakeAddress:
        def __init__(self, offset, space_name="ram"):
            self._offset = offset
            self._space_name = space_name

        def getOffset(self):
            return self._offset

        def getAddressSpace(self):
            return self

        def getName(self):
            return self._space_name

    class FakeSeqnum:
        def __init__(self, offset, order):
            self._target = FakeAddress(offset)
            self._order = order

        def getTarget(self):
            return self._target

        def getOrder(self):
            return self._order

    class FakeOp:
        def __init__(self, mnemonic, offset, order):
            self._mnemonic = mnemonic
            self._seqnum = FakeSeqnum(offset, order)

        def getMnemonic(self):
            return self._mnemonic

        def getOutput(self):
            return None

        def getNumInputs(self):
            return 0

        def getSeqnum(self):
            return self._seqnum

    class FakeBlock:
        def __init__(self, ops):
            self.pcode_ops = list(ops)

    class FakeConditionTracker:
        def __init__(self, call_block, paths):
            self.block_by_index = {0: call_block}
            self._paths = paths

        def get_all_valid_block_paths_to_block(self, _block):
            return [(path, []) for path in self._paths]

    class FakeTracer:
        def _get_storage_info_from_varnode(self, _varnode):
            return None

    def reg_storage(register_name, base_name, *, offset, size_bits, bit_offset_in_base):
        return {
            "is_register": True,
            "space_name": "register",
            "space_id": 0,
            "offset": offset,
            "size": max(1, size_bits // 8),
            "size_bits": size_bits,
            "register_name": register_name,
            "base_register_name": base_name,
            "base_register_offset": 0x30,
            "base_register_size": 8,
            "base_register_size_bits": 64,
            "bit_offset_in_base": bit_offset_in_base,
        }

    call_op = FakeOp("CALL", 0x1000, 10)
    call_block = FakeBlock([call_op])

    recovered = _recover_call_argument_from_storage(
        call_op,
        FakeTracer(),
        [
            {
                **_param(
                    "param_3",
                    size=4,
                    is_signed=True,
                    index=2,
                    storage=reg_storage("a2_lo", "a2", offset=0x34, size_bits=32, bit_offset_in_base=32),
                ),
                "data_type": "int",
                "data_type_obj": resolve_mock_data_type("int"),
            }
        ],
        {
            "name": "callee_ptr",
            "index": 2,
            "size": 8,
            "data_type": "int *",
            "storage": reg_storage("a2", "a2", offset=0x30, size_bits=64, bit_offset_in_base=0),
        },
        condition_tracker=FakeConditionTracker(
            call_block,
            [
                [FakeBlock([]), call_block],
                [FakeBlock([]), call_block],
            ],
        ),
    )

    assert recovered is None


def test_recover_call_argument_from_storage_accepts_semantic_width_fragment_live_in():
    class FakeAddress:
        def __init__(self, offset, space_name="ram"):
            self._offset = offset
            self._space_name = space_name

        def getOffset(self):
            return self._offset

        def getAddressSpace(self):
            return self

        def getName(self):
            return self._space_name

    class FakeSeqnum:
        def __init__(self, offset, order):
            self._target = FakeAddress(offset)
            self._order = order

        def getTarget(self):
            return self._target

        def getOrder(self):
            return self._order

    class FakeOp:
        def __init__(self, mnemonic, offset, order):
            self._mnemonic = mnemonic
            self._seqnum = FakeSeqnum(offset, order)

        def getMnemonic(self):
            return self._mnemonic

        def getOutput(self):
            return None

        def getNumInputs(self):
            return 0

        def getSeqnum(self):
            return self._seqnum

    class FakeBlock:
        def __init__(self, ops):
            self.pcode_ops = list(ops)

    class FakeConditionTracker:
        def __init__(self, call_block, paths):
            self.block_by_index = {0: call_block}
            self._paths = paths

        def get_all_valid_block_paths_to_block(self, _block):
            return [(path, []) for path in self._paths]

    class FakeTracer:
        def _get_storage_info_from_varnode(self, _varnode):
            return None

    def reg_storage(
        register_name: str,
        base_name: str,
        *,
        offset: int,
        size_bits: int,
        bit_offset_in_base: int,
    ) -> dict:
        return {
            "is_register": True,
            "space_name": "register",
            "space_id": 0,
            "offset": offset,
            "size": max(1, size_bits // 8),
            "size_bits": size_bits,
            "register_name": register_name,
            "base_register_name": base_name,
            "base_register_offset": 0x30,
            "base_register_size": 8,
            "base_register_size_bits": 64,
            "bit_offset_in_base": bit_offset_in_base,
        }

    call_op = FakeOp("CALL", 0x1000, 10)
    call_block = FakeBlock([call_op])
    int_type = resolve_mock_data_type("int")

    recovered = _recover_call_argument_from_storage(
        call_op,
        FakeTracer(),
        [
            {
                **_param(
                    "param_3",
                    size=4,
                    is_signed=True,
                    index=2,
                    storage=reg_storage(
                        "a2_lo",
                        "a2",
                        offset=0x34,
                        size_bits=32,
                        bit_offset_in_base=32,
                    ),
                ),
                "data_type": "int",
                "data_type_obj": int_type,
            }
        ],
        {
            "name": "callee_b",
            "index": 2,
            "size": 8,
            "data_type": "int",
            "data_type_obj": int_type,
            "storage": reg_storage(
                "a2",
                "a2",
                offset=0x30,
                size_bits=64,
                bit_offset_in_base=0,
            ),
        },
        condition_tracker=FakeConditionTracker(
            call_block,
            [
                [FakeBlock([]), call_block],
                [FakeBlock([]), call_block],
            ],
        ),
    )

    assert recovered is not None
    assert recovered.to_string() == "param_3"
    assert recovered.size == 4


def test_recover_call_argument_from_storage_refuses_global_scan_when_cfg_paths_inconclusive():
    class FakeAddress:
        def __init__(self, offset, space_name="ram"):
            self._offset = offset
            self._space_name = space_name

        def getOffset(self):
            return self._offset

        def getAddressSpace(self):
            return self

        def getName(self):
            return self._space_name

    class FakeSeqnum:
        def __init__(self, offset, order):
            self._target = FakeAddress(offset)
            self._order = order

        def getTarget(self):
            return self._target

        def getOrder(self):
            return self._order

    class FakeVarnode:
        def __init__(self, name, storage=None, expr=None, size=4):
            self.name = name
            self.storage = storage
            self.expr = expr
            self._size = size

        def getDef(self):
            return None

        def getSize(self):
            return self._size

    class FakeOp:
        def __init__(self, mnemonic, output, offset, order):
            self._mnemonic = mnemonic
            self._output = output
            self._seqnum = FakeSeqnum(offset, order)

        def getMnemonic(self):
            return self._mnemonic

        def getOutput(self):
            return self._output

        def getNumInputs(self):
            return 0

        def getSeqnum(self):
            return self._seqnum

    class InconclusiveConditionTracker:
        block_by_index = {}

        def get_all_valid_block_paths_to_block(self, _block):
            raise AssertionError("block lookup should fail before path enumeration")

    class FakeTracer:
        def __init__(self, ops):
            self._ops = ops

        def get_all_pcode_ops(self):
            return self._ops

        def _get_storage_info_from_varnode(self, varnode):
            return getattr(varnode, "storage", None)

        def trace_varnode(self, varnode, use_cache=False, depth=0):
            return getattr(varnode, "expr", None) or Expression.variable(varnode.name, size=varnode.getSize())

    storage = StorageInfo(**_reg_storage("a0", size_bytes=4))
    reaching_output = FakeVarnode(
        "a0_def",
        storage=storage,
        expr=Expression.parameter("param_1", 0, size=4),
    )
    reaching_def = FakeOp("COPY", reaching_output, 0x1000, 1)
    call_op = FakeOp("CALL", None, 0x1000, 10)

    recovered = _recover_call_argument_from_storage(
        call_op,
        FakeTracer([reaching_def]),
        [_param("param_1", size=4, is_signed=False, index=0, storage=_reg_storage("a0", size_bytes=4))],
        {"name": "x", "index": 0, "size": 4, "storage": _reg_storage("a0", size_bytes=4)},
        condition_tracker=InconclusiveConditionTracker(),
    )

    assert recovered is None


def test_find_block_info_for_pcode_op_uses_stable_ref_not_object_identity():
    class FakeOp:
        def __init__(self, ref):
            self.ref = ref

    class FakeBlock:
        def __init__(self, ops):
            self.pcode_ops = list(ops)

    class FakeTracer:
        def _make_pcode_op_ref(self, op):
            return op.ref

    class FakeConditionTracker:
        def __init__(self, block):
            self.tracer = FakeTracer()
            self.block_by_index = {0: block}

    ref = PcodeOpRef(
        address_offset=0x1000,
        seq_time=7,
        seq_order=0,
        block_index=3,
        mnemonic="CALL",
        input_sizes=(8,),
        output_size=4,
    )
    block_op = FakeOp(ref)
    query_op = FakeOp(ref)
    block = FakeBlock([block_op])

    assert _find_block_info_for_pcode_op(FakeConditionTracker(block), query_op) is block


def test_recover_call_argument_from_storage_rejects_conflicting_path_args():
    class FakeAddress:
        def __init__(self, offset, space_name="ram"):
            self._offset = offset
            self._space_name = space_name

        def getOffset(self):
            return self._offset

        def getAddressSpace(self):
            return self

        def getName(self):
            return self._space_name

    class FakeSeqnum:
        def __init__(self, offset, order):
            self._target = FakeAddress(offset)
            self._order = order

        def getTarget(self):
            return self._target

        def getOrder(self):
            return self._order

    class FakeVarnode:
        def __init__(self, name, storage=None, expr=None, size=4):
            self.name = name
            self.storage = storage
            self.expr = expr
            self._size = size

        def getDef(self):
            return None

        def getSize(self):
            return self._size

    class FakeOp:
        def __init__(self, mnemonic, output, offset, order):
            self._mnemonic = mnemonic
            self._output = output
            self._seqnum = FakeSeqnum(offset, order)

        def getMnemonic(self):
            return self._mnemonic

        def getOutput(self):
            return self._output

        def getNumInputs(self):
            return 0

        def getSeqnum(self):
            return self._seqnum

    class FakeBlock:
        def __init__(self, ops):
            self.pcode_ops = list(ops)

    class FakeConditionTracker:
        def __init__(self, call_block, paths):
            self.block_by_index = {0: call_block}
            self._paths = paths

        def get_all_valid_block_paths_to_block(self, _block):
            return [(path, []) for path in self._paths]

    class FakeTracer:
        def __init__(self, ops):
            self._ops = ops

        def get_all_pcode_ops(self):
            return self._ops

        def _get_storage_info_from_varnode(self, varnode):
            return getattr(varnode, "storage", None)

        def trace_varnode(self, varnode, use_cache=False, depth=0):
            return getattr(varnode, "expr", None) or Expression.variable(varnode.name, size=varnode.getSize())

    storage = StorageInfo(**_reg_storage("a0", size_bytes=4))
    out_a = FakeVarnode("a0_a", storage=storage, expr=Expression.parameter("param_1", 0, size=4))
    out_b = FakeVarnode("a0_b", storage=storage, expr=Expression.parameter("param_2", 1, size=4))
    def_a = FakeOp("COPY", out_a, 0x1000, 1)
    def_b = FakeOp("COPY", out_b, 0x1000, 2)
    call_op = FakeOp("CALL", None, 0x1000, 10)
    call_block = FakeBlock([call_op])

    recovered = _recover_call_argument_from_storage(
        call_op,
        FakeTracer([def_a, def_b]),
        [
            _param("param_1", size=4, is_signed=False, index=0, storage=_reg_storage("a0", size_bytes=4)),
            _param("param_2", size=4, is_signed=False, index=1, storage=_reg_storage("a1", size_bytes=4)),
        ],
        {"name": "x", "index": 0, "size": 4, "storage": _reg_storage("a0", size_bytes=4)},
        condition_tracker=FakeConditionTracker(
            call_block,
            [
                [FakeBlock([def_a]), call_block],
                [FakeBlock([def_b]), call_block],
            ],
        ),
    )

    assert recovered is None


def test_incomplete_call_argument_evidence_is_not_applied_to_deferred_call():
    pcode_ref = PcodeOpRef(address_offset=0x1000, seq_time=1, seq_order=0, mnemonic="CALL")
    deferred = DeferredCallInfo(
        placeholder_name="call_out_of_scope:callee#0",
        target_ref=CallTargetRef.from_name("callee"),
        deferred_call_ref=DeferredCallRef(
            pcode_op_ref=pcode_ref,
            target_ref=CallTargetRef.from_name("callee"),
            sequence=0,
        ),
    )
    analysis = FunctionReturnAnalysis(
        function_name="caller",
        entry_point="0x1000",
        returns=[],
        parameters=[{"name": "param_1", "index": 0, "size": 4}],
    )
    analysis.deferred_calls = {deferred.deferred_call_ref.stable_key(): deferred}
    analysis.effect_summary = EffectSummary(
        parameter_names=["param_1"],
        effects=[],
        call_argument_evidence={
            pcode_ref.stable_key(): CallArgumentEvidence(
                pcode_op_ref=pcode_ref,
                target_ref=CallTargetRef.from_name("callee"),
                callee_param_identities=(("parameter", 0),),
                arguments=(),
                sources=(),
                path_conditions=((),),
                coverage_complete=False,
                reason="argument_recovery_incomplete",
            )
        },
    )

    ReturnAnalyzer(program=None, debug=False)._apply_effect_call_argument_evidence_to_deferred_calls(analysis)

    assert deferred.arguments == []
    assert deferred.call_argument_recovery_status == CallArgumentEvidence.RECOVERY_INCONCLUSIVE
    assert deferred.call_argument_recovery_reason == "argument_recovery_incomplete"
    assert "effect_call_argument_evidence_incomplete" in analysis.analysis_notes


def test_recoverable_partial_call_argument_evidence_does_not_become_incomplete_blocker():
    pcode_ref = PcodeOpRef(address_offset=0x1008, seq_time=1, seq_order=0, mnemonic="CALL")
    deferred = DeferredCallInfo(
        placeholder_name="call_out_of_scope:callee#0",
        target_ref=CallTargetRef.from_name("callee"),
        arguments=[Expression.parameter("existing_arg", 0, size=4)],
        deferred_call_ref=DeferredCallRef(
            pcode_op_ref=pcode_ref,
            target_ref=CallTargetRef.from_name("callee"),
            sequence=0,
        ),
    )
    analysis = FunctionReturnAnalysis(
        function_name="caller",
        entry_point="0x1000",
        returns=[],
        parameters=[{"name": "param_1", "index": 0, "size": 4}],
    )
    analysis.deferred_calls = {deferred.deferred_call_ref.stable_key(): deferred}
    analysis.effect_summary = EffectSummary(
        parameter_names=["param_1"],
        effects=[],
        call_argument_evidence={
            pcode_ref.stable_key(): CallArgumentEvidence(
                pcode_op_ref=pcode_ref,
                target_ref=CallTargetRef.from_name("callee"),
                callee_param_identities=(("parameter", 0), ("parameter", 1)),
                arguments=(Expression.parameter("param_1", 0, size=4),),
                sources=("explicit_input",),
                path_conditions=((),),
                coverage_complete=False,
                recovery_status=CallArgumentEvidence.RECOVERY_RECOVERABLE_PARTIAL,
                reason="argument_recovery_recoverable_partial",
            )
        },
    )

    ReturnAnalyzer(program=None, debug=False)._apply_effect_call_argument_evidence_to_deferred_calls(analysis)

    assert len(deferred.arguments) == 1
    assert deferred.arguments[0].to_dict() == Expression.parameter("existing_arg", 0, size=4).to_dict()
    assert deferred.call_argument_recovery_status == CallArgumentEvidence.RECOVERY_RECOVERABLE_PARTIAL
    assert deferred.call_argument_recovery_reason == "argument_recovery_recoverable_partial"
    assert "effect_call_argument_evidence_incomplete" not in analysis.analysis_notes
    assert "effect_call_argument_evidence" not in analysis.analysis_notes


def test_inconclusive_call_argument_evidence_marks_existing_recovered_args_inconclusive():
    pcode_ref = PcodeOpRef(address_offset=0x1011, seq_time=1, seq_order=1, mnemonic="CALL")
    deferred = DeferredCallInfo(
        placeholder_name="call_out_of_scope:callee#0",
        target_ref=CallTargetRef.from_name("callee"),
        arguments=[Expression.parameter("param_1", 0, size=4)],
        deferred_call_ref=DeferredCallRef(
            pcode_op_ref=pcode_ref,
            target_ref=CallTargetRef.from_name("callee"),
            sequence=0,
        ),
        call_argument_recovery_status=CallArgumentEvidence.RECOVERY_COMPLETE,
    )
    analysis = FunctionReturnAnalysis(
        function_name="caller",
        entry_point="0x1000",
        returns=[],
        parameters=[{"name": "param_1", "index": 0, "size": 4}],
    )
    analysis.deferred_calls = {deferred.deferred_call_ref.stable_key(): deferred}
    analysis.effect_summary = EffectSummary(
        parameter_names=["param_1"],
        effects=[],
        call_argument_evidence={
            pcode_ref.stable_key(): CallArgumentEvidence(
                pcode_op_ref=pcode_ref,
                target_ref=CallTargetRef.from_name("callee"),
                callee_param_identities=(("parameter", 0),),
                arguments=(),
                sources=(),
                path_conditions=((),),
                coverage_complete=False,
                reason="argument_recovery_incomplete",
            )
        },
    )

    ReturnAnalyzer(program=None, debug=False)._apply_effect_call_argument_evidence_to_deferred_calls(analysis)

    assert len(deferred.arguments) == 1
    assert deferred.arguments[0].to_dict() == Expression.parameter("param_1", 0, size=4).to_dict()
    assert deferred.call_argument_recovery_status == CallArgumentEvidence.RECOVERY_INCONCLUSIVE
    assert deferred.call_argument_recovery_reason == "argument_recovery_incomplete"
    assert "effect_call_argument_evidence_incomplete" in analysis.analysis_notes


def test_complete_call_argument_evidence_is_applied_to_deferred_call_and_marked_complete():
    pcode_ref = PcodeOpRef(address_offset=0x1018, seq_time=1, seq_order=0, mnemonic="CALL")
    deferred = DeferredCallInfo(
        placeholder_name="call_out_of_scope:callee#0",
        target_ref=CallTargetRef.from_name("callee"),
        deferred_call_ref=DeferredCallRef(
            pcode_op_ref=pcode_ref,
            target_ref=CallTargetRef.from_name("callee"),
            sequence=0,
        ),
    )
    analysis = FunctionReturnAnalysis(
        function_name="caller",
        entry_point="0x1000",
        returns=[],
        parameters=[{"name": "param_1", "index": 0, "size": 4}],
    )
    analysis.deferred_calls = {deferred.deferred_call_ref.stable_key(): deferred}
    analysis.effect_summary = EffectSummary(
        parameter_names=["param_1"],
        effects=[],
        call_argument_evidence={
            pcode_ref.stable_key(): CallArgumentEvidence(
                pcode_op_ref=pcode_ref,
                target_ref=CallTargetRef.from_name("callee"),
                callee_param_identities=(("parameter", 0),),
                arguments=(Expression.parameter("param_1", 0, size=4),),
                sources=("explicit_input",),
                path_conditions=((),),
                coverage_complete=True,
            )
        },
    )

    ReturnAnalyzer(program=None, debug=False)._apply_effect_call_argument_evidence_to_deferred_calls(analysis)

    assert len(deferred.arguments) == 1
    assert deferred.arguments[0].to_dict() == Expression.parameter("param_1", 0, size=4).to_dict()
    assert deferred.call_argument_recovery_status == CallArgumentEvidence.RECOVERY_COMPLETE
    assert deferred.call_argument_recovery_reason is None
    assert "effect_call_argument_evidence" in analysis.analysis_notes
    assert "effect_call_argument_evidence_incomplete" not in analysis.analysis_notes


def test_deferred_call_default_recovery_status_is_inconclusive_without_proof():
    deferred_with_args = DeferredCallInfo(
        placeholder_name="call_out_of_scope:callee#0",
        target_ref=CallTargetRef.from_name("callee"),
        arguments=[Expression.parameter("param_1", 0, size=4)],
    )
    assert deferred_with_args.call_argument_recovery_status == CallArgumentEvidence.RECOVERY_INCONCLUSIVE

    deferred_without_args = DeferredCallInfo(
        placeholder_name="call_out_of_scope:callee#1",
        target_ref=CallTargetRef.from_name("callee"),
        arguments=[],
    )
    assert deferred_without_args.call_argument_recovery_status == CallArgumentEvidence.RECOVERY_INCONCLUSIVE

    deferred_unknown_args = DeferredCallInfo(
        placeholder_name="call_out_of_scope:callee#2",
        target_ref=CallTargetRef.from_name("callee"),
    )
    assert deferred_unknown_args.call_argument_recovery_status == CallArgumentEvidence.RECOVERY_INCONCLUSIVE


def test_recoverable_partial_call_argument_evidence_state_is_not_decisive():
    pcode_ref = PcodeOpRef(address_offset=0x1010, seq_time=1, seq_order=0, mnemonic="CALL")
    deferred = DeferredCallInfo(
        placeholder_name="call_out_of_scope:callee#0",
        target_ref=CallTargetRef.from_name("callee"),
        deferred_call_ref=DeferredCallRef(
            pcode_op_ref=pcode_ref,
            target_ref=CallTargetRef.from_name("callee"),
            sequence=0,
        ),
    )
    analysis = FunctionReturnAnalysis(
        function_name="caller",
        entry_point="0x1000",
        returns=[],
        parameters=[{"name": "param_1", "index": 0, "size": 4}],
    )
    analysis.deferred_calls = {deferred.deferred_call_ref.stable_key(): deferred}
    analysis.effect_summary = EffectSummary(
        parameter_names=["param_1"],
        effects=[],
        call_argument_evidence={
            pcode_ref.stable_key(): CallArgumentEvidence(
                pcode_op_ref=pcode_ref,
                target_ref=CallTargetRef.from_name("callee"),
                callee_param_identities=(("parameter", 0), ("parameter", 1)),
                arguments=(Expression.parameter("param_1", 0, size=4),),
                sources=("explicit_input",),
                path_conditions=((),),
                coverage_complete=False,
                recovery_status=CallArgumentEvidence.RECOVERY_RECOVERABLE_PARTIAL,
                reason="argument_recovery_recoverable_partial",
            )
        },
    )

    ReturnAnalyzer(program=None, debug=False)._apply_effect_call_argument_evidence_to_deferred_calls(analysis)

    assert "effect_call_argument_evidence_incomplete" not in analysis.get_decisive_sat_unsafety_reasons()
    assert deferred.call_argument_recovery_status == CallArgumentEvidence.RECOVERY_RECOVERABLE_PARTIAL
    assert deferred.call_argument_recovery_reason == "argument_recovery_recoverable_partial"


def test_call_argument_recovery_state_survives_specialize_and_merge_deferred_call_flow():
    analyzer = ReturnAnalyzer(program=None, debug=False)
    deferred = DeferredCallInfo(
        placeholder_name="call_out_of_scope:callee#0",
        target_ref=CallTargetRef.from_name("callee"),
        arguments=[Expression.parameter("param_1", 0, size=4)],
        call_argument_recovery_status=CallArgumentEvidence.RECOVERY_RECOVERABLE_PARTIAL,
        call_argument_recovery_reason="argument_recovery_recoverable_partial",
    )
    analysis = FunctionReturnAnalysis(
        function_name="callee",
        entry_point="0x2000",
        parameters=[{"name": "param_1", "index": 0, "size": 4}],
        returns=[],
    )
    analysis.deferred_calls = {deferred.deferred_call_ref.stable_key(): deferred}

    specialized = analyzer._specialize_call_analysis(
        analysis,
        [Expression.parameter("specialized_param_1", 0, size=4)],
    )
    specialized_deferred = next(iter(specialized.deferred_calls.values()))
    assert specialized_deferred.call_argument_recovery_status == CallArgumentEvidence.RECOVERY_RECOVERABLE_PARTIAL
    assert (
        specialized_deferred.call_argument_recovery_reason
        == "argument_recovery_recoverable_partial"
    )

    analyzer._current_deferred_calls = {}
    analyzer._merge_deferred_calls_into_current_analysis(specialized.deferred_calls)
    merged = next(iter(analyzer._current_deferred_calls.values()))
    assert merged.call_argument_recovery_status == CallArgumentEvidence.RECOVERY_RECOVERABLE_PARTIAL
    assert merged.call_argument_recovery_reason == "argument_recovery_recoverable_partial"


def test_merge_deferred_calls_into_current_analysis_preserves_most_conservative_state():
    analyzer = ReturnAnalyzer(program=None, debug=False)
    pcode_ref = PcodeOpRef(address_offset=0x2020, seq_time=1, seq_order=0, mnemonic="CALL")
    deferred_ref = DeferredCallRef(
        pcode_op_ref=pcode_ref,
        target_ref=CallTargetRef.from_name("callee"),
        sequence=0,
    )
    analyzer._current_deferred_calls = {
        deferred_ref.stable_key(): DeferredCallInfo(
            placeholder_name="call_out_of_scope:callee#0",
            target_ref=CallTargetRef.from_name("callee"),
            arguments=[Expression.parameter("known", 0, size=4)],
            deferred_call_ref=deferred_ref,
            call_argument_recovery_status=CallArgumentEvidence.RECOVERY_COMPLETE,
        )
    }
    analyzer._merge_deferred_calls_into_current_analysis(
        {
            deferred_ref.stable_key(): DeferredCallInfo(
                placeholder_name="call_out_of_scope:callee#0",
                target_ref=CallTargetRef.from_name("callee"),
                arguments=[],
                deferred_call_ref=deferred_ref,
                call_argument_recovery_status=CallArgumentEvidence.RECOVERY_INCONCLUSIVE,
                call_argument_recovery_reason="argument_recovery_inconclusive",
            )
        }
    )

    merged = next(iter(analyzer._current_deferred_calls.values()))
    assert merged.call_argument_recovery_status == CallArgumentEvidence.RECOVERY_INCONCLUSIVE
    assert merged.call_argument_recovery_reason == "argument_recovery_inconclusive"


def test_tri_state_call_argument_evidence_merge_preserves_usable_evidence():
    pcode_ref = PcodeOpRef(address_offset=0x1010, seq_time=2, seq_order=0, mnemonic="CALL")
    arg0 = Expression.parameter("param_1", 0, size=4)
    arg1 = Expression.parameter("param_2", 1, size=4)
    complete = CallArgumentEvidence(
        pcode_op_ref=pcode_ref,
        target_ref=CallTargetRef.from_name("callee"),
        callee_param_identities=(("parameter", 0), ("parameter", 1)),
        arguments=(arg0, arg1),
        sources=("explicit_input", "explicit_input"),
        path_conditions=((),),
        coverage_complete=True,
    )
    recoverable_partial = CallArgumentEvidence(
        pcode_op_ref=pcode_ref,
        target_ref=CallTargetRef.from_name("callee"),
        callee_param_identities=(("parameter", 0), ("parameter", 1)),
        arguments=(arg0,),
        sources=("explicit_input",),
        path_conditions=((),),
        coverage_complete=False,
        recovery_status=CallArgumentEvidence.RECOVERY_RECOVERABLE_PARTIAL,
        reason="argument_recovery_recoverable_partial",
    )

    merged = _merge_call_argument_evidence(complete, recoverable_partial)
    reverse_merged = _merge_call_argument_evidence(recoverable_partial, complete)

    assert merged.is_usable() is True
    assert merged.recovery_status == CallArgumentEvidence.RECOVERY_COMPLETE
    assert merged.arguments == (arg0, arg1)
    assert len(merged.path_conditions) == 2
    assert reverse_merged.is_usable() is True
    assert reverse_merged.arguments == (arg0, arg1)


def test_zero_argument_call_evidence_is_usable_for_true_no_arg_callee():
    class FakeTracer:
        def __init__(self, ref):
            self.ref = ref

        def _make_pcode_op_ref(self, _op):
            return self.ref

    pcode_ref = PcodeOpRef(address_offset=0x1100, seq_time=2, seq_order=0, mnemonic="CALL")
    evidence_map = {}

    _record_call_argument_evidence(
        evidence_map,
        FakeTracer(pcode_ref),
        object(),
        CallTargetRef.from_name("callee"),
        [],
        [],
        [],
        coverage_complete=True,
    )

    evidence = evidence_map[pcode_ref.stable_key()]
    assert evidence.is_usable() is True
    assert evidence.coverage_complete is True
    assert evidence.arguments == ()


def test_callee_parameter_ref_refuses_positional_identity_without_index_or_storage():
    assert _coerce_callee_parameter_ref({"name": "param_1"}, 0) is None
    assert _coerce_callee_parameter_ref("param_1", 0) is None

    explicit = _coerce_callee_parameter_ref({"name": "param_1", "index": 0}, 7)
    assert explicit is not None
    assert explicit.parameter_index == 0

    storage_only = _coerce_callee_parameter_ref(
        {"name": "param_1", "storage": _reg_storage("a0", size_bytes=8)},
        7,
    )
    assert storage_only is not None
    assert storage_only.is_storage()
    assert storage_only.storage_identity_key[0] == "register_storage"


def test_build_parameter_replacements_refuses_name_or_string_only_callee_params():
    arg = Expression.parameter("arg_1", 0, size=4)

    assert _build_parameter_replacements([{"name": "param_1"}], [arg]) == {}
    assert _build_parameter_replacements(["param_1"], [arg]) == {}


def test_build_parameter_replacements_accepts_storage_only_callee_identity():
    arg = Expression.parameter("arg_1", 0, size=4)
    replacements = _build_parameter_replacements(
        [
            {
                "name": "param_1",
                "size": 4,
                "storage": _reg_storage("a0", size_bytes=4),
            }
        ],
        [arg],
    )

    assert any(key and key[0] == "register_storage" for key in replacements)


def test_call_evidence_callee_param_identities_reject_unproven_ordinals():
    assert _call_evidence_callee_param_identities([{"name": "param_1"}]) == ()

    storage_identity = _call_evidence_callee_param_identities(
        [{"name": "param_1", "storage": _reg_storage("a0", size_bytes=8)}]
    )
    assert len(storage_identity) == 1
    assert storage_identity[0][0][0] == "register_storage"


def test_unresolved_target_call_argument_evidence_is_not_usable():
    class FakeTracer:
        def __init__(self, ref):
            self.ref = ref

        def _make_pcode_op_ref(self, _op):
            return self.ref

    pcode_ref = PcodeOpRef(address_offset=0x1200, seq_time=3, seq_order=0, mnemonic="CALL")
    evidence_map = {}

    _record_call_argument_evidence(
        evidence_map,
        FakeTracer(pcode_ref),
        object(),
        CallTargetRef.unknown(),
        [{"name": "param_1", "index": 0}],
        [Expression.parameter("param_1", 0, size=4)],
        [],
        coverage_complete=True,
    )

    evidence = evidence_map[pcode_ref.stable_key()]
    assert evidence.is_usable() is False
    assert evidence.coverage_complete is False
    assert evidence.arguments == ()
    assert evidence.reason == "call_target_unresolved"


def test_call_argument_evidence_target_match_requires_resolved_targets():
    evidence = CallArgumentEvidence(
        pcode_op_ref=PcodeOpRef(address_offset=0x1220, seq_time=5, seq_order=0, mnemonic="CALL"),
        target_ref=None,
        callee_param_identities=((("parameter", 0),),),
        arguments=(Expression.parameter("param_1", 0, size=4),),
        sources=("explicit_input",),
        coverage_complete=True,
    )

    assert evidence.is_usable() is False
    assert evidence.target_matches(CallTargetRef.from_name("callee")) is False


def test_storage_location_base_matches_descriptor_storage_identity_key():
    register_base = LocationBaseRef.storage(
        space_id=0,
        space_name="register",
        offset=0x1234,
        size=8,
        display_hint="a0",
    )
    assert _parameter_base_ref_matches_descriptor(
        register_base,
        {
            "name": "arg",
            "storage": {
                "is_register": True,
                "space_name": "register",
                "space_id": 0,
                "offset": 0x1234,
                "size": 8,
                "size_bits": 64,
                "register_offset": 0x1234,
                "register_size": 8,
                "register_size_bits": 64,
                "base_register_offset": 0x1234,
                "base_register_size": 8,
                "base_register_size_bits": 64,
                "bit_offset_in_base": 0,
            },
        },
    )

    memory_base = LocationBaseRef.storage(
        space_id=1,
        space_name="stack",
        offset=0x30,
        size=4,
        display_hint="stack[0x30]",
    )
    assert _parameter_base_ref_matches_descriptor(
        memory_base,
        {"name": "stack_arg", "storage": _stack_storage(0x30, size_bytes=4)},
    )

    fragment_storage = StorageInfo(
        is_register=True,
        space_name="register",
        space_id=0,
        offset=0x200,
        size=4,
        size_bits=32,
        register_offset=0x200,
        register_size=4,
        register_size_bits=32,
        base_register_offset=0x200,
        base_register_size=8,
        base_register_size_bits=64,
        bit_offset_in_base=32,
    )
    fragment_base = LocationBaseRef.storage(
        space_id=0,
        space_name="register",
        offset=0x200,
        size=8,
        storage_identity_key=fragment_storage.storage_identity_key(),
        display_hint="a0_hi",
    )
    assert _parameter_base_ref_matches_descriptor(
        fragment_base,
        {"name": "a0_hi", "storage": fragment_storage},
    )
    coarse_base = LocationBaseRef.storage(
        space_id=0,
        space_name="register",
        offset=0x200,
        size=8,
        display_hint="a0",
    )
    assert fragment_base != coarse_base


def test_missing_callee_parameter_identity_keeps_call_evidence_incomplete():
    class FakeTracer:
        def __init__(self, ref):
            self.ref = ref

        def _make_pcode_op_ref(self, _op):
            return self.ref

    pcode_ref = PcodeOpRef(address_offset=0x1210, seq_time=4, seq_order=0, mnemonic="CALL")
    evidence_map = {}

    _record_call_argument_evidence(
        evidence_map,
        FakeTracer(pcode_ref),
        object(),
        CallTargetRef.from_name("callee"),
        [{"name": "param_1"}],
        [Expression.parameter("param_1", 0, size=4)],
        [],
        coverage_complete=True,
    )

    evidence = evidence_map[pcode_ref.stable_key()]
    assert evidence.is_usable() is False
    assert evidence.coverage_complete is False
    assert evidence.arguments == ()
    assert evidence.reason == "callee_parameter_identity_unproven"


def test_effect_summary_does_not_synthesize_parameter_refs_from_names():
    summary = EffectSummary(parameter_names=["param_1"], effects=[])
    assert summary.parameter_refs == []


def test_storage_matches_parameter_rejects_superset_register_alias():
    expr_storage = StorageInfo(**_reg_storage("a0", size_bytes=8, register_name="a0"))
    param_storage = StorageInfo(
        is_register=True,
        space_name="register",
        offset=36,
        size=4,
        size_bits=32,
        register_name="a0_lo",
        base_register_name="a0",
        base_register_offset=0,
        base_register_size=8,
        base_register_size_bits=64,
        bit_offset_in_base=32,
    )

    assert _storage_matches_parameter(expr_storage, param_storage) is False
    assert _storage_matches_parameter(param_storage, param_storage) is True


def test_resolve_parameter_name_rejects_full_register_when_only_fragment_param_exists():
    params = [
        _param(
            "param_1",
            size=4,
            is_signed=False,
            index=0,
            storage={
                **_reg_storage("a0", size_bytes=4, register_name="a0_lo"),
                "offset": 36,
                "bit_offset_in_base": 32,
                "base_register_size": 8,
                "base_register_size_bits": 64,
            },
        )
    ]

    full_reg_expr = Expression.variable(
        "a0",
        size=8,
        storage_info=StorageInfo(**_reg_storage("a0", size_bytes=8, register_name="a0")),
    )
    fragment_expr = Expression.variable(
        "a0_lo",
        size=4,
        storage_info=StorageInfo(
            is_register=True,
            space_name="register",
            offset=36,
            size=4,
            size_bits=32,
            register_name="a0_lo",
            base_register_name="a0",
            base_register_offset=0,
            base_register_size=8,
            base_register_size_bits=64,
            bit_offset_in_base=32,
        ),
    )

    assert _resolve_parameter_name(full_reg_expr, params) is None
    assert _resolve_parameter_name(fragment_expr, params) == "param_1"


def test_resolve_parameter_name_prefers_index_and_storage_over_stale_name():
    params = [
        _param(
            "param_1",
            size=8,
            is_signed=False,
            index=0,
            storage=_reg_storage("a0", size_bytes=8, register_name="a0"),
        ),
        _param(
            "param_2",
            size=8,
            is_signed=False,
            index=1,
            storage=_reg_storage("a1", size_bytes=8, register_name="a1"),
        ),
    ]

    expr = Expression.parameter(
        "stale_name",
        index=1,
        size=8,
        storage_info=StorageInfo(**_reg_storage("a1", size_bytes=8, register_name="a1")),
    )

    assert _resolve_parameter_name(expr, params) == "param_2"


def test_expression_expander_infers_stack_location_for_indirect_output_without_tracer_storage():
    class FakeAddress:
        def __init__(self, offset, space_name="stack"):
            self._offset = offset
            self._space_name = space_name

        def getOffset(self):
            return self._offset

        def getAddressSpace(self):
            return self

        def getName(self):
            return self._space_name

    class FakeVarnode:
        def getAddress(self):
            return FakeAddress(-0x30, "stack")

        def getOffset(self):
            return -0x30

        def getSize(self):
            return 4

        def getHigh(self):
            return None

    class FakeTracer:
        def __init__(self):
            self.program = object()

        def _get_storage_info_from_varnode(self, _varnode):
            return None

    expander = ExpressionExpander(
        tracer=FakeTracer(),
        condition_tracker=None,
        debug=False,
        effect_summary=EffectSummary(parameter_names=["param_1"], effects=[]),
        parameters=[_param("param_1", size=4, is_signed=False, index=0)],
    )

    location = expander._infer_indirect_output_location(FakeVarnode(), 4)

    assert location == _loc("__locbase__stackframe", -0x30, 4)


def test_recover_call_argument_expressions_prefers_explicit_stack_local_address_over_storage_guess():
    class FakeAddress:
        def __init__(self, offset, space_name="register"):
            self._offset = offset
            self._space_name = space_name

        def getOffset(self):
            return self._offset

        def getAddressSpace(self):
            return self

        def getName(self):
            return self._space_name

    class FakeSeqnum:
        def __init__(self, offset, order):
            self._target = FakeAddress(offset, "ram")
            self._order = order

        def getTarget(self):
            return self._target

        def getOrder(self):
            return self._order

    class FakeVarnode:
        def __init__(self, storage=None, size=8):
            self.storage = storage
            self._size = size

        def getSize(self):
            return self._size

        def getAddress(self):
            if self.storage is None:
                return None
            return FakeAddress(self.storage.offset, self.storage.space_name)

        def getOffset(self):
            return 0 if self.storage is None else self.storage.offset

        def getDef(self):
            return None

        def getHigh(self):
            return None

    class FakeOp:
        def __init__(self, output):
            self._output = output
            self._seqnum = FakeSeqnum(0x1000, 3)

        def getSeqnum(self):
            return self._seqnum

        def getOutput(self):
            return self._output

        def getMnemonic(self):
            return "COPY"

        def getNumInputs(self):
            return 0

    class FakeTracer:
        def __init__(self, ops):
            self._ops = ops

        def get_all_pcode_ops(self):
            return self._ops

        def _get_storage_info_from_varnode(self, varnode):
            return getattr(varnode, "storage", None)

        def trace_varnode(self, _varnode, use_cache=False, depth=0):
            return Expression.variable("opaque", size=8)

    misleading_output = FakeVarnode(StorageInfo(**_reg_storage("a2")), size=8)
    tracer = FakeTracer([FakeOp(misleading_output)])
    call_op = FakeOp(None)
    local_addr = Expression.binary_op(
        "INT_ADD",
        Expression.variable(
            "sp",
            size=8,
            storage_info=StorageInfo(
                is_register=True,
                space_name="register",
                register_name="sp",
                base_register_name="sp",
                size=8,
                size_bits=64,
                base_register_size=8,
                base_register_size_bits=64,
                bit_offset_in_base=0,
            ),
        ),
        Expression.constant(-0x30, 8),
    )

    recovered = _recover_call_argument_expressions(
        call_op,
        tracer,
        [
            _param("param_1", size=4, is_signed=False, index=0),
            _param("param_2", size=4, is_signed=False, index=1),
        ],
        [
            {"name": "param_1", "size": 4, "storage": _reg_storage("a0_lo", size_bytes=4, register_name="a0_lo")},
            {"name": "param_2", "size": 4, "storage": _reg_storage("a1_lo", size_bytes=4, register_name="a1_lo")},
            {"name": "param_3", "size": 8, "storage": _reg_storage("a2")},
        ],
        [
            Expression.parameter("param_1", 0, size=4),
            Expression.parameter("param_2", 1, size=4),
            local_addr,
        ],
    )

    assert recovered[2].to_string() == "(sp + (-48))"


def test_recover_call_argument_expressions_refuses_unresolved_positional_arguments():
    class FakeTracer:
        def get_all_pcode_ops(self):
            return []

    recovered = _recover_call_argument_expressions(
        call_op=object(),
        tracer=FakeTracer(),
        caller_parameters=[
            _param("caller_a", size=8, is_signed=False, index=0),
            _param("caller_b", size=8, is_signed=False, index=1),
        ],
        callee_parameters=[
            {"name": "callee_a", "size": 8},
            {"name": "callee_b", "size": 8},
        ],
        explicit_args=[],
    )

    assert recovered == []


def test_recover_call_argument_expressions_preserves_explicit_phi_function_pointer():
    class FakeAddress:
        def __init__(self, offset, space_name="ram"):
            self._offset = offset
            self._space_name = space_name

        def getOffset(self):
            return self._offset

        def getAddressSpace(self):
            return self

        def getName(self):
            return self._space_name

    class FakeSeqnum:
        def __init__(self, offset, order):
            self._target = FakeAddress(offset)
            self._order = order

        def getTarget(self):
            return self._target

        def getOrder(self):
            return self._order

    class FakeOp:
        def __init__(self):
            self._seqnum = FakeSeqnum(0x1000, 3)

        def getSeqnum(self):
            return self._seqnum

        def getOutput(self):
            return None

        def getMnemonic(self):
            return "CALL"

        def getNumInputs(self):
            return 0

    class FakeTracer:
        def get_all_pcode_ops(self):
            return []

        def _get_storage_info_from_varnode(self, _varnode):
            return None

        def trace_varnode(self, _varnode, use_cache=False, depth=0):
            return Expression.variable("opaque", size=8)

    call_op = FakeOp()
    explicit_target = Expression.phi(
        [
            (
                Condition(
                    Expression.binary_op(
                        "INT_EQUAL",
                        Expression.parameter("selector", 0, size=4),
                        Expression.constant(0, 4),
                    ),
                    False,
                ),
                Expression.binary_op(
                    "INT_ADD",
                    Expression.constant(0, 8),
                    Expression.constant(0x100814, 8),
                ),
            ),
            (
                Condition(
                    Expression.binary_op(
                        "INT_NOTEQUAL",
                        Expression.parameter("selector", 0, size=4),
                        Expression.constant(0, 4),
                    ),
                    False,
                ),
                Expression.binary_op(
                    "INT_ADD",
                    Expression.constant(0, 8),
                    Expression.constant(0x10081C, 8),
                ),
            ),
        ]
    )

    recovered = _recover_call_argument_expressions(
        call_op,
        FakeTracer(),
        [
            _param("param_1", size=8, is_signed=False, index=0, storage=_reg_storage("x0")),
        ],
        [
            {"name": "param_1", "size": 8, "data_type": "code *", "storage": _reg_storage("x0")},
        ],
        [explicit_target],
    )

    assert len(recovered) == 1
    assert recovered[0].expr_type.name == "PHI"
    assert recovered[0].to_string() == explicit_target.to_string()


def test_recover_call_argument_expressions_refuses_unproven_explicit_subsequence_alignment():
    class FakeAddress:
        def __init__(self, offset, space_name="ram"):
            self._offset = offset
            self._space_name = space_name

        def getOffset(self):
            return self._offset

        def getAddressSpace(self):
            return self

        def getName(self):
            return self._space_name

    class FakeSeqnum:
        def __init__(self, offset, order):
            self._target = FakeAddress(offset)
            self._order = order

        def getTarget(self):
            return self._target

        def getOrder(self):
            return self._order

    class FakeCallOp:
        def __init__(self):
            self._seqnum = FakeSeqnum(0x2000, 10)

        def getSeqnum(self):
            return self._seqnum

        def getOutput(self):
            return None

        def getMnemonic(self):
            return "CALL"

        def getNumInputs(self):
            return 0

    class FakeTracer:
        def get_all_pcode_ops(self):
            return []

        def _get_storage_info_from_varnode(self, _varnode):
            return None

        def trace_varnode(self, _varnode, use_cache=False, depth=0):
            return Expression.variable("opaque", size=4)

    recovered = _recover_call_argument_expressions(
        FakeCallOp(),
        FakeTracer(),
        [
            _param("param_1", size=4, is_signed=False, index=0, storage=_reg_storage("a0", size_bytes=4)),
            _param("param_2", size=4, is_signed=False, index=1, storage=_reg_storage("a1", size_bytes=4)),
            _param("param_3", size=4, is_signed=False, index=2, storage=_reg_storage("a2", size_bytes=4)),
        ],
        [
            _param("lhs", size=4, is_signed=False, index=0, storage=_reg_storage("a0", size_bytes=4)),
            _param("rhs", size=4, is_signed=False, index=1, storage=_reg_storage("a1", size_bytes=4)),
            _param("bias", size=4, is_signed=False, index=2, storage=_reg_storage("a2", size_bytes=4)),
        ],
        [
            Expression.binary_op(
                "INT_SUB",
                Expression.parameter("param_1", 0, size=4),
                Expression.parameter("param_2", 1, size=4),
            ),
            Expression.parameter("param_1", 0, size=4),
            Expression.parameter("param_2", 1, size=4),
            Expression.constant(1, 4),
        ],
    )

    assert recovered == []


def test_recover_call_argument_expressions_refuses_right_aligned_hidden_prefix_without_object_evidence():
    class FakeAddress:
        def __init__(self, offset, space_name="ram"):
            self._offset = offset
            self._space_name = space_name

        def getOffset(self):
            return self._offset

        def getAddressSpace(self):
            return self

        def getName(self):
            return self._space_name

    class FakeSeqnum:
        def __init__(self, offset, order):
            self._target = FakeAddress(offset)
            self._order = order

        def getTarget(self):
            return self._target

        def getOrder(self):
            return self._order

    class FakeCallOp:
        def __init__(self):
            self._seqnum = FakeSeqnum(0x3000, 10)

        def getSeqnum(self):
            return self._seqnum

        def getOutput(self):
            return None

        def getMnemonic(self):
            return "CALL"

        def getNumInputs(self):
            return 0

    class FakeTracer:
        def get_all_pcode_ops(self):
            return []

        def _get_storage_info_from_varnode(self, _varnode):
            return None

        def trace_varnode(self, _varnode, use_cache=False, depth=0):
            return Expression.variable("opaque", size=4)

    recovered = _recover_call_argument_expressions(
        FakeCallOp(),
        FakeTracer(),
        [
            _param("param_1", size=4, is_signed=False, index=0, storage=_reg_storage("a0", size_bytes=4)),
            _param("param_2", size=4, is_signed=False, index=1, storage=_reg_storage("a1", size_bytes=4)),
            _param("param_3", size=4, is_signed=False, index=2, storage=_reg_storage("a2", size_bytes=4)),
        ],
        [
            _param("value", size=4, is_signed=False, index=0, storage=_reg_storage("a0", size_bytes=4)),
            _param("bias", size=4, is_signed=False, index=1, storage=_reg_storage("a1", size_bytes=4)),
        ],
        [
            Expression.parameter("param_3", 2, size=4),
            Expression.parameter("param_3", 2, size=4),
            Expression.constant(0xFFFFFFFD, 8),
        ],
    )

    assert recovered == []


def test_recover_call_argument_expressions_uses_path_sensitive_multiequal_input_for_hidden_arg():
    class FakeAddress:
        def __init__(self, offset, space_name="ram"):
            self._offset = offset
            self._space_name = space_name

        def getOffset(self):
            return self._offset

        def getAddressSpace(self):
            return self

        def getName(self):
            return self._space_name

    class FakeSeqnum:
        def __init__(self, offset, order):
            self._target = FakeAddress(offset)
            self._order = order

        def getTarget(self):
            return self._target

        def getOrder(self):
            return self._order

    class FakeVarnode:
        def __init__(self, name):
            self.name = name

        def getDef(self):
            return None

        def getSize(self):
            return 4

        def getHigh(self):
            return None

    class FakeBlock:
        def __init__(self, index):
            self._index = index
            self._ins = []

        def getIndex(self):
            return self._index

        def getInSize(self):
            return len(self._ins)

        def getIn(self, index):
            return self._ins[index]

    class FakeBlockInfo:
        def __init__(self, block, pcode_ops):
            self.block = block
            self.index = block.getIndex()
            self.pcode_ops = list(pcode_ops)

    class FakeOp:
        def __init__(self, mnemonic, order, output=None, inputs=None):
            self._mnemonic = mnemonic
            self._seqnum = FakeSeqnum(0x4000, order)
            self._output = output
            self._inputs = list(inputs or [])

        def getSeqnum(self):
            return self._seqnum

        def getOutput(self):
            return self._output

        def getMnemonic(self):
            return self._mnemonic

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

    class FakeTracer:
        def __init__(self, expressions, storage_map, ops):
            self._expressions = expressions
            self._storage_map = storage_map
            self._ops = ops

        def get_all_pcode_ops(self):
            return list(self._ops)

        def _get_storage_info_from_varnode(self, varnode):
            return self._storage_map.get(varnode)

        def trace_varnode(self, varnode, use_cache=False, depth=0):
            return self._expressions[varnode]

    class FakeConditionTracker:
        def __init__(self, block_infos, path_entries):
            self.block_by_index = {info.index: info for info in block_infos}
            self._paths = list(path_entries)

        def get_all_valid_block_paths_to_block(self, _target_block):
            return list(self._paths)

    output = FakeVarnode("out")
    path_true_input = FakeVarnode("path_true")
    path_false_input = FakeVarnode("path_false")
    target_storage = StorageInfo(**_reg_storage("a2", size_bytes=4, register_name="a2"))

    phi_op = FakeOp("MULTIEQUAL", 1, output=output, inputs=[path_false_input, path_true_input])
    call_op = FakeOp("CALL", 2)

    false_block = FakeBlock(1)
    true_block = FakeBlock(2)
    call_block = FakeBlock(3)
    call_block._ins = [false_block, true_block]

    false_info = FakeBlockInfo(false_block, [])
    true_info = FakeBlockInfo(true_block, [])
    call_info = FakeBlockInfo(call_block, [phi_op, call_op])

    selector = Expression.parameter("selector", 0, size=4)
    true_cond = Condition(
        Expression.binary_op("INT_NOTEQUAL", selector, Expression.constant(0, 4)),
        False,
    )
    false_cond = Condition(
        Expression.binary_op("INT_EQUAL", selector, Expression.constant(0, 4)),
        False,
    )

    tracer = FakeTracer(
        {
            output: Expression.phi([(false_cond, Expression.variable("tmp_x2", size=4)), (true_cond, Expression.parameter("param_3", 2, size=4))]),
            path_false_input: Expression.variable("tmp_x2", size=4),
            path_true_input: Expression.parameter("param_3", 2, size=4),
        },
        {
            output: target_storage,
        },
        [phi_op, call_op],
    )
    condition_tracker = FakeConditionTracker(
        [false_info, true_info, call_info],
        [
            ([false_info, call_info], [false_cond]),
            ([true_info, call_info], [true_cond]),
        ],
    )

    recovered = _recover_call_argument_expressions(
        call_op,
        tracer,
        [
            _param("selector", size=4, is_signed=False, index=0, storage=_reg_storage("a0", size_bytes=4)),
            _param("param_3", size=4, is_signed=False, index=2, storage=target_storage),
        ],
        [
            _param("rhs", size=4, is_signed=False, index=0, storage=target_storage),
        ],
        [],
        condition_tracker=condition_tracker,
        current_conditions=[true_cond],
    )

    assert len(recovered) == 1
    assert recovered[0].to_string() == "param_3"


def test_resolve_call_argument_expression_recovers_parameter_from_storage_alias():
    class FakeVarnode:
        def getSize(self):
            return 8

        def getDef(self):
            return None

        def getHigh(self):
            return None

    class FakeTracer:
        def trace_varnode(self, _varnode, use_cache=False):
            return Expression.variable("tmp_arg", size=8)

        def _get_storage_info_from_varnode(self, _varnode):
            return StorageInfo(
                is_register=True,
                space_name="register",
                register_name="A0",
                base_register_name="A0",
                size=8,
                size_bits=64,
                base_register_size=8,
                base_register_size_bits=64,
                bit_offset_in_base=0,
            )

    resolved = _resolve_call_argument_expression(
        FakeVarnode(),
        FakeTracer(),
        [_param("param_1", size=8, is_signed=False, storage=_reg_storage("A0"))],
    )

    assert resolved.expr_type.name == "PARAMETER"
    assert resolved.name == "param_1"


def test_resolve_call_argument_expression_does_not_relabel_call_defined_register_as_parameter():
    class FakeSymbol:
        def __init__(self, name: str):
            self._name = name

        def getName(self):
            return self._name

        def isParameter(self):
            return True

    class FakeHigh:
        def __init__(self, name: str, symbol=None):
            self._name = name
            self._symbol = symbol

        def getName(self):
            return self._name

        def getSymbol(self):
            return self._symbol

    class FakeCallOp:
        def getMnemonic(self):
            return "CALL"

    class FakeVarnode:
        def __init__(self, def_op=None, high=None):
            self._def_op = def_op
            self._high = high

        def getSize(self):
            return 4

        def getDef(self):
            return self._def_op

        def getHigh(self):
            return self._high

    call_defined = FakeVarnode(
        def_op=FakeCallOp(),
        high=FakeHigh("param_1", FakeSymbol("param_1")),
    )

    class FakeTracer:
        def trace_varnode(self, _varnode, use_cache=False):
            return Expression.variable(
                "w0",
                size=4,
                storage_info=StorageInfo(**_reg_storage("a0", size_bytes=4, register_name="a0")),
            )

        def _get_storage_info_from_varnode(self, _varnode):
            return StorageInfo(**_reg_storage("a0", size_bytes=4, register_name="a0"))

    resolved = _resolve_call_argument_expression(
        call_defined,
        FakeTracer(),
        [_param("param_1", size=4, is_signed=False, storage=_reg_storage("a0", size_bytes=4, register_name="a0"))],
    )

    assert resolved.expr_type.name == "VARIABLE"
    assert resolved.name == "w0"


def test_normalize_call_argument_expression_refuses_positional_parameter_fallback():
    unresolved = Expression.variable("opaque_arg", size=8)

    normalized = _normalize_call_argument_expression(
        unresolved,
        1,
        [
            _param("param_1", size=8, is_signed=False, index=0),
            _param("param_2", size=8, is_signed=False, index=1),
        ],
    )

    assert normalized is unresolved


def test_normalize_call_argument_expression_uses_storage_identity():
    storage = StorageInfo(**_reg_storage("a1"))
    variable = Expression.variable("opaque_arg", size=8, storage_info=storage)

    normalized = _normalize_call_argument_expression(
        variable,
        0,
        [
            _param("param_1", size=8, is_signed=False, index=0, storage=_reg_storage("a0")),
            _param("param_2", size=8, is_signed=False, index=1, storage=_reg_storage("a1")),
        ],
    )

    assert normalized.expr_type.name == "PARAMETER"
    assert normalized.name == "param_2"
    assert normalized.value == 1


def test_choose_effect_substitution_args_does_not_invent_positional_parameters():
    args = [Expression.variable("opaque0", size=8), Expression.variable("opaque1", size=8)]

    chosen = _choose_effect_substitution_args(
        _loc("a", 0, 4),
        ["a", "b"],
        args,
        [
            _param("param_1", size=8, is_signed=False, index=0),
            _param("param_2", size=8, is_signed=False, index=1),
        ],
    )

    assert chosen is args


def test_summarize_store_effects_marks_argumentless_call_unknown_without_callsite_arg_evidence():
    class FakeAddress:
        def __init__(self, offset):
            self._offset = offset

        def getOffset(self):
            return self._offset

    class FakeSeqnum:
        def __init__(self, offset, order):
            self._target = FakeAddress(offset)
            self._order = order

        def getTarget(self):
            return self._target

        def getOrder(self):
            return self._order

    class FakeVarnode:
        def getAddress(self):
            return None

    class FakeCallOp:
        def __init__(self):
            self._target = FakeVarnode()
            self._seqnum = FakeSeqnum(0x401000, 1)

        def getMnemonic(self):
            return "CALL"

        def getNumInputs(self):
            return 1

        def getInput(self, index):
            assert index == 0
            return self._target

        def getOutput(self):
            return None

        def getSeqnum(self):
            return self._seqnum

    class FakeBlockInfo:
        def __init__(self, op):
            self.pcode_ops = [op]

    class FakeConditionTracker:
        def get_all_valid_paths_to_block(self, _block):
            return [[]]

    class FakeTracer:
        def __init__(self, op):
            self._op = op

        def resolve_call_target_ref(self, _varnode, **_kwargs):
            return CallTargetRef.from_name("callee")

        def _get_function_name(self, _varnode):
            return "callee"

        def get_all_pcode_ops(self):
            return [self._op]

        def _get_storage_info_from_varnode(self, _varnode):
            return None

        def trace_varnode(self, _varnode, use_cache=False):
            return Expression.constant(0x401100, 8)

    call_op = FakeCallOp()
    captured_args = {}

    def _direct_call_summary(_name, args):
        captured_args["args"] = list(args)
        return EffectSummary(
            parameter_names=["a", "b"],
            effects=[
                StoreEffect(
                    location=_loc("a", 0, 4),
                    value=Expression.memory(Expression.parameter("b", 1, size=8), size=4),
                    conditions=[],
                    order_key=1,
                ),
                StoreEffect(
                    location=_loc("b", 0, 4),
                    value=Expression.memory(Expression.parameter("a", 0, size=8), size=4),
                    conditions=[],
                    order_key=1,
                ),
            ],
        )

    summary = summarize_store_effects(
        [FakeBlockInfo(call_op)],
        FakeTracer(call_op),
        FakeConditionTracker(),
        [
            _param("param_1", size=8, is_signed=False, index=0, storage=_reg_storage("x0", register_name="x0")),
            _param("param_2", size=8, is_signed=False, index=1, storage=_reg_storage("x1", register_name="x1")),
        ],
        direct_call_summary=_direct_call_summary,
        resolve_callee_parameters=lambda _target_ref: [
            _param("a", size=8, is_signed=False, index=0, storage=_reg_storage("x0", register_name="x0")),
            _param("b", size=8, is_signed=False, index=1, storage=_reg_storage("x1", register_name="x1")),
        ],
        debug=False,
    )

    assert "args" not in captured_args
    assert summary.effects == []
    assert summary.has_unsupported_call is True


def test_summarize_store_effects_substitutes_stack_pointer_relative_out_parameter_locations():
    class FakeAddress:
        def __init__(self, offset):
            self._offset = offset

        def getOffset(self):
            return self._offset

    class FakeSeqnum:
        def __init__(self, offset, order):
            self._target = FakeAddress(offset)
            self._order = order

        def getTarget(self):
            return self._target

        def getOrder(self):
            return self._order

    class FakeVarnode:
        def __init__(self, key):
            self.key = key

        def getSize(self):
            return 8

        def getDef(self):
            return None

        def getHigh(self):
            return None

    class FakeCallOp:
        def __init__(self):
            self._inputs = [
                FakeVarnode("target"),
                FakeVarnode("arg0"),
                FakeVarnode("out0"),
            ]
            self._seqnum = FakeSeqnum(0x401100, 3)

        def getMnemonic(self):
            return "CALL"

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

        def getOutput(self):
            return None

        def getSeqnum(self):
            return self._seqnum

    class FakeBlockInfo:
        def __init__(self, op):
            self.pcode_ops = [op]

    class FakeConditionTracker:
        def get_all_valid_paths_to_block(self, _block):
            return [[]]

    sp = Expression.variable(
        "sp",
        size=8,
        storage_info=StorageInfo(
            is_register=True,
            space_name="register",
            register_name="sp",
            base_register_name="sp",
            size=8,
            size_bits=64,
            base_register_size=8,
            base_register_size_bits=64,
            bit_offset_in_base=0,
        ),
    )

    class FakeTracer:
        def __init__(self, op):
            self._op = op

        def _get_function_name(self, _varnode):
            return "callee"

        def get_all_pcode_ops(self):
            return [self._op]

        def _get_storage_info_from_varnode(self, _varnode):
            return None

        def trace_varnode(self, varnode, use_cache=False):
            if varnode.key == "arg0":
                return Expression.parameter("param_1", 0, size=8)
            if varnode.key == "out0":
                return Expression.binary_op("INT_ADD", sp, Expression.constant(-0x1C, 8))
            return Expression.constant(0x401100, 8)

    call_op = FakeCallOp()
    summary = summarize_store_effects(
        [FakeBlockInfo(call_op)],
        FakeTracer(call_op),
        FakeConditionTracker(),
        [_param("param_1", size=8, is_signed=False, index=0)],
        direct_call_summary=lambda _target_ref, _args: EffectSummary(
            parameter_names=["value", "out"],
            parameter_refs=[
                LocationBaseRef.parameter("value", index=0),
                LocationBaseRef.parameter("out", index=1),
            ],
            effects=[
                StoreEffect(
                    location=_loc("out", 0, 4),
                    value=Expression.parameter("value", 0, size=4),
                    conditions=[],
                    order_key=1,
                )
            ],
        ),
        resolve_callee_parameters=lambda _target_ref: [
            _param("value", size=8, is_signed=False, index=0),
            _param("out", size=8, is_signed=False, index=1),
        ],
        debug=False,
    )

    assert len(summary.effects) == 1
    assert summary.effects[0].location == _loc("__locbase__stackframe", -0x1C, 4)
    assert summary.effects[0].value.expr_type.name == "PARAMETER"
    assert summary.effects[0].value.name == "param_1"


def test_expression_expander_stabilizes_parameter_like_call_arg_from_original_input():
    class FakeAddress:
        def __init__(self, offset):
            self._offset = offset

        def getOffset(self):
            return self._offset

        def getAddressSpace(self):
            return self

        def getName(self):
            return "ram"

    class FakeSeqnum:
        def __init__(self, offset, order):
            self._target = FakeAddress(offset)
            self._order = order

        def getTarget(self):
            return self._target

        def getOrder(self):
            return self._order

    class FakeSymbol:
        def __init__(self, name: str, is_parameter: bool):
            self._name = name
            self._is_parameter = is_parameter

        def getName(self):
            return self._name

        def isParameter(self):
            return self._is_parameter

    class FakeHigh:
        def __init__(self, name: str, symbol=None):
            self._name = name
            self._symbol = symbol

        def getName(self):
            return self._name

        def getSymbol(self):
            return self._symbol

    class FakeVarnode:
        def __init__(self, name, size=4, def_op=None, high=None):
            self.name = name
            self._size = size
            self._def_op = def_op
            self._high = high

        def getDef(self):
            return self._def_op

        def getSize(self):
            return self._size

        def getHigh(self):
            return self._high

    class FakeOutput:
        def __init__(self, size):
            self._size = size

        def getSize(self):
            return self._size

    class FakeCopyOp:
        def __init__(self, source):
            self._source = source

        def getMnemonic(self):
            return "COPY"

        def getNumInputs(self):
            return 1

        def getInput(self, index):
            return self._source if index == 0 else None

    class FakeCallOp:
        def __init__(self, inputs):
            self._inputs = inputs
            self._output = FakeOutput(4)
            self._seqnum = FakeSeqnum(0x401020, 10)

        def getMnemonic(self):
            return "CALL"

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

        def getOutput(self):
            return self._output

        def getSeqnum(self):
            return self._seqnum

    target_varnode = FakeVarnode("callee_addr", size=8)
    source_param3 = FakeVarnode(
        "param3_src",
        size=4,
        high=FakeHigh("param_3", FakeSymbol("param_3", True)),
    )
    copied_first_arg = FakeVarnode(
        "copied_first_arg",
        size=4,
        def_op=FakeCopyOp(source_param3),
        high=FakeHigh("tmp_w0"),
    )
    bias_varnode = FakeVarnode("bias", size=4)
    call_op = FakeCallOp([target_varnode, copied_first_arg, bias_varnode])

    class FakeTracer:
        debug = False

        def resolve_call_target_ref(self, _varnode, **_kwargs):
            return CallTargetRef.from_name("fc_bias")

        def _get_function_name(self, _varnode):
            return "fc_bias"

        def trace_varnode(self, varnode, depth=0, use_cache=False):
            if varnode is target_varnode:
                return Expression.constant(0x401000, 8)
            if varnode is copied_first_arg:
                return Expression.variable(
                    "w0",
                    size=4,
                    storage_info=StorageInfo(**_reg_storage("a0", size_bytes=4, register_name="a0")),
                )
            if varnode is bias_varnode:
                return Expression.constant(0xFFFFFFFD, 4)
            raise AssertionError(f"unexpected trace: {varnode}")

        def emit_unknown_event(self, **kwargs):
            raise AssertionError(f"call should have been resolved: {kwargs}")

        def _trace_pcode_op(self, *_args, **_kwargs):
            raise AssertionError("recursive tracing fallback should not run")

        def get_all_pcode_ops(self):
            return [call_op]

        def _get_storage_info_from_varnode(self, varnode):
            if varnode is copied_first_arg:
                return StorageInfo(**_reg_storage("a0", size_bytes=4, register_name="a0"))
            if varnode is source_param3:
                return StorageInfo(**_reg_storage("a2", size_bytes=4, register_name="a2"))
            return None

    captured = {}

    def resolve_call(target_ref, args):
        captured["target"] = target_ref
        captured["args"] = list(args)
        return [ExpandedValue(Expression.constant(1, 4), [])]

    expander = ExpressionExpander(
        FakeTracer(),
        condition_tracker=None,
        debug=False,
        call_resolver=resolve_call,
        parameters=[
            _param("param_1", size=4, index=0, storage=_reg_storage("a0", size_bytes=4, register_name="a0")),
            _param("param_3", size=4, index=2, storage=_reg_storage("a2", size_bytes=4, register_name="a2")),
        ],
        resolve_callee_parameters=lambda _target_ref: [
            _param("value", size=4, index=0, storage=_reg_storage("a0", size_bytes=4, register_name="a0")),
            _param("bias", size=4, index=1, storage=_reg_storage("a1", size_bytes=4, register_name="a1")),
        ],
    )
    expander._expand_input_varnode = lambda varnode, conditions, depth: {
        copied_first_arg: [ExpandedValue(Expression.parameter("param_1", 0, size=4), [])],
        bias_varnode: [ExpandedValue(Expression.constant(0xFFFFFFFD, 4), [])],
    }[varnode]

    expanded = expander._expand_call_operation(call_op, [], depth=0, output_size=4)

    assert len(expanded) == 1
    assert captured["target"] == CallTargetRef.from_name("fc_bias")
    assert [arg.to_string() for arg in captured["args"]] == ["param_3", "4294967293"]


def test_summarize_store_effects_recovers_direct_call_store_values_from_call_expander():
    class FakeAddress:
        def __init__(self, offset):
            self._offset = offset

        def getOffset(self):
            return self._offset

    class FakeSeqnum:
        def __init__(self, offset, order):
            self._target = FakeAddress(offset)
            self._order = order

        def getTarget(self):
            return self._target

        def getOrder(self):
            return self._order

    class FakeVarnode:
        def __init__(self, key, size, def_op=None):
            self.key = key
            self._size = size
            self._def_op = def_op

        def getSize(self):
            return self._size

        def getDef(self):
            return self._def_op

        def getHigh(self):
            return None

    class FakeCallOp:
        def __init__(self):
            self._inputs = [
                FakeVarnode("target", 8),
                FakeVarnode("lhs", 4),
                FakeVarnode("rhs", 4),
            ]
            self._seqnum = FakeSeqnum(0x401180, 2)

        def getMnemonic(self):
            return "CALL"

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

        def getOutput(self):
            return None

        def getSeqnum(self):
            return self._seqnum

    class FakeStoreOp:
        def __init__(self, call_op):
            self._inputs = [
                FakeVarnode("space", 4),
                FakeVarnode("addr", 8),
                FakeVarnode("value", 4, def_op=call_op),
            ]
            self._seqnum = FakeSeqnum(0x401190, 3)

        def getMnemonic(self):
            return "STORE"

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

        def getOutput(self):
            return None

        def getSeqnum(self):
            return self._seqnum

    class FakeBlockInfo:
        def __init__(self, *ops):
            self.pcode_ops = list(ops)

    class FakeConditionTracker:
        def get_all_valid_paths_to_block(self, _block):
            return [[]]

    class FakeTracer:
        def _get_function_name(self, varnode):
            if getattr(varnode, "key", None) == "target":
                return "fc_add"
            return "UNKNOWN_FUNC"

        def trace_varnode(self, varnode, use_cache=False):
            if varnode.key == "addr":
                return Expression.parameter("slot", 0, size=8)
            if varnode.key == "lhs":
                return Expression.parameter("lhs", 1, size=4)
            if varnode.key == "rhs":
                return Expression.parameter("rhs", 2, size=4)
            if varnode.key == "value":
                return Expression.unknown("call_out_of_scope:fc_add")
            return Expression.constant(0, max(1, varnode.getSize()))

    call_op = FakeCallOp()
    summary = summarize_store_effects(
        [FakeBlockInfo(FakeStoreOp(call_op))],
        FakeTracer(),
        FakeConditionTracker(),
        [
            _param("slot", size=8, is_signed=False, index=0, storage=_reg_storage("x0", register_name="x0")),
            _param("lhs", size=4, index=1, storage=_reg_storage("x1", size_bytes=4, register_name="w1")),
            _param("rhs", size=4, index=2, storage=_reg_storage("x2", size_bytes=4, register_name="w2")),
        ],
        direct_call_expander=lambda _target_ref, args: [
            ExpandedValue(Expression.binary_op("INT_ADD", args[0], args[1]), [])
        ],
        resolve_callee_parameters=lambda _target_ref: [
            _param("a", size=4, index=0, storage=_reg_storage("x0", size_bytes=4, register_name="w0")),
            _param("b", size=4, index=1, storage=_reg_storage("x1", size_bytes=4, register_name="w1")),
        ],
        debug=False,
    )

    assert summary.has_unsupported_call is False
    assert len(summary.effects) == 1
    assert summary.effects[0].location == _loc("slot", 0, 4)
    assert summary.effects[0].value.to_string() == "(lhs + rhs)"


def test_summarize_store_effects_expands_nested_copy_and_arithmetic_store_values_object_centrically():
    class FakeAddress:
        def __init__(self, offset):
            self._offset = offset

        def getOffset(self):
            return self._offset

    class FakeSeqnum:
        def __init__(self, offset, order):
            self._target = FakeAddress(offset)
            self._order = order

        def getTarget(self):
            return self._target

        def getOrder(self):
            return self._order

    class FakeVarnode:
        def __init__(self, key, size, def_op=None):
            self.key = key
            self._size = size
            self._def_op = def_op

        def getSize(self):
            return self._size

        def getDef(self):
            return self._def_op

        def getHigh(self):
            return None

    class FakeCallOp:
        def __init__(self):
            self._inputs = [
                FakeVarnode("target", 8),
                FakeVarnode("lhs", 4),
                FakeVarnode("rhs", 4),
            ]
            self._output = FakeVarnode("ret", 4, def_op=self)
            self._seqnum = FakeSeqnum(0x401180, 2)

        def getMnemonic(self):
            return "CALL"

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

        def getOutput(self):
            return self._output

        def getSeqnum(self):
            return self._seqnum

    class FakeCopyOp:
        def __init__(self, source):
            self._inputs = [source]
            self._output = FakeVarnode("copied", 4, def_op=self)
            self._seqnum = FakeSeqnum(0x401184, 3)

        def getMnemonic(self):
            return "COPY"

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

        def getOutput(self):
            return self._output

        def getSeqnum(self):
            return self._seqnum

    class FakeAddOp:
        def __init__(self, lhs, rhs):
            self._inputs = [lhs, rhs]
            self._output = FakeVarnode("sum", 4, def_op=self)
            self._seqnum = FakeSeqnum(0x401188, 4)

        def getMnemonic(self):
            return "INT_ADD"

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

        def getOutput(self):
            return self._output

        def getSeqnum(self):
            return self._seqnum

    class FakeStoreOp:
        def __init__(self, value_varnode):
            self._inputs = [
                FakeVarnode("space", 4),
                FakeVarnode("addr", 8),
                value_varnode,
            ]
            self._seqnum = FakeSeqnum(0x401190, 5)

        def getMnemonic(self):
            return "STORE"

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

        def getOutput(self):
            return None

        def getSeqnum(self):
            return self._seqnum

    class FakeBlockInfo:
        def __init__(self, *ops):
            self.pcode_ops = list(ops)

    class FakeConditionTracker:
        def get_all_valid_paths_to_block(self, _block):
            return [[]]

    class FakeTracer:
        def _get_function_name(self, varnode):
            if getattr(varnode, "key", None) == "target":
                return "fc_add"
            return "UNKNOWN_FUNC"

        def _trace_pcode_op(self, pcode_op, depth=0, use_cache=False):
            mnemonic = pcode_op.getMnemonic()
            if mnemonic == "INT_ADD":
                return Expression.binary_op(
                    "INT_ADD",
                    self.trace_varnode(pcode_op.getInput(0), use_cache=False),
                    self.trace_varnode(pcode_op.getInput(1), use_cache=False),
                )
            raise AssertionError(f"unexpected traced op: {mnemonic}")

        def trace_varnode(self, varnode, depth=0, use_cache=False):
            if varnode.key == "addr":
                return Expression.parameter("slot", 0, size=8)
            if varnode.key == "lhs":
                return Expression.parameter("lhs", 1, size=4)
            if varnode.key == "rhs":
                return Expression.parameter("rhs", 2, size=4)
            if varnode.key == "copied":
                return Expression.unknown("copied_call_value")
            if varnode.key == "ret":
                return Expression.unknown("call_out_of_scope:fc_add")
            if varnode.key == "sum":
                return Expression.unknown("nested_sum")
            return Expression.constant(0, max(1, varnode.getSize()))

        def _get_op_order_key(self, pcode_op):
            return pcode_op.getSeqnum().getOrder()

    call_op = FakeCallOp()
    copy_op = FakeCopyOp(call_op.getOutput())
    add_op = FakeAddOp(copy_op.getOutput(), FakeVarnode("rhs", 4))

    summary = summarize_store_effects(
        [FakeBlockInfo(call_op, copy_op, add_op, FakeStoreOp(add_op.getOutput()))],
        FakeTracer(),
        FakeConditionTracker(),
        [
            _param("slot", size=8, is_signed=False, index=0, storage=_reg_storage("x0", register_name="x0")),
            _param("lhs", size=4, index=1, storage=_reg_storage("x1", size_bytes=4, register_name="w1")),
            _param("rhs", size=4, index=2, storage=_reg_storage("x2", size_bytes=4, register_name="w2")),
        ],
        direct_call_expander=lambda _target_ref, args: [
            ExpandedValue(Expression.binary_op("INT_ADD", args[0], args[1]), [])
        ],
        resolve_callee_parameters=lambda _target_ref: [
            _param("a", size=4, index=0, storage=_reg_storage("x0", size_bytes=4, register_name="w0")),
            _param("b", size=4, index=1, storage=_reg_storage("x1", size_bytes=4, register_name="w1")),
        ],
        debug=False,
    )

    assert summary.has_unsupported_call is False
    assert len(summary.effects) == 1
    assert summary.effects[0].location == _loc("slot", 0, 4)
    assert summary.effects[0].value.to_string() == "((lhs + rhs) + rhs)"


def test_summarize_store_effects_keeps_effect_free_value_calls_from_poisoning_summary():
    class FakeAddress:
        def __init__(self, offset):
            self._offset = offset

        def getOffset(self):
            return self._offset

    class FakeSeqnum:
        def __init__(self, offset, order):
            self._target = FakeAddress(offset)
            self._order = order

        def getTarget(self):
            return self._target

        def getOrder(self):
            return self._order

    class FakeVarnode:
        def __init__(self, key, size, def_op=None):
            self.key = key
            self._size = size
            self._def_op = def_op

        def getSize(self):
            return self._size

        def getDef(self):
            return self._def_op

        def getHigh(self):
            return None

    class FakeCallOp:
        def __init__(self):
            self._inputs = [
                FakeVarnode("target", 8),
                FakeVarnode("lhs", 4),
                FakeVarnode("rhs", 4),
            ]
            self._output = FakeVarnode("ret", 4, def_op=self)
            self._seqnum = FakeSeqnum(0x401180, 2)

        def getMnemonic(self):
            return "CALL"

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

        def getOutput(self):
            return self._output

        def getSeqnum(self):
            return self._seqnum

    class FakeStoreOp:
        def __init__(self, call_op):
            self._inputs = [
                FakeVarnode("space", 4),
                FakeVarnode("addr", 8),
                call_op.getOutput(),
            ]
            self._seqnum = FakeSeqnum(0x401190, 3)

        def getMnemonic(self):
            return "STORE"

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

        def getOutput(self):
            return None

        def getSeqnum(self):
            return self._seqnum

    class FakeBlockInfo:
        def __init__(self, *ops):
            self.pcode_ops = list(ops)

    class FakeConditionTracker:
        def get_all_valid_paths_to_block(self, _block):
            return [[]]

    class FakeTracer:
        def _get_function_name(self, varnode):
            if getattr(varnode, "key", None) == "target":
                return "fc_add"
            return "UNKNOWN_FUNC"

        def trace_varnode(self, varnode, use_cache=False):
            if varnode.key == "addr":
                return Expression.parameter("slot", 0, size=8)
            if varnode.key == "lhs":
                return Expression.parameter("lhs", 1, size=4)
            if varnode.key == "rhs":
                return Expression.parameter("rhs", 2, size=4)
            if varnode.key == "ret":
                return Expression.unknown("call_out_of_scope:fc_add")
            return Expression.constant(0, max(1, varnode.getSize()))

    call_op = FakeCallOp()
    summary = summarize_store_effects(
        [FakeBlockInfo(call_op, FakeStoreOp(call_op))],
        FakeTracer(),
        FakeConditionTracker(),
        [
            _param("slot", size=8, is_signed=False, index=0, storage=_reg_storage("x0", register_name="x0")),
            _param("lhs", size=4, index=1, storage=_reg_storage("x1", size_bytes=4, register_name="w1")),
            _param("rhs", size=4, index=2, storage=_reg_storage("x2", size_bytes=4, register_name="w2")),
        ],
        direct_call_summary=lambda _target_ref, _args: EffectSummary(
            parameter_names=["a", "b"],
            effects=[],
            has_unsupported_call=False,
        ),
        direct_call_expander=lambda _target_ref, args: [
            ExpandedValue(Expression.binary_op("INT_ADD", args[0], args[1]), [])
        ],
        resolve_callee_parameters=lambda _target_ref: [
            _param("a", size=4, index=0, storage=_reg_storage("x0", size_bytes=4, register_name="w0")),
            _param("b", size=4, index=1, storage=_reg_storage("x1", size_bytes=4, register_name="w1")),
        ],
        debug=False,
    )

    assert summary.has_unsupported_call is False
    assert len(summary.effects) == 1
    assert summary.effects[0].location == _loc("slot", 0, 4)
    assert summary.effects[0].value.to_string() == "(lhs + rhs)"


def test_expression_expander_keeps_concrete_call_arg_when_canonical_candidate_is_unresolved_phi():
    class FakeAddress:
        def __init__(self, offset):
            self._offset = offset

        def getOffset(self):
            return self._offset

        def getAddressSpace(self):
            return self

        def getName(self):
            return "ram"

    class FakeSeqnum:
        def __init__(self, offset, order):
            self._target = FakeAddress(offset)
            self._order = order

        def getTarget(self):
            return self._target

        def getOrder(self):
            return self._order

    class FakeHigh:
        def __init__(self, name: str):
            self._name = name

        def getName(self):
            return self._name

        def getSymbol(self):
            return None

    class FakeVarnode:
        def __init__(self, name, size=4, def_op=None, high=None):
            self.name = name
            self._size = size
            self._def_op = def_op
            self._high = high

        def getDef(self):
            return self._def_op

        def getSize(self):
            return self._size

        def getHigh(self):
            return self._high

    class FakeOutput:
        def __init__(self, size):
            self._size = size

        def getSize(self):
            return self._size

    class FakeAddOp:
        def __init__(self):
            self._inputs = []

        def getMnemonic(self):
            return "INT_ADD"

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

    class FakeCallOp:
        def __init__(self, inputs):
            self._inputs = inputs
            self._output = FakeOutput(4)
            self._seqnum = FakeSeqnum(0x401040, 12)

        def getMnemonic(self):
            return "CALL"

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

        def getOutput(self):
            return self._output

        def getSeqnum(self):
            return self._seqnum

    target_varnode = FakeVarnode("callee_addr", size=8)
    unstable_source = FakeVarnode(
        "unstable_arg",
        size=4,
        def_op=FakeAddOp(),
        high=FakeHigh("tmp_w0"),
    )
    call_op = FakeCallOp([target_varnode, unstable_source])

    unresolved_phi = Expression.phi(
        [
            (
                Condition(Expression.binary_op("INT_EQUAL", Expression.parameter("param_1", 0, size=4), Expression.constant(0, 4))),
                Expression.unknown("call_out_of_scope:fc_wrap_add_then_bias"),
            ),
            (
                Condition(Expression.binary_op("INT_NOTEQUAL", Expression.parameter("param_1", 0, size=4), Expression.constant(0, 4))),
                Expression.unknown("call_out_of_scope:fc_bias"),
            ),
        ]
    )

    class FakeTracer:
        debug = False

        def resolve_call_target_ref(self, _varnode, **_kwargs):
            return CallTargetRef.from_name("fc_scale")

        def _get_function_name(self, _varnode):
            return "fc_scale"

        def trace_varnode(self, varnode, depth=0, use_cache=False):
            if varnode is target_varnode:
                return Expression.constant(0x401000, 8)
            if varnode is unstable_source:
                return unresolved_phi
            raise AssertionError(f"unexpected trace: {varnode}")

        def emit_unknown_event(self, **kwargs):
            raise AssertionError(f"call should have been resolved: {kwargs}")

        def _trace_pcode_op(self, *_args, **_kwargs):
            raise AssertionError("recursive tracing fallback should not run")

        def get_all_pcode_ops(self):
            return [call_op]

        def _get_storage_info_from_varnode(self, _varnode):
            return None

    captured = {}

    def resolve_call(target_ref, args):
        captured["target"] = target_ref
        captured["args"] = list(args)
        return [ExpandedValue(Expression.constant(1, 4), [])]

    expander = ExpressionExpander(
        FakeTracer(),
        condition_tracker=None,
        debug=False,
        call_resolver=resolve_call,
        parameters=[
            _param("param_1", size=4, index=0, storage=_reg_storage("a0", size_bytes=4, register_name="a0")),
        ],
        resolve_callee_parameters=lambda _target_ref: [
            _param("value", size=4, index=0, storage=_reg_storage("a0", size_bytes=4, register_name="a0")),
        ],
    )
    expander._expand_input_varnode = lambda varnode, conditions, depth: {
        unstable_source: [ExpandedValue(Expression.parameter("param_1", 0, size=4), [])],
    }[varnode]

    expanded = expander._expand_call_operation(call_op, [], depth=0, output_size=4)

    assert len(expanded) == 1
    assert captured["target"] == CallTargetRef.from_name("fc_scale")
    assert [arg.to_string() for arg in captured["args"]] == ["param_1"]


def test_summarize_store_effects_refuses_hidden_call_operands_without_object_evidence():
    class FakeAddress:
        def __init__(self, offset, space_name="ram"):
            self._offset = offset
            self._space_name = space_name

        def getOffset(self):
            return self._offset

        def getAddressSpace(self):
            return self

        def getName(self):
            return self._space_name

    class FakeSeqnum:
        def __init__(self, offset, order):
            self._target = FakeAddress(offset)
            self._order = order

        def getTarget(self):
            return self._target

        def getOrder(self):
            return self._order

    class FakeVarnode:
        def __init__(self, key, size=4, storage=None):
            self.key = key
            self._size = size
            self.storage = storage

        def getSize(self):
            return self._size

        def getDef(self):
            return None

        def getHigh(self):
            return None

    class FakeCallOp:
        def __init__(self):
            self._inputs = [
                FakeVarnode("target", size=8),
                FakeVarnode("hidden", size=4),
                FakeVarnode("lhs", size=4),
                FakeVarnode("rhs", size=4),
                FakeVarnode("bias", size=4),
            ]
            self._seqnum = FakeSeqnum(0x401100, 10)

        def getMnemonic(self):
            return "CALL"

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

        def getOutput(self):
            return None

        def getSeqnum(self):
            return self._seqnum

    class FakeBlockInfo:
        def __init__(self, op):
            self.pcode_ops = [op]

    class FakeConditionTracker:
        def get_all_valid_paths_to_block(self, _block):
            return [[]]

    class FakeTracer:
        def __init__(self, op):
            self._op = op

        def _get_function_name(self, _varnode):
            return "callee"

        def get_all_pcode_ops(self):
            return [self._op]

        def _get_storage_info_from_varnode(self, _varnode):
            return None

        def trace_varnode(self, varnode, use_cache=False):
            if varnode.key == "hidden":
                return Expression.binary_op(
                    "INT_SUB",
                    Expression.parameter("param_1", 0, size=4),
                    Expression.parameter("param_2", 1, size=4),
                )
            if varnode.key == "lhs":
                return Expression.parameter("param_1", 0, size=4)
            if varnode.key == "rhs":
                return Expression.parameter("param_2", 1, size=4)
            if varnode.key == "bias":
                return Expression.constant(1, 4)
            return Expression.constant(0x401100, 8)

    captured_args = {}
    call_op = FakeCallOp()

    def _direct_call_summary(_name, args):
        captured_args["args"] = list(args)
        return EffectSummary(parameter_names=["lhs", "rhs", "bias"], effects=[])

    summary = summarize_store_effects(
        [FakeBlockInfo(call_op)],
        FakeTracer(call_op),
        FakeConditionTracker(),
        [
            _param("param_1", size=4, is_signed=False, index=0, storage=_reg_storage("a0", size_bytes=4)),
            _param("param_2", size=4, is_signed=False, index=1, storage=_reg_storage("a1", size_bytes=4)),
            _param("param_3", size=4, is_signed=False, index=2, storage=_reg_storage("a2", size_bytes=4)),
        ],
        direct_call_summary=_direct_call_summary,
        resolve_callee_parameters=lambda _target_ref: [
            _param("lhs", size=4, is_signed=False, index=0, storage=_reg_storage("a0", size_bytes=4)),
            _param("rhs", size=4, is_signed=False, index=1, storage=_reg_storage("a1", size_bytes=4)),
            _param("bias", size=4, is_signed=False, index=2, storage=_reg_storage("a2", size_bytes=4)),
        ],
        debug=False,
    )

    assert summary.effects == []
    assert summary.has_unsupported_call is True
    assert "args" not in captured_args


def test_summarize_store_effects_propagates_phi_argument_branch_conditions_into_effects():
    class FakeAddress:
        def __init__(self, offset):
            self._offset = offset

        def getOffset(self):
            return self._offset

    class FakeSeqnum:
        def __init__(self, offset, order):
            self._target = FakeAddress(offset)
            self._order = order

        def getTarget(self):
            return self._target

        def getOrder(self):
            return self._order

    class FakeVarnode:
        def __init__(self, key, size=4):
            self.key = key
            self._size = size

        def getSize(self):
            return self._size

        def getDef(self):
            return None

        def getHigh(self):
            return None

    class FakeCallOp:
        def __init__(self):
            self._inputs = [
                FakeVarnode("target", size=8),
                FakeVarnode("ptr", size=8),
                FakeVarnode("delta", size=4),
            ]
            self._seqnum = FakeSeqnum(0x401180, 12)

        def getMnemonic(self):
            return "CALL"

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

        def getOutput(self):
            return None

        def getSeqnum(self):
            return self._seqnum

    class FakeBlockInfo:
        def __init__(self, op):
            self.pcode_ops = [op]

    class FakeConditionTracker:
        def get_all_valid_paths_to_block(self, _block):
            return [[
                Condition(
                    Expression.binary_op(
                        "INT_NOTEQUAL",
                        Expression.parameter("param_1", 0, size=8),
                        Expression.constant(0, size=8),
                    ),
                    False,
                )
            ]]

    class FakeTracer:
        def __init__(self, op):
            self._op = op

        def _get_function_name(self, _varnode):
            return "callee"

        def get_all_pcode_ops(self):
            return [self._op]

        def _get_storage_info_from_varnode(self, _varnode):
            return None

        def trace_varnode(self, varnode, use_cache=False):
            if varnode.key == "ptr":
                return Expression.parameter("param_1", 0, data_type="int *", size=8)
            if varnode.key == "delta":
                return Expression.phi(
                    [
                        (
                            Condition(
                                Expression.binary_op(
                                    "INT_EQUAL",
                                    Expression.binary_op(
                                        "INT_AND",
                                        Expression.parameter("param_2", 1, size=4),
                                        Expression.constant(1, size=4),
                                    ),
                                    Expression.constant(0, size=4),
                                ),
                                False,
                            ),
                            Expression.parameter("param_2", 1, size=4),
                        ),
                        (
                            Condition(
                                Expression.binary_op(
                                    "INT_EQUAL",
                                    Expression.binary_op(
                                        "INT_AND",
                                        Expression.parameter("param_2", 1, size=4),
                                        Expression.constant(1, size=4),
                                    ),
                                    Expression.constant(0, size=4),
                                ),
                                True,
                            ),
                            Expression.unary_op("INT_2COMP", Expression.parameter("param_2", 1, size=4)),
                        ),
                    ]
                )
            return Expression.constant(0x401180, 8)

    call_op = FakeCallOp()

    summary = summarize_store_effects(
        [FakeBlockInfo(call_op)],
        FakeTracer(call_op),
        FakeConditionTracker(),
        [
            _param("param_1", size=8, is_signed=False, index=0, storage=_reg_storage("a0", size_bytes=8)),
            _param("param_2", size=4, is_signed=True, index=1, storage=_reg_storage("a1", size_bytes=4)),
        ],
        direct_call_summary=lambda _target_ref, _args: EffectSummary(
            parameter_names=["ptr", "delta"],
            parameter_refs=[
                LocationBaseRef.parameter("ptr", index=0),
                LocationBaseRef.parameter("delta", index=1),
            ],
            effects=[
                StoreEffect(
                    location=_loc("ptr", 0, 4),
                    value=Expression.binary_op(
                        "INT_ADD",
                        Expression.memory(Expression.parameter("ptr", 0, data_type="int *", size=8), size=4),
                        Expression.parameter("delta", 1, size=4),
                    ),
                    conditions=[],
                    order_key=1,
                ),
            ],
        ),
        resolve_callee_parameters=lambda _target_ref: [
            _param("ptr", size=8, is_signed=False, index=0, storage=_reg_storage("a0", size_bytes=8)),
            _param("delta", size=4, is_signed=True, index=1, storage=_reg_storage("a1", size_bytes=4)),
        ],
        debug=False,
    )

    assert len(summary.effects) == 2
    effect_conditions = {tuple(cond.to_string() for cond in effect.conditions): effect.value.to_string() for effect in summary.effects}
    assert any("((param_2 & 1) == 0)" in " ".join(conds) for conds in effect_conditions)
    assert any("not ((param_2 & 1) == 0)" in " ".join(conds) for conds in effect_conditions)
    assert any(value == "(MEM[param_1] + param_2)" for value in effect_conditions.values())
    assert any(value == "(MEM[param_1] + (-param_2))" for value in effect_conditions.values())


def test_summarize_store_effects_reduces_phi_argument_and_path_conditions_under_active_path():
    class FakeAddress:
        def __init__(self, offset):
            self._offset = offset

        def getOffset(self):
            return self._offset

    class FakeSeqnum:
        def __init__(self, offset, order):
            self._target = FakeAddress(offset)
            self._order = order

        def getTarget(self):
            return self._target

        def getOrder(self):
            return self._order

    class FakeVarnode:
        def __init__(self, key, size=4):
            self.key = key
            self._size = size

        def getSize(self):
            return self._size

        def getDef(self):
            return None

        def getHigh(self):
            return None

    class FakeCallOp:
        def __init__(self):
            self._inputs = [
                FakeVarnode("target", size=8),
                FakeVarnode("ptr", size=8),
                FakeVarnode("delta", size=4),
            ]
            self._seqnum = FakeSeqnum(0x401188, 13)

        def getMnemonic(self):
            return "CALL"

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

        def getOutput(self):
            return None

        def getSeqnum(self):
            return self._seqnum

    class FakeBlockInfo:
        def __init__(self, op):
            self.pcode_ops = [op]

    phi_counter = Expression.phi(
        [
            (
                None,
                Expression.binary_op(
                    "INT_ADD",
                    Expression.unknown("phi_circular"),
                    Expression.constant(1, size=4),
                ),
            ),
            (
                Condition(
                    Expression.binary_op(
                        "INT_EQUAL",
                        Expression.parameter("param_1", 0, size=8),
                        Expression.constant(0, size=8),
                    ),
                    True,
                ),
                Expression.parameter("param_2", 1, size=4),
            ),
        ]
    )

    class FakeConditionTracker:
        def get_all_valid_paths_to_block(self, _block):
            return [[
                Condition(
                    Expression.binary_op(
                        "INT_NOTEQUAL",
                        Expression.parameter("param_1", 0, size=8),
                        Expression.constant(0, size=8),
                    ),
                    False,
                ),
                Condition(
                    Expression.binary_op(
                        "INT_SLESS",
                        phi_counter,
                        Expression.parameter("param_3", 2, size=4),
                    ),
                    False,
                ),
                Condition(
                    Expression.binary_op(
                        "INT_EQUAL",
                        Expression.binary_op(
                            "INT_AND",
                            phi_counter,
                            Expression.constant(1, size=4),
                        ),
                        Expression.constant(0, size=4),
                    ),
                    False,
                ),
            ]]

    class FakeTracer:
        def __init__(self, op):
            self._op = op

        def _get_function_name(self, _varnode):
            return "callee"

        def get_all_pcode_ops(self):
            return [self._op]

        def _get_storage_info_from_varnode(self, _varnode):
            return None

        def trace_varnode(self, varnode, use_cache=False):
            if varnode.key == "ptr":
                return Expression.parameter("param_1", 0, data_type="int *", size=8)
            if varnode.key == "delta":
                return phi_counter
            return Expression.constant(0x401188, 8)

    call_op = FakeCallOp()
    summary = summarize_store_effects(
        [FakeBlockInfo(call_op)],
        FakeTracer(call_op),
        FakeConditionTracker(),
        [
            _param("param_1", size=8, is_signed=False, index=0, storage=_reg_storage("a0", size_bytes=8)),
            _param("param_2", size=4, is_signed=True, index=1, storage=_reg_storage("a1", size_bytes=4)),
            _param("param_3", size=4, is_signed=True, index=2, storage=_reg_storage("a2", size_bytes=4)),
        ],
        direct_call_summary=lambda _target_ref, _args: EffectSummary(
            parameter_names=["ptr", "delta"],
            parameter_refs=[
                LocationBaseRef.parameter("ptr", index=0),
                LocationBaseRef.parameter("delta", index=1),
            ],
            effects=[
                StoreEffect(
                    location=_loc("ptr", 0, 4),
                    value=Expression.binary_op(
                        "INT_ADD",
                        Expression.memory(Expression.parameter("ptr", 0, data_type="int *", size=8), size=4),
                        Expression.parameter("delta", 1, size=4),
                    ),
                    conditions=[],
                    order_key=1,
                )
            ],
        ),
        resolve_callee_parameters=lambda _target_ref: [
            _param("ptr", size=8, is_signed=False, index=0, storage=_reg_storage("a0", size_bytes=8)),
            _param("delta", size=4, is_signed=True, index=1, storage=_reg_storage("a1", size_bytes=4)),
        ],
        debug=False,
    )

    assert len(summary.effects) == 1
    effect = summary.effects[0]
    assert effect.value.to_string() == "(MEM[param_1] + param_2)"
    cond_strings = [cond.to_string() for cond in effect.conditions]
    assert "(param_1 != 0)" in cond_strings
    assert "(param_2 < param_3)" in cond_strings
    assert "((param_2 & 1) == 0)" in cond_strings


def test_summarize_store_effects_captures_double_indirect_parameter_store():
    class FakeAddress:
        def __init__(self, offset):
            self._offset = offset

        def getOffset(self):
            return self._offset

    class FakeSeqnum:
        def __init__(self, offset, order):
            self._target = FakeAddress(offset)
            self._order = order

        def getTarget(self):
            return self._target

        def getOrder(self):
            return self._order

    class FakeVarnode:
        def __init__(self, key, size):
            self.key = key
            self._size = size

        def getSize(self):
            return self._size

    class FakeStoreOp:
        def __init__(self):
            self._inputs = [
                FakeVarnode("space", 4),
                FakeVarnode("addr", 8),
                FakeVarnode("value", 4),
            ]
            self._seqnum = FakeSeqnum(0x401200, 7)

        def getMnemonic(self):
            return "STORE"

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

        def getOutput(self):
            return None

        def getSeqnum(self):
            return self._seqnum

    class FakeBlockInfo:
        def __init__(self, op):
            self.pcode_ops = [op]

    class FakeConditionTracker:
        def get_all_valid_paths_to_block(self, _block):
            return [[]]

    class FakeTracer:
        def trace_varnode(self, varnode, use_cache=False):
            if varnode.key == "addr":
                return Expression.memory(Expression.parameter("slot", 0, size=8), size=8)
            if varnode.key == "value":
                return Expression.parameter("value", 1, size=4)
            return Expression.constant(0, 4)

    summary = summarize_store_effects(
        [FakeBlockInfo(FakeStoreOp())],
        FakeTracer(),
        FakeConditionTracker(),
        [
            _param("slot", size=8, is_signed=False, index=0),
            _param("value", size=4, index=1),
        ],
        debug=False,
    )

    assert len(summary.effects) == 1
    assert summary.effects[0].location == _loc(
        "slot",
        0,
        4,
        steps=(LocationStep("deref", 8),),
    )
    assert summary.effects[0].value.to_string() == "value"


def test_summarize_store_effects_marks_store_block_incomplete_when_paths_unavailable():
    class FakeVarnode:
        def __init__(self, key, size):
            self.key = key
            self._size = size

        def getSize(self):
            return self._size

    class FakeStoreOp:
        def __init__(self):
            self._inputs = [
                FakeVarnode("space", 4),
                FakeVarnode("addr", 8),
                FakeVarnode("value", 4),
            ]

        def getMnemonic(self):
            return "STORE"

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

    class FakeBlockInfo:
        def __init__(self, op):
            self.pcode_ops = [op]

    class FakeConditionTracker:
        def get_all_valid_paths_to_block(self, _block):
            return []

    class FakeTracer:
        def trace_varnode(self, _varnode, use_cache=False):
            raise AssertionError("path-incomplete store blocks must not be scanned")

    summary = summarize_store_effects(
        [FakeBlockInfo(FakeStoreOp())],
        FakeTracer(),
        FakeConditionTracker(),
        [_param("slot", size=8, is_signed=False, index=0)],
        debug=False,
    )

    assert summary.effects == []
    assert summary.has_unsupported_call is True
    assert summary.incomplete_reasons == ("effect_summary_path_coverage_incomplete",)


def test_summarize_store_effects_ignores_proven_unreachable_effect_block():
    class FakeVarnode:
        def __init__(self, key, size):
            self.key = key
            self._size = size

        def getSize(self):
            return self._size

    class FakeStoreOp:
        def __init__(self):
            self._inputs = [
                FakeVarnode("space", 4),
                FakeVarnode("addr", 8),
                FakeVarnode("value", 4),
            ]

        def getMnemonic(self):
            return "STORE"

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

    class FakeBlockInfo:
        def __init__(self, op):
            self.pcode_ops = [op]

    class FakeCoverage:
        status = "complete_unreachable"
        condition_paths = []

    class FakeConditionTracker:
        def get_path_coverage_to_block(self, _block):
            return FakeCoverage()

    class FakeTracer:
        def trace_varnode(self, _varnode, use_cache=False):
            raise AssertionError("unreachable effect blocks must not be scanned")

    summary = summarize_store_effects(
        [FakeBlockInfo(FakeStoreOp())],
        FakeTracer(),
        FakeConditionTracker(),
        [_param("slot", size=8, is_signed=False, index=0)],
        debug=False,
    )

    assert summary.effects == []
    assert summary.has_unsupported_call is False
    assert summary.incomplete_reasons == ()


def test_summarize_store_effects_allows_pathless_effect_free_explicit_call():
    class FakeVarnode:
        def __init__(self, key, size):
            self.key = key
            self._size = size

        def getSize(self):
            return self._size

        def getDef(self):
            return None

    class FakeCallOp:
        def __init__(self):
            self._inputs = [
                FakeVarnode("target", 8),
                FakeVarnode("lhs", 4),
                FakeVarnode("rhs", 4),
            ]

        def getMnemonic(self):
            return "CALL"

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

    class FakeBlockInfo:
        def __init__(self, op):
            self.pcode_ops = [op]

    class FakeConditionTracker:
        def get_all_valid_paths_to_block(self, _block):
            return []

    class FakeTracer:
        def resolve_call_target_ref(self, _varnode, **_kwargs):
            return CallTargetRef.from_name("effect_free")

        def trace_varnode(self, varnode, use_cache=False):
            if varnode.key == "lhs":
                return Expression.parameter("lhs", 0, size=4)
            if varnode.key == "rhs":
                return Expression.parameter("rhs", 1, size=4)
            return Expression.constant(0, max(1, varnode.getSize()))

    call_op = FakeCallOp()
    summary = summarize_store_effects(
        [FakeBlockInfo(call_op)],
        FakeTracer(),
        FakeConditionTracker(),
        [
            _param("lhs", size=4, index=0, storage=_reg_storage("x0", size_bytes=4, register_name="w0")),
            _param("rhs", size=4, index=1, storage=_reg_storage("x1", size_bytes=4, register_name="w1")),
        ],
        direct_call_summary=lambda _target_ref, _args: EffectSummary(
            parameter_names=["lhs", "rhs"],
            effects=[],
            has_unsupported_call=False,
        ),
        resolve_callee_parameters=lambda _target_ref: [
            _param("lhs", size=4, index=0, storage=_reg_storage("x0", size_bytes=4, register_name="w0")),
            _param("rhs", size=4, index=1, storage=_reg_storage("x1", size_bytes=4, register_name="w1")),
        ],
        debug=False,
    )

    assert summary.effects == []
    assert summary.has_unsupported_call is False
    assert summary.incomplete_reasons == ()


def test_summarize_store_effects_keeps_unresolved_scalar_callback_unsupported():
    class FakeVarnode:
        def __init__(self, key, size):
            self.key = key
            self._size = size

        def getSize(self):
            return self._size

    class FakeCallIndOp:
        def __init__(self):
            self._inputs = [
                FakeVarnode("target", 8),
                FakeVarnode("lhs", 4),
                FakeVarnode("rhs", 4),
            ]

        def getMnemonic(self):
            return "CALLIND"

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

    class FakeBlockInfo:
        def __init__(self, op):
            self.pcode_ops = [op]

    class FakeCoverage:
        status = "complete"
        condition_paths = [[]]

    class FakeConditionTracker:
        def get_path_coverage_to_block(self, _block):
            return FakeCoverage()

    class FakeTracer:
        def resolve_call_target_ref(self, _varnode, **_kwargs):
            return None

        def trace_varnode(self, varnode, use_cache=False):
            if varnode.key == "lhs":
                return Expression.parameter("lhs", 0, size=4)
            if varnode.key == "rhs":
                return Expression.parameter("rhs", 1, size=4)
            return Expression.parameter("callback", 2, size=8)

    summary = summarize_store_effects(
        [FakeBlockInfo(FakeCallIndOp())],
        FakeTracer(),
        FakeConditionTracker(),
        [
            _param("lhs", size=4, index=0, storage=_reg_storage("w0", size_bytes=4, register_name="w0"), data_type="int"),
            _param("rhs", size=4, index=1, storage=_reg_storage("w1", size_bytes=4, register_name="w1"), data_type="int"),
        ],
        direct_call_summary=lambda _target_ref, _args: None,
        debug=False,
    )

    assert summary.effects == []
    assert summary.has_unsupported_call is True
    assert summary.incomplete_reasons == ()


def test_summarize_store_effects_keeps_unresolved_pointer_callback_effect_unsupported():
    class FakeVarnode:
        def __init__(self, key, size):
            self.key = key
            self._size = size

        def getSize(self):
            return self._size

    class FakeCallIndOp:
        def __init__(self):
            self._inputs = [
                FakeVarnode("target", 8),
                FakeVarnode("ptr", 8),
            ]

        def getMnemonic(self):
            return "CALLIND"

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

    class FakeBlockInfo:
        def __init__(self, op):
            self.pcode_ops = [op]

    class FakeCoverage:
        status = "complete"
        condition_paths = [[]]

    class FakeConditionTracker:
        def get_path_coverage_to_block(self, _block):
            return FakeCoverage()

    class FakeTracer:
        def resolve_call_target_ref(self, _varnode, **_kwargs):
            return None

        def trace_varnode(self, varnode, use_cache=False):
            if varnode.key == "ptr":
                return Expression.parameter("ptr", 0, size=8)
            return Expression.parameter("callback", 1, size=8)

    ptr_param = _param(
        "ptr",
        size=8,
        index=0,
        storage=_reg_storage("x0", register_name="x0"),
    )
    ptr_param["data_type_obj"] = resolve_mock_data_type("int *")

    summary = summarize_store_effects(
        [FakeBlockInfo(FakeCallIndOp())],
        FakeTracer(),
        FakeConditionTracker(),
        [ptr_param],
        direct_call_summary=lambda _target_ref, _args: None,
        debug=False,
    )

    assert summary.effects == []
    assert summary.has_unsupported_call is True
    assert summary.incomplete_reasons == ()


def _summarize_unresolved_single_parameter_call(param: dict) -> EffectSummary:
    class FakeVarnode:
        def __init__(self, key, size):
            self.key = key
            self._size = size

        def getSize(self):
            return self._size

    class FakeCallIndOp:
        def __init__(self):
            self._inputs = [
                FakeVarnode("target", 8),
                FakeVarnode("arg", max(1, int(param.get("size") or 8))),
            ]

        def getMnemonic(self):
            return "CALLIND"

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

    class FakeBlockInfo:
        def __init__(self, op):
            self.pcode_ops = [op]

    class FakeCoverage:
        status = "complete"
        condition_paths = [[]]

    class FakeConditionTracker:
        def get_path_coverage_to_block(self, _block):
            return FakeCoverage()

    class FakeTracer:
        def resolve_call_target_ref(self, _varnode, **_kwargs):
            return None

        def trace_varnode(self, varnode, use_cache=False):
            if varnode.key == "arg":
                return Expression.parameter(param["name"], param["index"], size=param["size"])
            return Expression.parameter("callback", 9, size=8)

    return summarize_store_effects(
        [FakeBlockInfo(FakeCallIndOp())],
        FakeTracer(),
        FakeConditionTracker(),
        [param],
        direct_call_summary=lambda _target_ref, _args: None,
        debug=False,
    )


def test_summarize_store_effects_keeps_data_type_string_pointer_callback_unsupported():
    summary = _summarize_unresolved_single_parameter_call(
        _param(
            "ptr",
            size=8,
            index=0,
            storage=_reg_storage("x0", register_name="x0"),
            data_type="int *",
        )
    )

    assert summary.effects == []
    assert summary.has_unsupported_call is True
    assert summary.incomplete_reasons == ()


def test_summarize_store_effects_keeps_undefined_address_sized_callback_unsupported():
    summary = _summarize_unresolved_single_parameter_call(
        _param(
            "maybe_ptr",
            size=8,
            index=0,
            storage=_reg_storage("x0", register_name="x0"),
            data_type="undefined8",
        )
    )

    assert summary.effects == []
    assert summary.has_unsupported_call is True
    assert summary.incomplete_reasons == ()


def test_summarize_store_effects_keeps_missing_scalar_only_callee_summary_unsupported():
    class FakeVarnode:
        def __init__(self, key, size):
            self.key = key
            self._size = size

        def getSize(self):
            return self._size

    class FakeCallOp:
        def __init__(self):
            self._inputs = [
                FakeVarnode("target", 8),
                FakeVarnode("lhs", 4),
                FakeVarnode("rhs", 4),
            ]

        def getMnemonic(self):
            return "CALL"

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

    class FakeBlockInfo:
        def __init__(self, op):
            self.pcode_ops = [op]

    class FakeCoverage:
        status = "complete"
        condition_paths = [[]]

    class FakeConditionTracker:
        def get_path_coverage_to_block(self, _block):
            return FakeCoverage()

    class FakeTracer:
        def resolve_call_target_ref(self, _varnode, **_kwargs):
            return CallTargetRef.from_name("missing_scalar_helper")

        def trace_varnode(self, varnode, use_cache=False):
            if varnode.key == "lhs":
                return Expression.parameter("lhs", 0, size=4)
            if varnode.key == "rhs":
                return Expression.parameter("rhs", 1, size=4)
            return Expression.constant(0, max(1, varnode.getSize()))

    summary = summarize_store_effects(
        [FakeBlockInfo(FakeCallOp())],
        FakeTracer(),
        FakeConditionTracker(),
        [
            _param("lhs", size=8, index=0, storage=_reg_storage("x0", register_name="x0"), data_type="undefined8"),
            _param("rhs", size=8, index=1, storage=_reg_storage("x1", register_name="x1"), data_type="undefined8"),
        ],
        direct_call_summary=lambda _target_ref, _args: None,
        resolve_callee_parameters=lambda _target_ref: [
            _param("lhs", size=4, index=0, storage=_reg_storage("w0", size_bytes=4, register_name="w0"), data_type="int"),
            _param("rhs", size=4, index=1, storage=_reg_storage("w1", size_bytes=4, register_name="w1"), data_type="int"),
        ],
        debug=False,
    )

    assert summary.effects == []
    assert summary.has_unsupported_call is True
    assert summary.incomplete_reasons == ()


def test_summarize_store_effects_keeps_zero_arg_missing_callee_summary_unsupported():
    class FakeVarnode:
        def __init__(self, key, size):
            self.key = key
            self._size = size

        def getSize(self):
            return self._size

    class FakeCallOp:
        def __init__(self):
            self._inputs = [FakeVarnode("target", 8)]

        def getMnemonic(self):
            return "CALL"

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

    class FakeBlockInfo:
        def __init__(self, op):
            self.pcode_ops = [op]

    class FakeCoverage:
        status = "complete"
        condition_paths = [[]]

    class FakeConditionTracker:
        def get_path_coverage_to_block(self, _block):
            return FakeCoverage()

    class FakeTracer:
        def resolve_call_target_ref(self, _varnode, **_kwargs):
            return CallTargetRef.from_name("missing_zero_arg_helper")

        def trace_varnode(self, varnode, use_cache=False):
            return Expression.constant(0, max(1, varnode.getSize()))

    summary = summarize_store_effects(
        [FakeBlockInfo(FakeCallOp())],
        FakeTracer(),
        FakeConditionTracker(),
        [],
        direct_call_summary=lambda _target_ref, _args: None,
        resolve_callee_parameters=lambda _target_ref: [],
        debug=False,
    )

    assert summary.effects == []
    assert summary.has_unsupported_call is True
    assert summary.incomplete_reasons == ()


def test_summarize_store_effects_keeps_pointer_actual_to_address_sized_scalar_missing_summary_unsupported():
    class FakeVarnode:
        def __init__(self, key, size):
            self.key = key
            self._size = size

        def getSize(self):
            return self._size

    class FakeCallOp:
        def __init__(self):
            self._inputs = [
                FakeVarnode("target", 8),
                FakeVarnode("ptr", 8),
            ]

        def getMnemonic(self):
            return "CALL"

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

    class FakeBlockInfo:
        def __init__(self, op):
            self.pcode_ops = [op]

    class FakeCoverage:
        status = "complete"
        condition_paths = [[]]

    class FakeConditionTracker:
        def get_path_coverage_to_block(self, _block):
            return FakeCoverage()

    class FakeTracer:
        def resolve_call_target_ref(self, _varnode, **_kwargs):
            return CallTargetRef.from_name("missing_uintptr_helper")

        def trace_varnode(self, varnode, use_cache=False):
            if varnode.key == "ptr":
                return Expression.parameter("ptr", 0, data_type="int *", size=8)
            return Expression.constant(0, max(1, varnode.getSize()))

    summary = summarize_store_effects(
        [FakeBlockInfo(FakeCallOp())],
        FakeTracer(),
        FakeConditionTracker(),
        [
            _param("ptr", size=8, index=0, storage=_reg_storage("x0", register_name="x0"), data_type="int *"),
        ],
        direct_call_summary=lambda _target_ref, _args: None,
        resolve_callee_parameters=lambda _target_ref: [
            _param("as_int", size=8, index=0, storage=_reg_storage("x0", register_name="x0"), data_type="ulong"),
        ],
        debug=False,
    )

    assert summary.effects == []
    assert summary.has_unsupported_call is True
    assert summary.incomplete_reasons == ()


def test_summarize_store_effects_keeps_constant_actual_missing_summary_unsupported():
    class FakeVarnode:
        def __init__(self, key, size):
            self.key = key
            self._size = size

        def getSize(self):
            return self._size

        def getDef(self):
            return None

    class FakeCallOp:
        def __init__(self):
            self._inputs = [
                FakeVarnode("target", 8),
                FakeVarnode("literal", 8),
            ]

        def getMnemonic(self):
            return "CALL"

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

    class FakeBlockInfo:
        def __init__(self, op):
            self.pcode_ops = [op]

    class FakeCoverage:
        status = "complete"
        condition_paths = [[]]

    class FakeConditionTracker:
        def get_path_coverage_to_block(self, _block):
            return FakeCoverage()

    class FakeTracer:
        def resolve_call_target_ref(self, _varnode, **_kwargs):
            return CallTargetRef.from_name("missing_uintptr_helper")

        def _get_storage_info_from_varnode(self, _varnode):
            return None

        def trace_varnode(self, varnode, use_cache=False):
            if varnode.key == "literal":
                return Expression.constant(0x1234, size=8)
            return Expression.constant(0, max(1, varnode.getSize()))

    summary = summarize_store_effects(
        [FakeBlockInfo(FakeCallOp())],
        FakeTracer(),
        FakeConditionTracker(),
        [
            _param("ptr", size=8, index=0, storage=_reg_storage("x0", register_name="x0"), data_type="int *"),
        ],
        direct_call_summary=lambda _target_ref, _args: None,
        resolve_callee_parameters=lambda _target_ref: [
            _param("as_int", size=8, index=0, storage=_reg_storage("x0", register_name="x0"), data_type="ulong"),
        ],
        debug=False,
    )

    assert summary.effects == []
    assert summary.has_unsupported_call is True
    assert summary.incomplete_reasons == ()


def test_summarize_store_effects_does_not_propagate_scalar_only_unsupported_callee():
    class FakeVarnode:
        def __init__(self, key, size):
            self.key = key
            self._size = size

        def getSize(self):
            return self._size

    class FakeCallOp:
        def __init__(self):
            self._inputs = [
                FakeVarnode("target", 8),
                FakeVarnode("lhs", 4),
                FakeVarnode("rhs", 4),
            ]

        def getMnemonic(self):
            return "CALL"

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

    class FakeBlockInfo:
        def __init__(self, op):
            self.pcode_ops = [op]

    class FakeCoverage:
        status = "complete"
        condition_paths = [[]]

    class FakeConditionTracker:
        def get_path_coverage_to_block(self, _block):
            return FakeCoverage()

    class FakeTracer:
        def resolve_call_target_ref(self, _varnode, **_kwargs):
            return CallTargetRef.from_name("scalar_callback_wrapper")

        def trace_varnode(self, varnode, use_cache=False):
            if varnode.key == "lhs":
                return Expression.parameter("lhs", 0, size=4)
            if varnode.key == "rhs":
                return Expression.parameter("rhs", 1, size=4)
            return Expression.constant(0, max(1, varnode.getSize()))

    summary = summarize_store_effects(
        [FakeBlockInfo(FakeCallOp())],
        FakeTracer(),
        FakeConditionTracker(),
        [
            _param("lhs", size=8, index=0, storage=_reg_storage("x0", register_name="x0"), data_type="undefined8"),
            _param("rhs", size=8, index=1, storage=_reg_storage("x1", register_name="x1"), data_type="undefined8"),
        ],
        direct_call_summary=lambda _target_ref, _args: EffectSummary(
            parameter_names=["lhs", "rhs"],
            effects=[],
            has_unsupported_call=True,
        ),
        resolve_callee_parameters=lambda _target_ref: [
            _param("lhs", size=4, index=0, storage=_reg_storage("w0", size_bytes=4, register_name="w0"), data_type="int"),
            _param("rhs", size=4, index=1, storage=_reg_storage("w1", size_bytes=4, register_name="w1"), data_type="int"),
        ],
        debug=False,
    )

    assert summary.effects == []
    assert summary.has_unsupported_call is False
    assert summary.incomplete_reasons == ()


def test_recoverable_partial_call_summary_does_not_become_unsupported_blocker():
    class FakeVarnode:
        def __init__(self, key, size):
            self.key = key
            self._size = size

        def getSize(self):
            return self._size

    class FakeCallOp:
        def __init__(self):
            self._inputs = [
                FakeVarnode("target", 8),
                FakeVarnode("lhs", 4),
            ]

        def getMnemonic(self):
            return "CALL"

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

    class FakeBlockInfo:
        def __init__(self, op):
            self.pcode_ops = [op]

    class FakeCoverage:
        status = "complete"
        condition_paths = [[]]

    class FakeConditionTracker:
        def get_path_coverage_to_block(self, _block):
            return FakeCoverage()

    class FakeTracer:
        def resolve_call_target_ref(self, _varnode, **_kwargs):
            return CallTargetRef.from_name("effect_free_callee")

        def trace_varnode(self, varnode, use_cache=False):
            if varnode.key == "lhs":
                return Expression.parameter("lhs", 0, size=4)
            return Expression.constant(0, max(1, varnode.getSize()))

    captured_args = []

    def direct_call_summary(_target_ref, args):
        captured_args.append(tuple(args))
        return EffectSummary(parameter_names=["lhs", "rhs"], effects=[])

    summary = summarize_store_effects(
        [FakeBlockInfo(FakeCallOp())],
        FakeTracer(),
        FakeConditionTracker(),
        [
            _param("lhs", size=4, index=0, storage=_reg_storage("w0", size_bytes=4, register_name="w0")),
        ],
        direct_call_summary=direct_call_summary,
        resolve_callee_parameters=lambda _target_ref: [
            _param("lhs", size=4, index=0, storage=_reg_storage("w0", size_bytes=4, register_name="w0")),
            _param("rhs", size=4, index=1, storage=_reg_storage("w1", size_bytes=4, register_name="w1")),
        ],
        debug=False,
    )
    analysis = FunctionReturnAnalysis(
        function_name="caller",
        entry_point="0x1000",
        returns=[],
        parameters=[_param("lhs", size=4, index=0)],
        effect_summary=summary,
    )

    assert len(captured_args) == 1
    assert len(captured_args[0]) == 1
    assert summary.has_unsupported_call is False
    assert summary.incomplete_reasons == ()
    assert "unsupported_call_effect_summary" not in analysis.get_decisive_sat_unsafety_reasons()
    assert "unsupported_call_effect_summary" not in analysis.get_equivalence_blocking_unsafety_reasons()


def test_summarize_store_effects_rejects_nested_incomplete_effect_free_callee():
    class FakeVarnode:
        def __init__(self, key, size):
            self.key = key
            self._size = size

        def getSize(self):
            return self._size

    class FakeCallOp:
        def __init__(self):
            self._inputs = [
                FakeVarnode("target", 8),
                FakeVarnode("lhs", 4),
            ]

        def getMnemonic(self):
            return "CALL"

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

    class FakeBlockInfo:
        def __init__(self, op):
            self.pcode_ops = [op]

    class FakeCoverage:
        status = "complete"
        condition_paths = [[]]

    class FakeConditionTracker:
        def get_path_coverage_to_block(self, _block):
            return FakeCoverage()

    class FakeTracer:
        def resolve_call_target_ref(self, _varnode, **_kwargs):
            return CallTargetRef.from_name("incomplete_helper")

        def trace_varnode(self, varnode, use_cache=False):
            if varnode.key == "lhs":
                return Expression.parameter("lhs", 0, size=4)
            return Expression.constant(0, max(1, varnode.getSize()))

    summary = summarize_store_effects(
        [FakeBlockInfo(FakeCallOp())],
        FakeTracer(),
        FakeConditionTracker(),
        [
            _param("lhs", size=4, index=0, storage=_reg_storage("w0", size_bytes=4, register_name="w0"), data_type="int"),
        ],
        direct_call_summary=lambda _target_ref, _args: EffectSummary(
            parameter_names=["lhs"],
            effects=[],
            has_unsupported_call=False,
            incomplete_reasons=("effect_summary_path_coverage_incomplete",),
        ),
        resolve_callee_parameters=lambda _target_ref: [
            _param("lhs", size=4, index=0, storage=_reg_storage("w0", size_bytes=4, register_name="w0"), data_type="int"),
        ],
        debug=False,
    )

    assert summary.effects == []
    assert summary.has_unsupported_call is True
    assert summary.incomplete_reasons == ()


def test_summarize_store_effects_keeps_pathless_side_effect_call_incomplete():
    class FakeVarnode:
        def __init__(self, key, size):
            self.key = key
            self._size = size

        def getSize(self):
            return self._size

    class FakeCallOp:
        def __init__(self):
            self._inputs = [
                FakeVarnode("target", 8),
                FakeVarnode("ptr", 8),
            ]

        def getMnemonic(self):
            return "CALL"

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

    class FakeBlockInfo:
        def __init__(self, op):
            self.pcode_ops = [op]

    class FakeConditionTracker:
        def get_all_valid_paths_to_block(self, _block):
            return []

    class FakeTracer:
        def resolve_call_target_ref(self, _varnode, **_kwargs):
            return CallTargetRef.from_name("writer")

        def trace_varnode(self, varnode, use_cache=False):
            if varnode.key == "ptr":
                return Expression.parameter("ptr", 0, size=8)
            return Expression.constant(0, max(1, varnode.getSize()))

    call_op = FakeCallOp()
    summary = summarize_store_effects(
        [FakeBlockInfo(call_op)],
        FakeTracer(),
        FakeConditionTracker(),
        [_param("ptr", size=8, index=0, storage=_reg_storage("x0", register_name="x0"))],
        direct_call_summary=lambda _target_ref, _args: EffectSummary(
            parameter_names=["ptr"],
            effects=[
                StoreEffect(
                    location=_loc("ptr", 0, 4),
                    value=Expression.constant(7, 4),
                    conditions=[],
                    order_key=1,
                )
            ],
        ),
        resolve_callee_parameters=lambda _target_ref: [
            _param("ptr", size=8, index=0, storage=_reg_storage("x0", register_name="x0")),
        ],
        debug=False,
    )

    assert summary.effects == []
    assert summary.has_unsupported_call is True
    assert summary.incomplete_reasons == ("effect_summary_path_coverage_incomplete",)


def test_effect_summary_path_coverage_note_is_sat_unsafe():
    analysis = FunctionReturnAnalysis(
        function_name="path_incomplete_store",
        entry_point="0x5000",
        parameters=[],
        returns=[
            ReturnInfo(
                address="0x5000",
                value=Expression.constant(0, 4),
                conditions=[],
            )
        ],
        effect_summary=EffectSummary(
            parameter_names=[],
            effects=[],
            has_unsupported_call=True,
            incomplete_reasons=("effect_summary_path_coverage_incomplete",),
        ),
    )

    reasons = analysis.get_decisive_sat_unsafety_reasons()
    assert "effect_summary_path_coverage_incomplete" in reasons
    assert "unsupported_call_effect_summary" in reasons


def test_effect_summary_accepts_mul_by_one_wrapped_parameter_addresses():
    addr_expr = Expression.binary_op(
        "INT_MULT",
        Expression.constant(1, 8),
        Expression.binary_op(
            "INT_ADD",
            Expression.parameter("box", 0, size=8),
            Expression.constant(4, 8),
        ),
    )

    location = canonicalize_param_location(
        addr_expr,
        [_param("box", size=8, is_signed=False)],
        size=4,
    )

    assert location == _loc("box", 4, 4)


def test_effect_summary_accepts_subpiece_lower_parameter_addresses():
    ptr = Expression.parameter("ptr", 0, size=8)
    addr_expr = Expression.unary_op(
        "INT_ZEXT",
        Expression.binary_op("SUBPIECE", ptr, Expression.constant(0, 4)),
    )
    addr_expr.size = 8

    location = canonicalize_param_location(
        addr_expr,
        [_param("ptr", size=8, is_signed=False)],
        size=4,
    )

    assert location == _loc("ptr", 0, 4)


def test_effect_summary_accepts_ptradd_style_constant_offsets():
    ptr = Expression.parameter("ptr", 0, size=8)
    addr_expr = Expression.binary_op(
        "INT_ADD",
        ptr,
        Expression.binary_op(
            "INT_MULT",
            Expression.constant(1, 8),
            Expression.constant(4, 8),
        ),
    )

    location = canonicalize_param_location(
        addr_expr,
        [_param("ptr", size=8, is_signed=False)],
        size=4,
    )

    assert location == _loc("ptr", 4, 4)


def test_normalize_post_state_expression_composes_same_location_increment_effects():
    ptr = Expression.parameter("ptr", 0, size=8)
    field = Expression.binary_op(
        "INT_ADD",
        ptr,
        Expression.binary_op(
            "INT_MULT",
            Expression.constant(1, 8),
            Expression.constant(4, 8),
        ),
    )
    field_load = Expression.memory(field, size=4)
    expr = Expression.binary_op("INT_ADD", field_load, Expression.constant(7, 4))
    effects = [
        StoreEffect(
            location=_loc("ptr", 4, 4),
            value=Expression.binary_op("INT_ADD", Expression.memory(field, size=4), Expression.constant(1, 4)),
            conditions=[],
            order_key=1,
        ),
        StoreEffect(
            location=_loc("ptr", 4, 4),
            value=Expression.binary_op("INT_ADD", Expression.memory(field, size=4), Expression.constant(1, 4)),
            conditions=[],
            order_key=2,
        ),
    ]

    normalized = normalize_post_state_expression(
        expr,
        [],
        effects,
        [_param("ptr", size=8, is_signed=False)],
        prefer_canonical_post_state=False,
    )

    assert normalized is not None
    assert normalized.to_string() == "(((MEM[(ptr + 4)] + 1) + 1) + 7)"


def test_effect_summary_keeps_load_when_multiple_writes_overlap():
    ptr = Expression.parameter("ptr", 0, size=8)
    original = Expression.memory(ptr, size=4)
    effects = [
        StoreEffect(
            location=_loc("ptr", 0, 4),
            value=Expression.constant(1, 4),
            conditions=[],
            order_key=2,
        ),
        StoreEffect(
            location=_loc("ptr", 0, 4),
            value=Expression.constant(2, 4),
            conditions=[],
            order_key=1,
        ),
    ]

    rewritten = rewrite_loads_from_effects(
        original,
        [],
        effects,
        [_param("ptr", size=8, is_signed=False)],
    )

    assert rewritten.expr_type.name == "MEMORY"


def test_effect_summary_skips_effects_that_contradict_return_conditions():
    ptr = Expression.parameter("ptr", 0, size=8)
    flag = Expression.parameter("flag", 1, size=4)
    original = Expression.memory(ptr, size=4)
    positive = Condition(
        Expression.binary_op("INT_NOTEQUAL", flag, Expression.constant(0, 4)),
        False,
    )
    negative = positive.negate()
    effects = [
        StoreEffect(
            location=_loc("ptr", 0, 4),
            value=Expression.parameter("v_true", 2, size=4),
            conditions=[positive],
            order_key=2,
        ),
        StoreEffect(
            location=_loc("ptr", 0, 4),
            value=Expression.parameter("v_false", 3, size=4),
            conditions=[negative],
            order_key=1,
        ),
    ]

    rewritten = rewrite_loads_from_effects(
        original,
        [positive],
        effects,
        [
            _param("ptr", size=8, is_signed=False),
            _param("flag", size=4, index=1),
            _param("v_true", size=4, index=2),
            _param("v_false", size=4, index=3),
        ],
    )

    assert rewritten.to_string() == "v_true"


def test_effect_summary_does_not_reapply_self_referential_store():
    box = Expression.parameter("box", 0, size=8)
    delta = Expression.parameter("delta", 1, size=4)
    right_addr = Expression.binary_op("INT_ADD", box, Expression.constant(4, 8))
    original = Expression.binary_op("INT_ADD", Expression.memory(right_addr, size=4), delta)
    effect = StoreEffect(
        location=_loc("box", 4, 4),
        value=Expression.binary_op("INT_ADD", Expression.memory(right_addr, size=4), delta),
        conditions=[],
        order_key=3,
    )

    rewritten = rewrite_loads_from_effects(
        original,
        [],
        [effect],
        [_param("box", size=8, is_signed=False), _param("delta", size=4, index=1)],
    )

    assert rewritten.to_string() == "(MEM[(box + 4)] + delta)"


def test_effect_summary_does_not_reapply_commuted_self_referential_store():
    box = Expression.parameter("box", 0, size=8)
    delta = Expression.parameter("delta", 1, size=4)
    right_addr = Expression.binary_op("INT_ADD", box, Expression.constant(4, 8))
    original = Expression.binary_op("INT_ADD", delta, Expression.memory(right_addr, size=4))
    effect = StoreEffect(
        location=_loc("box", 4, 4),
        value=Expression.binary_op("INT_ADD", Expression.memory(right_addr, size=4), delta),
        conditions=[],
        order_key=3,
    )

    rewritten = rewrite_loads_from_effects(
        original,
        [],
        [effect],
        [_param("box", size=8, is_signed=False), _param("delta", size=4, index=1)],
    )

    assert rewritten.to_string() == "(delta + MEM[(box + 4)])"


def test_normalize_post_state_expression_does_not_replay_existing_effect_value_twice():
    trace = Expression.parameter("trace", 0, size=8)
    trace_nonnull = Condition(
        Expression.binary_op("INT_NOTEQUAL", trace, Expression.constant(0, 8)),
        False,
    )
    steps_addr = Expression.binary_op("INT_ADD", trace, Expression.constant(4, 8))
    already_replayed = Expression.binary_op(
        "INT_ADD",
        Expression.memory(steps_addr, size=4),
        Expression.constant(1, 4),
    )

    normalized = normalize_post_state_expression(
        already_replayed,
        [trace_nonnull],
        [
            StoreEffect(
                location=_loc("trace", 4, 4),
                value=already_replayed,
                conditions=[trace_nonnull],
                order_key=1,
            ),
            StoreEffect(
                location=_loc("trace", 4, 4),
                value=already_replayed,
                conditions=[trace_nonnull],
                order_key=2,
            ),
        ],
        [_param("trace", size=8, is_signed=False)],
        prefer_canonical_post_state=False,
    )

    assert normalized is not None
    assert normalized.to_string() == "(MEM[(trace + 4)] + 1)"


def test_lower_post_state_expression_for_smt_keeps_materialized_object_state_value_atomic():
    dst = Expression.parameter("dst", 0, size=8)
    src = Expression.parameter("src", 1, size=8)
    copy_flag = Expression.parameter("copy_flag", 2, size=4)
    dst_nonnull = Condition(
        Expression.binary_op("INT_NOTEQUAL", dst, Expression.constant(0, 8)),
        False,
    )
    src_nonnull = Condition(
        Expression.binary_op("INT_NOTEQUAL", src, Expression.constant(0, 8)),
        False,
    )
    accumulate_taken = Condition(
        Expression.binary_op("INT_EQUAL", copy_flag, Expression.constant(0, 4)),
        False,
    )
    accumulated = Expression.binary_op(
        "INT_ADD",
        Expression.memory(dst, size=4),
        Expression.memory(src, size=4),
    )
    effects = [
        StoreEffect(
            location=_loc("dst", 0, 4),
            value=accumulated,
            conditions=[dst_nonnull, src_nonnull, accumulate_taken],
            order_key=7,
        ),
    ]
    params = [
        _param("dst", size=8, is_signed=False),
        _param("src", size=8, is_signed=False, index=1),
        _param("copy_flag", size=4, is_signed=False, index=2),
    ]

    symbolic_value = post_state_read_expression_for_location(
        _loc("dst", 0, 4),
        params,
        symbolic=True,
    )

    normalized = lower_post_state_expression_for_smt(
        symbolic_value,
        [dst_nonnull, src_nonnull, accumulate_taken],
        effects,
        params,
    )

    assert normalized is not None
    assert normalized.to_string() == "(MEM[dst] + MEM[src])"
    assert isinstance(getattr(normalized, "runtime_ref", None), PostStateValueRef)
    assert normalized.runtime_ref.location == _loc("dst", 0, 4)

    lowered = lower_post_state_expression_for_smt(
        normalized,
        [dst_nonnull, src_nonnull, accumulate_taken],
        effects,
        params,
    )

    assert lowered is not None
    assert lowered.to_string() == "(MEM[dst] + MEM[src])"


def test_lower_post_state_expression_for_smt_materializes_matching_composite_effect_value_before_replay():
    dst = Expression.parameter("dst", 0, size=8)
    src = Expression.parameter("src", 1, size=8)
    copy_flag = Expression.parameter("copy_flag", 2, size=4)
    dst_nonnull = Condition(
        Expression.binary_op("INT_NOTEQUAL", dst, Expression.constant(0, 8)),
        False,
    )
    src_nonnull = Condition(
        Expression.binary_op("INT_NOTEQUAL", src, Expression.constant(0, 8)),
        False,
    )
    accumulate_taken = Condition(
        Expression.binary_op("INT_EQUAL", copy_flag, Expression.constant(0, 4)),
        False,
    )
    expr = Expression.binary_op(
        "INT_ADD",
        Expression.memory(dst, size=4, runtime_ref=_loc("dst", 0, 4)),
        Expression.memory(src, size=4, runtime_ref=_loc("src", 0, 4)),
    )
    effects = [
        StoreEffect(
            location=_loc("dst", 0, 4),
            value=Expression.binary_op(
                "INT_ADD",
                Expression.memory(dst, size=4, read_order_key=10),
                Expression.memory(src, size=4, read_order_key=11),
            ),
            conditions=[dst_nonnull, src_nonnull, accumulate_taken],
            order_key=7,
        ),
    ]
    params = [
        _param("dst", size=8, is_signed=False),
        _param("src", size=8, is_signed=False, index=1),
        _param("copy_flag", size=4, is_signed=False, index=2),
    ]

    lowered = lower_post_state_expression_for_smt(
        expr,
        [dst_nonnull, src_nonnull, accumulate_taken],
        effects,
        params,
    )

    assert lowered is not None
    assert lowered.to_string() == "(MEM[dst] + MEM[src])"
    assert isinstance(getattr(lowered, "runtime_ref", None), PostStateValueRef)
    assert lowered.runtime_ref.location == _loc("dst", 0, 4)


def test_call_effect_summary_policy_accepts_interdependent_swap_writes():
    summary = EffectSummary(
        parameter_names=["a", "b"],
        effects=[
            StoreEffect(
                location=_loc("a", 0, 4),
                value=Expression.memory(Expression.parameter("b", 1, size=8), size=4),
                conditions=[],
                order_key=1,
            ),
            StoreEffect(
                location=_loc("b", 0, 4),
                value=Expression.memory(Expression.parameter("a", 0, size=8), size=4),
                conditions=[],
                order_key=2,
            ),
        ],
    )

    assert is_call_effect_summary_allowed(summary)


def test_effect_summary_does_not_rebind_no_index_location_by_parameter_name():
    unresolved_location = CanonicalLocation(
        base_ref=LocationBaseRef.parameter("dst"),
        offset=0,
        size=4,
    )

    summary = EffectSummary(
        parameter_names=["dst", "dst"],
        effects=[
            StoreEffect(
                location=unresolved_location,
                value=Expression.constant(1, size=4),
                conditions=[],
                order_key=1,
            )
        ],
    )

    bound_ref = summary.effects[0].location.base_ref
    assert isinstance(bound_ref, LocationBaseRef)
    assert bound_ref.is_parameter()
    assert bound_ref.parameter_index is None


def test_effect_summary_rewrites_swap_branch_using_pre_store_values():
    a = Expression.parameter("a", 0, size=8)
    b = Expression.parameter("b", 1, size=8)
    original = Expression.binary_op("INT_SUB", Expression.memory(a, size=4), Expression.memory(b, size=4))
    swap_taken = Condition(
        Expression.binary_op("INT_SLESS", Expression.memory(b, size=4), Expression.memory(a, size=4)),
        False,
    )
    effects = [
        StoreEffect(
            location=_loc("a", 0, 4),
            value=Expression.memory(b, size=4),
            conditions=[swap_taken],
            order_key=1,
        ),
        StoreEffect(
            location=_loc("b", 0, 4),
            value=Expression.memory(a, size=4),
            conditions=[swap_taken],
            order_key=2,
        ),
    ]

    rewritten = rewrite_loads_from_effects(
        original,
        [swap_taken],
        effects,
        [
            _param("a", size=8, is_signed=False),
            _param("b", size=8, is_signed=False, index=1),
        ],
    )

    assert rewritten.to_string() == "(MEM[b] - MEM[a])"


def test_effect_summary_rewrites_observed_post_call_loads_into_phi_difference():
    a = Expression.parameter("a", 0, size=8)
    b = Expression.parameter("b", 1, size=8)
    nonnull_a = Condition(Expression.binary_op("INT_NOTEQUAL", a, Expression.constant(0, 8)), False)
    nonnull_b = Condition(Expression.binary_op("INT_NOTEQUAL", b, Expression.constant(0, 8)), False)
    original = Expression.binary_op(
        "INT_SUB",
        Expression.memory(a, size=4, read_order_key=20),
        Expression.memory(b, size=4, read_order_key=21),
    )
    swap_taken = Condition(
        Expression.binary_op("INT_SLESS", Expression.memory(b, size=4), Expression.memory(a, size=4)),
        False,
    )
    effects = [
        StoreEffect(
            location=_loc("a", 0, 4),
            value=Expression.memory(b, size=4),
            conditions=[swap_taken],
            order_key=10,
        ),
        StoreEffect(
            location=_loc("b", 0, 4),
            value=Expression.memory(a, size=4),
            conditions=[swap_taken],
            order_key=11,
        ),
    ]

    rewritten = rewrite_observed_loads_from_effects(
        original,
        [nonnull_a, nonnull_b],
        effects,
        [
            _param("a", size=8, is_signed=False),
            _param("b", size=8, is_signed=False, index=1),
        ],
    )

    assert rewritten.to_string() == "(PHI(MEM[b] if (MEM[b] < MEM[a]), MEM[a]) - PHI(MEM[a] if (MEM[b] < MEM[a]), MEM[b]))"


def test_effect_summary_collapses_post_state_phi_to_canonical_memory_location():
    a = Expression.parameter("a", 0, size=8)
    b = Expression.parameter("b", 1, size=8)
    swap_taken = Condition(
        Expression.binary_op("INT_SLESS", Expression.memory(b, size=4), Expression.memory(a, size=4)),
        False,
    )
    post_swap_b = Expression.phi(
        [
            (swap_taken, Expression.memory(a, size=4)),
            (None, Expression.memory(b, size=4)),
        ]
    )
    post_swap_b.size = 4
    effects = [
        StoreEffect(
            location=_loc("a", 0, 4),
            value=Expression.memory(b, size=4),
            conditions=[swap_taken],
            order_key=1,
        ),
        StoreEffect(
            location=_loc("b", 0, 4),
            value=Expression.memory(a, size=4),
            conditions=[swap_taken],
            order_key=2,
        ),
    ]

    collapsed = collapse_post_state_expr_to_canonical_memory(
        post_swap_b,
        effects,
        [
            _param("a", size=8, is_signed=False),
            _param("b", size=8, is_signed=False, index=1),
        ],
    )

    assert collapsed is not None
    assert collapsed.to_string() == "MEM[b]"


def test_expression_expander_collapses_nested_multiequal_matching_effect_post_state():
    a = Expression.parameter("a", 0, size=8)
    b = Expression.parameter("b", 1, size=8)
    swap_taken = Condition(
        Expression.binary_op("INT_SLESS", Expression.memory(b, size=4), Expression.memory(a, size=4)),
        False,
    )
    post_swap_b = Expression.phi(
        [
            (swap_taken, Expression.memory(a, size=4)),
            (None, Expression.memory(b, size=4)),
        ]
    )
    post_swap_b.size = 4
    effect_summary = EffectSummary(
        parameter_names=["a", "b"],
        effects=[
            StoreEffect(
                location=_loc("a", 0, 4),
                value=Expression.memory(b, size=4),
                conditions=[swap_taken],
                order_key=1,
            ),
            StoreEffect(
                location=_loc("b", 0, 4),
                value=Expression.memory(a, size=4),
                conditions=[swap_taken],
                order_key=2,
            ),
        ],
    )

    class FakeMultiequalOp:
        def getMnemonic(self):
            return "MULTIEQUAL"

    class FakeVarnode:
        def __init__(self, def_op):
            self._def_op = def_op

        def getSize(self):
            return 4

        def getDef(self):
            return self._def_op

    class FakeTracer:
        def _trace_pcode_op(self, _op, depth=0, use_cache=False):
            return post_swap_b

    expander = ExpressionExpander(
        FakeTracer(),
        condition_tracker=None,
        debug=False,
        effect_summary=effect_summary,
        parameters=[
            _param("a", size=8, is_signed=False),
            _param("b", size=8, is_signed=False, index=1),
        ],
    )

    expanded = expander._expand_input_varnode(
        FakeVarnode(FakeMultiequalOp()),
        [],
        depth=0,
    )

    assert len(expanded) == 1
    assert expanded[0].value.to_string() == "MEM[b]"


def test_effect_summary_collapses_post_state_phi_with_explicit_complementary_guards():
    a = Expression.parameter("a", 0, size=8)
    b = Expression.parameter("b", 1, size=8)
    swap_taken = Condition(
        Expression.binary_op("INT_SLESS", Expression.memory(b, size=4), Expression.memory(a, size=4)),
        False,
    )
    no_swap = Condition(swap_taken.expression, True)
    post_swap_b = Expression.phi(
        [
            (swap_taken, Expression.memory(a, size=4)),
            (no_swap, Expression.memory(b, size=4)),
        ]
    )
    post_swap_b.size = 4
    effects = [
        StoreEffect(
            location=_loc("a", 0, 4),
            value=Expression.memory(b, size=4),
            conditions=[swap_taken],
            order_key=1,
        ),
        StoreEffect(
            location=_loc("b", 0, 4),
            value=Expression.memory(a, size=4),
            conditions=[swap_taken],
            order_key=2,
        ),
    ]

    collapsed = collapse_post_state_expr_to_canonical_memory(
        post_swap_b,
        effects,
        [
            _param("a", size=8, is_signed=False),
            _param("b", size=8, is_signed=False, index=1),
        ],
        return_conditions=[swap_taken],
    )

    assert collapsed is not None
    assert collapsed.to_string() == "MEM[b]"


def test_effect_summary_collapses_pruned_post_state_memory_leaf_to_canonical_location():
    a = Expression.parameter("a", 0, size=8)
    b = Expression.parameter("b", 1, size=8)
    swap_taken = Condition(
        Expression.binary_op("INT_SLESS", Expression.memory(b, size=4), Expression.memory(a, size=4)),
        False,
    )
    effects = [
        StoreEffect(
            location=_loc("a", 0, 4),
            value=Expression.memory(b, size=4),
            conditions=[swap_taken],
            order_key=1,
        ),
        StoreEffect(
            location=_loc("b", 0, 4),
            value=Expression.memory(a, size=4),
            conditions=[swap_taken],
            order_key=2,
        ),
    ]

    collapsed = collapse_pruned_post_state_memory_leaf_to_canonical_memory(
        Expression.memory(a, size=4),
        effects,
        [
            _param("a", size=8, is_signed=False),
            _param("b", size=8, is_signed=False, index=1),
        ],
        return_conditions=[swap_taken],
    )

    assert collapsed is not None
    assert collapsed.to_string() == "MEM[b]"


def test_effect_summary_generalized_collapse_resolves_raw_post_state_memory_leaf():
    a = Expression.parameter("a", 0, size=8)
    b = Expression.parameter("b", 1, size=8)
    swap_taken = Condition(
        Expression.binary_op("INT_SLESS", Expression.memory(b, size=4), Expression.memory(a, size=4)),
        False,
    )
    effects = [
        StoreEffect(
            location=_loc("a", 0, 4),
            value=Expression.memory(b, size=4),
            conditions=[swap_taken],
            order_key=1,
        ),
        StoreEffect(
            location=_loc("b", 0, 4),
            value=Expression.memory(a, size=4),
            conditions=[swap_taken],
            order_key=2,
        ),
    ]

    collapsed = collapse_post_state_expr_to_canonical_memory(
        Expression.memory(a, size=4),
        effects,
        [
            _param("a", size=8, is_signed=False),
            _param("b", size=8, is_signed=False, index=1),
        ],
        return_conditions=[swap_taken],
    )

    assert collapsed is not None
    assert collapsed.to_string() == "MEM[b]"


def test_expression_expander_collapses_nested_multiequal_using_active_conditions():
    a = Expression.parameter("a", 0, size=8)
    b = Expression.parameter("b", 1, size=8)
    swap_taken = Condition(
        Expression.binary_op("INT_SLESS", Expression.memory(b, size=4), Expression.memory(a, size=4)),
        False,
    )
    no_swap = Condition(swap_taken.expression, True)
    post_swap_b = Expression.phi(
        [
            (swap_taken, Expression.memory(a, size=4)),
            (no_swap, Expression.memory(b, size=4)),
        ]
    )
    post_swap_b.size = 4
    effect_summary = EffectSummary(
        parameter_names=["a", "b"],
        effects=[
            StoreEffect(
                location=_loc("a", 0, 4),
                value=Expression.memory(b, size=4),
                conditions=[swap_taken],
                order_key=1,
            ),
            StoreEffect(
                location=_loc("b", 0, 4),
                value=Expression.memory(a, size=4),
                conditions=[swap_taken],
                order_key=2,
            ),
        ],
    )

    class FakeMultiequalOp:
        def getMnemonic(self):
            return "MULTIEQUAL"

    class FakeVarnode:
        def __init__(self, def_op):
            self._def_op = def_op

        def getSize(self):
            return 4

        def getDef(self):
            return self._def_op

    class FakeTracer:
        def _trace_pcode_op(self, _op, depth=0, use_cache=False):
            return post_swap_b

    expander = ExpressionExpander(
        FakeTracer(),
        condition_tracker=None,
        debug=False,
        effect_summary=effect_summary,
        parameters=[
            _param("a", size=8, is_signed=False),
            _param("b", size=8, is_signed=False, index=1),
        ],
    )

    expanded = expander._expand_input_varnode(
        FakeVarnode(FakeMultiequalOp()),
        [swap_taken],
        depth=0,
    )

    assert len(expanded) == 1
    assert expanded[0].value.to_string() == "MEM[b]"


def test_expression_expander_canonicalizes_top_level_phi_input_using_effects():
    a = Expression.parameter("a", 0, size=8)
    b = Expression.parameter("b", 1, size=8)
    nonnull = Condition.combine_and(
        [
            Condition(Expression.binary_op("INT_NOTEQUAL", a, Expression.constant(0, 8)), False),
            Condition(Expression.binary_op("INT_NOTEQUAL", b, Expression.constant(0, 8)), False),
        ]
    )
    swap_taken = Condition(
        Expression.binary_op("INT_SLESS", Expression.memory(b, size=4), Expression.memory(a, size=4)),
        False,
    )
    no_swap = Condition(swap_taken.expression, True)
    expr = Expression.binary_op(
        "INT_SUB",
        Expression.memory(a, size=4),
        Expression.phi(
            [
                (Condition.combine_and([nonnull, swap_taken]), Expression.memory(a, size=4)),
                (Condition.combine_and([nonnull, no_swap]), Expression.memory(b, size=4)),
            ]
        ),
    )
    expr.operands[1].size = 4
    effect_summary = EffectSummary(
        parameter_names=["a", "b"],
        effects=[
            StoreEffect(
                location=_loc("a", 0, 4),
                value=Expression.memory(b, size=4),
                conditions=[swap_taken],
                order_key=1,
            ),
            StoreEffect(
                location=_loc("b", 0, 4),
                value=Expression.memory(a, size=4),
                conditions=[swap_taken],
                order_key=2,
            ),
        ],
    )

    class FakeTracer:
        def trace_varnode(self, _varnode, depth=0, use_cache=False):
            return expr

        def _trace_pcode_op(self, _op, depth=0, use_cache=False):
            return expr

    expander = ExpressionExpander(
        FakeTracer(),
        condition_tracker=None,
        debug=False,
        effect_summary=effect_summary,
        parameters=[
            _param("a", size=8, is_signed=False),
            _param("b", size=8, is_signed=False, index=1),
        ],
    )

    conds = [
        Condition(Expression.binary_op("INT_NOTEQUAL", a, Expression.constant(0, 8)), False),
        Condition(Expression.binary_op("INT_NOTEQUAL", b, Expression.constant(0, 8)), False),
        swap_taken,
    ]
    canonicalized = expander._trace_and_canonicalize_input_value(object(), conds, 0)

    assert canonicalized is not None
    assert canonicalized.to_string() == "(MEM[a] - MEM[b])"


def test_expression_expander_canonicalizes_multiequal_branch_memory_leaf_using_effects():
    a = Expression.parameter("a", 0, size=8)
    b = Expression.parameter("b", 1, size=8)
    swap_taken = Condition(
        Expression.binary_op("INT_SLESS", Expression.memory(b, size=4), Expression.memory(a, size=4)),
        False,
    )
    effect_summary = EffectSummary(
        parameter_names=["a", "b"],
        effects=[
            StoreEffect(
                location=_loc("a", 0, 4),
                value=Expression.memory(b, size=4),
                conditions=[swap_taken],
                order_key=1,
            ),
            StoreEffect(
                location=_loc("b", 0, 4),
                value=Expression.memory(a, size=4),
                conditions=[swap_taken],
                order_key=2,
            ),
        ],
    )

    class FakeTracer:
        def trace_varnode(self, _varnode, depth=0, use_cache=False):
            return Expression.memory(a, size=4)

    expander = ExpressionExpander(
        FakeTracer(),
        condition_tracker=None,
        debug=False,
        effect_summary=effect_summary,
        parameters=[
            _param("a", size=8, is_signed=False),
            _param("b", size=8, is_signed=False, index=1),
        ],
    )

    canonicalized = expander._trace_and_canonicalize_input_value(object(), [swap_taken], 0)

    assert canonicalized is not None
    assert canonicalized.to_string() == "MEM[b]"


def test_collapse_post_state_read_preserves_root_object_identity():
    a = Expression.parameter("a", 0, size=8)
    b = Expression.parameter("b", 1, size=8)
    swap_taken = Condition(
        Expression.binary_op("INT_SLESS", Expression.memory(b, size=4), Expression.memory(a, size=4)),
        False,
    )
    effects = [
        StoreEffect(
            location=_loc("a", 0, 4),
            value=Expression.memory(b, size=4),
            conditions=[swap_taken],
            order_key=1,
        ),
        StoreEffect(
            location=_loc("b", 0, 4),
            value=Expression.memory(a, size=4),
            conditions=[swap_taken],
            order_key=2,
        ),
    ]
    params = [
        _param("a", size=8, is_signed=False),
        _param("b", size=8, is_signed=False, index=1),
    ]
    post_state_b = post_state_read_expression_for_location(
        _loc("b", 0, 4),
        params,
        symbolic=True,
    )

    collapsed = collapse_post_state_expr_to_canonical_memory(
        post_state_b,
        effects,
        params,
        return_conditions=[swap_taken],
    )

    assert collapsed is not None
    assert collapsed.to_string() == "MEM[b]"


def test_effect_summary_treats_composite_guard_as_implied_by_split_active_conditions():
    a = Expression.parameter("a", 0, size=8)
    b = Expression.parameter("b", 1, size=8)
    nonnull_a = Condition(Expression.binary_op("INT_NOTEQUAL", a, Expression.constant(0, 8)), False)
    nonnull_b = Condition(Expression.binary_op("INT_NOTEQUAL", b, Expression.constant(0, 8)), False)
    swap_taken = Condition(
        Expression.binary_op("INT_SLESS", Expression.memory(b, size=4), Expression.memory(a, size=4)),
        False,
    )
    composite = Condition.combine_and([nonnull_a, nonnull_b, swap_taken])

    residual = subtract_implied_conditions([composite], [nonnull_a, nonnull_b, swap_taken])

    assert residual == []


def test_effect_summary_treats_composite_guard_as_implied_by_grouped_active_conditions():
    a = Expression.parameter("a", 0, size=8)
    b = Expression.parameter("b", 1, size=8)
    nonnull_a = Condition(Expression.binary_op("INT_NOTEQUAL", a, Expression.constant(0, 8)), False)
    nonnull_b = Condition(Expression.binary_op("INT_NOTEQUAL", b, Expression.constant(0, 8)), False)
    nonnull = Condition.combine_and([nonnull_a, nonnull_b])
    swap_taken = Condition(
        Expression.binary_op("INT_SLESS", Expression.memory(b, size=4), Expression.memory(a, size=4)),
        False,
    )
    composite = Condition.combine_and([nonnull, swap_taken])

    residual = subtract_implied_conditions([composite], [nonnull, swap_taken])

    assert residual == []


def test_canonicalize_post_state_subexpressions_handles_composite_guard_without_self_subtraction():
    a = Expression.parameter("a", 0, size=8)
    b = Expression.parameter("b", 1, size=8)
    nonnull_a = Condition(Expression.binary_op("INT_NOTEQUAL", a, Expression.constant(0, 8)), False)
    nonnull_b = Condition(Expression.binary_op("INT_NOTEQUAL", b, Expression.constant(0, 8)), False)
    swap_taken = Condition(
        Expression.binary_op("INT_SLESS", Expression.memory(b, size=4), Expression.memory(a, size=4)),
        False,
    )
    no_swap = Condition(swap_taken.expression, True)
    expr = Expression.binary_op(
        "INT_SUB",
        Expression.memory(a, size=4),
        Expression.phi(
            [
                (Condition.combine_and([nonnull_a, nonnull_b, swap_taken]), Expression.memory(a, size=4)),
                (Condition.combine_and([nonnull_a, nonnull_b, no_swap]), Expression.memory(b, size=4)),
            ]
        ),
    )
    expr.operands[1].size = 4
    effects = [
        StoreEffect(
            location=_loc("a", 0, 4),
            value=Expression.memory(b, size=4),
            conditions=[swap_taken],
            order_key=1,
        ),
        StoreEffect(
            location=_loc("b", 0, 4),
            value=Expression.memory(a, size=4),
            conditions=[swap_taken],
            order_key=2,
        ),
    ]

    normalized = canonicalize_post_state_subexpressions(
        expr,
        [nonnull_a, nonnull_b, swap_taken],
        effects,
        [
            _param("a", size=8, is_signed=False),
            _param("b", size=8, is_signed=False, index=1),
        ],
    )

    assert normalized.to_string() == "(MEM[a] - MEM[b])"


def test_expression_expander_collapses_nested_multiequal_with_grouped_active_conditions():
    a = Expression.parameter("a", 0, size=8)
    b = Expression.parameter("b", 1, size=8)
    nonnull_a = Condition(Expression.binary_op("INT_NOTEQUAL", a, Expression.constant(0, 8)), False)
    nonnull_b = Condition(Expression.binary_op("INT_NOTEQUAL", b, Expression.constant(0, 8)), False)
    nonnull = Condition.combine_and([nonnull_a, nonnull_b])
    swap_taken = Condition(
        Expression.binary_op("INT_SLESS", Expression.memory(b, size=4), Expression.memory(a, size=4)),
        False,
    )
    no_swap = Condition(swap_taken.expression, True)
    post_swap_b = Expression.phi(
        [
            (Condition.combine_and([nonnull, swap_taken]), Expression.memory(a, size=4)),
            (Condition.combine_and([nonnull, no_swap]), Expression.memory(b, size=4)),
        ]
    )
    post_swap_b.size = 4
    effect_summary = EffectSummary(
        parameter_names=["a", "b"],
        effects=[
            StoreEffect(
                location=_loc("a", 0, 4),
                value=Expression.memory(b, size=4),
                conditions=[swap_taken],
                order_key=1,
            ),
            StoreEffect(
                location=_loc("b", 0, 4),
                value=Expression.memory(a, size=4),
                conditions=[swap_taken],
                order_key=2,
            ),
        ],
    )

    class FakeMultiequalOp:
        def getMnemonic(self):
            return "MULTIEQUAL"

    class FakeVarnode:
        def __init__(self, def_op):
            self._def_op = def_op

        def getSize(self):
            return 4

        def getDef(self):
            return self._def_op

    class FakeTracer:
        def _trace_pcode_op(self, _op, depth=0, use_cache=False):
            return post_swap_b

    expander = ExpressionExpander(
        FakeTracer(),
        condition_tracker=None,
        debug=False,
        effect_summary=effect_summary,
        parameters=[
            _param("a", size=8, is_signed=False),
            _param("b", size=8, is_signed=False, index=1),
        ],
    )

    expanded = expander._expand_input_varnode(
        FakeVarnode(FakeMultiequalOp()),
        [nonnull, swap_taken],
        depth=0,
    )

    assert len(expanded) == 1
    assert expanded[0].value.to_string() == "MEM[b]"


def test_normalize_post_state_expression_collapses_effect_rewritten_branch_value():
    value = Expression.parameter("value", 0, size=8)
    delta = Expression.parameter("delta", 1, size=4)
    negate = Expression.parameter("negate", 2, size=8)
    negate_zero = Condition(
        Expression.binary_op("INT_EQUAL", negate, Expression.constant(0, 8)),
        False,
    )
    negate_nonzero = negate_zero.negate()
    effects = [
        StoreEffect(
            location=_loc("value", 0, 4),
            value=Expression.binary_op("INT_ADD", Expression.memory(value, size=4), delta),
            conditions=[negate_zero],
            order_key=5,
        ),
        StoreEffect(
            location=_loc("value", 0, 4),
            value=Expression.binary_op("INT_SUB", delta, Expression.memory(value, size=4)),
            conditions=[negate_nonzero],
            order_key=5,
        ),
    ]

    rewritten = rewrite_observed_loads_from_effects(
        Expression.memory(value, size=4, read_order_key=9),
        [negate_zero],
        effects,
        [
            _param("value", size=8, is_signed=False),
            _param("delta", size=4, index=1),
            _param("negate", size=8, index=2),
        ],
    )
    normalized = normalize_post_state_expression(
        rewritten,
        [negate_zero],
        effects,
        [
            _param("value", size=8, is_signed=False),
            _param("delta", size=4, index=1),
            _param("negate", size=8, index=2),
        ],
    )

    assert rewritten.to_string() == "(MEM[value] + delta)"
    assert normalized.to_string() == "MEM[value]"


def test_normalize_post_state_expression_rewrites_double_indirect_post_state_load():
    slot = Expression.parameter("slot", 0, size=8)
    value = Expression.parameter("value", 1, size=4)
    slot_nonnull = Condition(
        Expression.binary_op("INT_NOTEQUAL", slot, Expression.constant(0, 8)),
        False,
    )
    inner_nonnull = Condition(
        Expression.binary_op(
            "INT_NOTEQUAL",
            Expression.memory(slot, size=8),
            Expression.constant(0, 8),
        ),
        False,
    )
    expr = Expression.binary_op(
        "INT_ADD",
        Expression.memory(Expression.memory(slot, size=8), size=4),
        Expression.constant(1, 4),
    )

    normalized = normalize_post_state_expression(
        expr,
        [slot_nonnull, inner_nonnull],
        [
            StoreEffect(
                location=_loc(
                    "slot",
                    offset=0,
                    size=4,
                    steps=(LocationStep("deref", 8),),
                ),
                value=value,
                conditions=[slot_nonnull, inner_nonnull],
                order_key=5,
            ),
        ],
        [
            _param("slot", size=8, is_signed=False),
            _param("value", size=4, index=1),
        ],
    )

    assert normalized.to_string() == "(value + 1)"


def test_post_state_read_expression_for_location_can_build_symbolic_reads():
    expr = post_state_read_expression_for_location(
        _loc("trace", 4, 4),
        [_param("trace", size=8, is_signed=False)],
        symbolic=True,
    )

    assert expr is not None
    assert expr.expr_type == ExpressionType.MEMORY
    assert _runtime_location(expr) == _loc("trace", 4, 4)
    assert isinstance(getattr(expr, "runtime_ref", None), PostStateReadRef)


def test_post_state_read_expression_for_location_respects_nonsymbolic_mode():
    expr = post_state_read_expression_for_location(
        _loc("trace", 4, 4),
        [_param("trace", size=8, is_signed=False)],
        symbolic=False,
    )

    assert expr is not None
    assert expr.expr_type == ExpressionType.MEMORY
    assert getattr(expr, "runtime_ref", None) is None


def test_normalize_post_state_expression_preserves_symbolic_post_state_reads_until_smt_lowering():
    trace = Expression.parameter("trace", 0, size=8)
    start = Expression.parameter("start", 1, size=4)
    limit = Expression.parameter("limit", 2, size=4)
    steps_addr = Expression.binary_op("INT_ADD", trace, Expression.constant(4, 8))
    odd_delta = Expression.unary_op("INT_2COMP", start)

    trace_nonnull = Condition(
        Expression.binary_op("INT_NOTEQUAL", trace, Expression.constant(0, 8)),
        False,
    )
    loop_active = Condition(
        Expression.binary_op("INT_SLESS", start, limit),
        False,
    )
    odd_iteration = Condition(
        Expression.binary_op(
            "INT_NOTEQUAL",
            Expression.binary_op("INT_AND", start, Expression.constant(1, 4)),
            Expression.constant(0, 4),
        ),
        False,
    )
    final_iter = Condition(
        Expression.binary_op(
            "INT_EQUAL",
            limit,
            Expression.binary_op("INT_ADD", start, Expression.constant(1, 4)),
        ),
        False,
    )

    explicit_expr = Expression.binary_op(
        "INT_ADD",
        Expression.binary_op("INT_ADD", Expression.memory(steps_addr, size=4), Expression.constant(1, 4)),
        Expression.binary_op("INT_ADD", Expression.memory(trace, size=4), odd_delta),
    )
    effects = [
        StoreEffect(
            location=_loc("trace", 0, 4),
            value=Expression.binary_op("INT_ADD", Expression.memory(trace, size=4), odd_delta),
            conditions=[trace_nonnull, loop_active, odd_iteration, final_iter],
            order_key=5,
        ),
        StoreEffect(
            location=_loc("trace", 4, 4),
            value=Expression.binary_op("INT_ADD", Expression.memory(steps_addr, size=4), Expression.constant(1, 4)),
            conditions=[trace_nonnull, loop_active, final_iter],
            order_key=6,
        ),
    ]

    normalized = normalize_post_state_expression(
        explicit_expr,
        [trace_nonnull, loop_active, odd_iteration, final_iter],
        effects,
        [
            _param("trace", size=8, is_signed=False),
            _param("start", size=4, index=1),
            _param("limit", size=4, index=2),
        ],
        symbolic_post_state=True,
    )

    assert normalized is not None
    assert expression_contains_post_state_reads(normalized)


def test_normalize_post_state_expression_promotes_observed_loads_to_symbolic_post_state():
    a = Expression.parameter("param_1", 0, size=8)
    b = Expression.parameter("param_2", 1, size=8)
    nonnull_a = Condition(
        Expression.binary_op("INT_NOTEQUAL", a, Expression.constant(0, 8)),
        False,
    )
    nonnull_b = Condition(
        Expression.binary_op("INT_NOTEQUAL", b, Expression.constant(0, 8)),
        False,
    )
    swap_taken = Condition(
        Expression.binary_op("INT_SLESS", Expression.memory(b, size=4), Expression.memory(a, size=4)),
        False,
    )
    params = [
        _param("param_1", size=8, is_signed=False),
        _param("param_2", size=8, is_signed=False, index=1),
    ]
    effects = [
        StoreEffect(
            location=_loc("param_1", 0, 4),
            value=Expression.memory(b, size=4),
            conditions=[swap_taken],
            order_key=10,
        ),
        StoreEffect(
            location=_loc("param_2", 0, 4),
            value=Expression.memory(a, size=4),
            conditions=[swap_taken],
            order_key=11,
        ),
    ]
    expr = Expression.binary_op(
        "INT_SUB",
        Expression.memory(a, size=4, read_order_key=20),
        Expression.memory(b, size=4, read_order_key=21),
    )

    normalized = normalize_post_state_expression(
        expr,
        [nonnull_a, nonnull_b],
        effects,
        params,
        symbolic_post_state=True,
    )

    assert normalized is not None
    assert expression_contains_post_state_reads(normalized)
    assert expression_contains_post_state_reads(normalized.operands[0])
    assert expression_contains_post_state_reads(normalized.operands[1])

    lowered = lower_post_state_expression_for_smt(
        normalized,
        [nonnull_a, nonnull_b],
        effects,
        params,
    )

    assert lowered is not None
    assert lowered.to_string() != expr.to_string()
    assert expression_contains_post_state_reads(lowered) is False
    assert lowered.operands[0].expr_type == ExpressionType.PHI
    assert lowered.operands[1].expr_type == ExpressionType.PHI


def test_lower_post_state_expression_for_smt_replays_symbolic_reads_under_merged_guards():
    trace = Expression.parameter("trace", 0, size=8)
    start = Expression.parameter("start", 1, size=4)
    limit = Expression.parameter("limit", 2, size=4)
    steps_addr = Expression.binary_op("INT_ADD", trace, Expression.constant(4, 8))
    odd_delta = Expression.unary_op("INT_2COMP", start)

    trace_nonnull = Condition(
        Expression.binary_op("INT_NOTEQUAL", trace, Expression.constant(0, 8)),
        False,
    )
    loop_active = Condition(
        Expression.binary_op("INT_SLESS", start, limit),
        False,
    )
    final_iter = Condition(
        Expression.binary_op(
            "INT_EQUAL",
            limit,
            Expression.binary_op("INT_ADD", start, Expression.constant(1, 4)),
        ),
        False,
    )
    odd_iteration = Condition(
        Expression.binary_op(
            "INT_NOTEQUAL",
            Expression.binary_op("INT_AND", start, Expression.constant(1, 4)),
            Expression.constant(0, 4),
        ),
        False,
    )
    even_iteration = odd_iteration.negate()

    params = [
        _param("trace", size=8, is_signed=False),
        _param("start", size=4, index=1),
        _param("limit", size=4, index=2),
    ]
    symbolic_expr = Expression.binary_op(
        "INT_ADD",
        post_state_read_expression_for_location(
            _loc("trace", 4, 4),
            params,
            symbolic=True,
        ),
        post_state_read_expression_for_location(
            _loc("trace", 0, 4),
            params,
            symbolic=True,
        ),
    )
    effects = [
        StoreEffect(
            location=_loc("trace", 0, 4),
            value=Expression.binary_op("INT_ADD", Expression.memory(trace, size=4), odd_delta),
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
            value=Expression.binary_op("INT_ADD", Expression.memory(steps_addr, size=4), Expression.constant(1, 4)),
            conditions=[trace_nonnull, loop_active, final_iter],
            order_key=6,
        ),
    ]

    lowered = lower_post_state_expression_for_smt(
        symbolic_expr,
        [trace_nonnull, loop_active, final_iter],
        effects,
        params,
    )

    assert lowered is not None
    lowered_smt = lowered.to_smt()
    assert "__locread__" not in lowered_smt
    assert "ite" in lowered_smt
    assert "bvneg start" in lowered_smt
    assert "select mem32 trace" in lowered_smt


def test_lower_post_state_expression_for_smt_rewrites_nested_symbolic_effect_values():
    trace = Expression.parameter("trace", 0, size=8)
    start = Expression.parameter("start", 1, size=4)
    limit = Expression.parameter("limit", 2, size=4)
    steps_addr = Expression.binary_op("INT_ADD", trace, Expression.constant(4, 8))
    odd_delta = Expression.unary_op("INT_2COMP", start)

    trace_nonnull = Condition(
        Expression.binary_op("INT_NOTEQUAL", trace, Expression.constant(0, 8)),
        False,
    )
    loop_active = Condition(
        Expression.binary_op("INT_SLESS", start, limit),
        False,
    )
    final_iter = Condition(
        Expression.binary_op(
            "INT_EQUAL",
            limit,
            Expression.binary_op("INT_ADD", start, Expression.constant(1, 4)),
        ),
        False,
    )
    odd_iteration = Condition(
        Expression.binary_op(
            "INT_NOTEQUAL",
            Expression.binary_op("INT_AND", start, Expression.constant(1, 4)),
            Expression.constant(0, 4),
        ),
        False,
    )
    even_iteration = odd_iteration.negate()

    params = [
        _param("trace", size=8, is_signed=False),
        _param("start", size=4, index=1),
        _param("limit", size=4, index=2),
    ]
    symbolic_expr = Expression.binary_op(
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
            value=Expression.binary_op("INT_ADD", Expression.memory(trace, size=4), odd_delta),
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

    lowered = lower_post_state_expression_for_smt(
        symbolic_expr,
        [trace_nonnull, loop_active, odd_iteration, final_iter],
        effects,
        params,
    )

    assert lowered is not None
    lowered_smt = lowered.to_smt()
    assert "__locread__" not in lowered_smt
    assert "select mem32 trace" in lowered_smt
    assert "select mem32 (bvadd trace (_ bv4 64))" in lowered_smt


def test_normalize_post_state_expression_preserves_iteration_delta_wrapped_step_value_symbolically():
    trace = Expression.parameter("trace", 0, size=8)
    start = Expression.parameter("start", 1, size=4)
    limit = Expression.parameter("limit", 2, size=4)
    steps_addr = Expression.binary_op("INT_ADD", trace, Expression.constant(4, 8))

    trace_nonnull = Condition(
        Expression.binary_op("INT_NOTEQUAL", trace, Expression.constant(0, 8)),
        False,
    )
    loop_active = Condition(
        Expression.binary_op("INT_SLESS", start, limit),
        False,
    )
    final_iter = Condition(
        Expression.binary_op(
            "INT_EQUAL",
            limit,
            Expression.binary_op("INT_ADD", start, Expression.constant(1, 4)),
        ),
        False,
    )

    wrapped_expr = Expression.binary_op(
        "INT_SUB",
        Expression.binary_op(
            "INT_ADD",
            limit,
            Expression.binary_op(
                "INT_ADD",
                Expression.memory(steps_addr, size=4),
                Expression.constant(1, 4),
            ),
        ),
        start,
    )
    normalized = normalize_post_state_expression(
        wrapped_expr,
        [trace_nonnull, loop_active, final_iter],
        [
            StoreEffect(
                location=_loc("trace", 4, 4),
                value=Expression.binary_op(
                    "INT_ADD",
                    Expression.memory(steps_addr, size=4),
                    Expression.constant(1, 4),
                ),
                conditions=[trace_nonnull, loop_active, final_iter],
                order_key=6,
            ),
        ],
        [
            _param("trace", size=8, is_signed=False),
            _param("start", size=4, index=1),
            _param("limit", size=4, index=2),
        ],
        symbolic_post_state=True,
    )

    assert normalized is not None
    assert expression_contains_post_state_reads(normalized)


def test_lower_post_state_expression_for_smt_materializes_iteration_delta_wrapped_symbolic_value():
    trace = Expression.parameter("trace", 0, size=8)
    start = Expression.parameter("start", 1, size=4)
    limit = Expression.parameter("limit", 2, size=4)
    steps_addr = Expression.binary_op("INT_ADD", trace, Expression.constant(4, 8))
    odd_delta = Expression.unary_op("INT_2COMP", start)

    trace_nonnull = Condition(
        Expression.binary_op("INT_NOTEQUAL", trace, Expression.constant(0, 8)),
        False,
    )
    loop_active = Condition(
        Expression.binary_op("INT_SLESS", start, limit),
        False,
    )
    final_iter = Condition(
        Expression.binary_op(
            "INT_EQUAL",
            limit,
            Expression.binary_op("INT_ADD", start, Expression.constant(1, 4)),
        ),
        False,
    )
    odd_iteration = Condition(
        Expression.binary_op(
            "INT_NOTEQUAL",
            Expression.binary_op("INT_AND", start, Expression.constant(1, 4)),
            Expression.constant(0, 4),
        ),
        False,
    )

    params = [
        _param("trace", size=8, is_signed=False),
        _param("start", size=4, index=1),
        _param("limit", size=4, index=2),
    ]
    symbolic_expr = Expression.binary_op(
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
    normalized = normalize_post_state_expression(
        symbolic_expr,
        [trace_nonnull, loop_active, odd_iteration, final_iter],
        [
            StoreEffect(
                location=_loc("trace", 0, 4),
                value=Expression.binary_op("INT_ADD", Expression.memory(trace, size=4), odd_delta),
                conditions=[trace_nonnull, loop_active, odd_iteration, final_iter],
                order_key=5,
            ),
            StoreEffect(
                location=_loc("trace", 4, 4),
                value=Expression.binary_op(
                    "INT_ADD",
                    Expression.memory(steps_addr, size=4),
                    Expression.constant(1, 4),
                ),
                conditions=[trace_nonnull, loop_active, final_iter],
                order_key=6,
            ),
        ],
        params,
        symbolic_post_state=True,
    )

    lowered = lower_post_state_expression_for_smt(
        normalized,
        [trace_nonnull, loop_active, odd_iteration, final_iter],
        [
            StoreEffect(
                location=_loc("trace", 0, 4),
                value=Expression.binary_op("INT_ADD", Expression.memory(trace, size=4), odd_delta),
                conditions=[trace_nonnull, loop_active, odd_iteration, final_iter],
                order_key=5,
            ),
            StoreEffect(
                location=_loc("trace", 4, 4),
                value=Expression.binary_op(
                    "INT_ADD",
                    Expression.memory(steps_addr, size=4),
                    Expression.constant(1, 4),
                ),
                conditions=[trace_nonnull, loop_active, final_iter],
                order_key=6,
            ),
        ],
        params,
    )

    assert lowered is not None
    lowered_smt = lowered.to_smt()
    assert "__locread__" not in lowered_smt
    assert "select mem32 trace" in lowered_smt
    assert "select mem32 (bvadd trace (_ bv4 64))" in lowered_smt


def test_normalize_and_lower_post_state_expression_avoids_extra_increment_for_wrapped_even_iteration_step():
    trace = Expression.parameter("param_1", 0, size=8)
    start = Expression.parameter("param_2", 1, size=4)
    limit = Expression.parameter("param_3", 2, size=4)
    steps_addr = Expression.binary_op("INT_ADD", trace, Expression.constant(4, 8))

    trace_nonnull = Condition(
        Expression.binary_op("INT_NOTEQUAL", trace, Expression.constant(0, 8)),
        False,
    )
    loop_active = Condition(
        Expression.binary_op("INT_SLESS", start, limit),
        False,
    )
    even_iteration = Condition(
        Expression.binary_op(
            "INT_EQUAL",
            Expression.binary_op("INT_AND", start, Expression.constant(1, 4)),
            Expression.constant(0, 4),
        ),
        False,
    )
    final_iter = Condition(
        Expression.binary_op(
            "INT_EQUAL",
            limit,
            Expression.binary_op("INT_ADD", start, Expression.constant(1, 4)),
        ),
        False,
    )

    params = [
        _param("param_1", size=8, is_signed=False),
        _param("param_2", size=4, index=1),
        _param("param_3", size=4, index=2),
    ]
    expr = Expression.binary_op(
        "INT_ADD",
        Expression.binary_op(
            "INT_ADD",
            Expression.memory(trace, size=4),
            start,
        ),
        Expression.binary_op(
            "INT_SUB",
            Expression.binary_op(
                "INT_ADD",
                limit,
                Expression.memory(
                    steps_addr,
                    size=4,
                ),
            ),
            start,
        ),
    )
    effects = [
        StoreEffect(
            location=_loc("param_1", 0, 4),
            value=Expression.binary_op(
                "INT_ADD",
                Expression.memory(trace, size=4),
                start,
            ),
            conditions=[trace_nonnull, loop_active, even_iteration, final_iter],
            order_key=5,
        ),
        StoreEffect(
            location=_loc("param_1", 4, 4),
            value=Expression.binary_op(
                "INT_ADD",
                Expression.memory(steps_addr, size=4),
                Expression.constant(1, 4),
            ),
            conditions=[trace_nonnull, loop_active, final_iter],
            order_key=6,
        ),
    ]

    normalized = normalize_post_state_expression(
        expr,
        [trace_nonnull, loop_active, even_iteration, final_iter],
        effects,
        params,
        symbolic_post_state=True,
    )

    lowered = lower_post_state_expression_for_smt(
        normalized,
        [trace_nonnull, loop_active, even_iteration, final_iter],
        effects,
        params,
    )

    assert lowered is not None
    assert lowered.to_string() == "((MEM[param_1] + param_2) + (MEM[(param_1 + 4)] + 1))"


def test_lower_post_state_expression_for_smt_does_not_double_replay_add_neg_form():
    trace = Expression.parameter("param_1", 0, size=8)
    start = Expression.parameter("param_2", 1, size=4)
    limit = Expression.parameter("param_3", 2, size=4)
    steps_addr = Expression.binary_op("INT_ADD", trace, Expression.constant(4, 8))

    trace_nonnull = Condition(
        Expression.binary_op("INT_NOTEQUAL", trace, Expression.constant(0, 8)),
        False,
    )
    loop_active = Condition(
        Expression.binary_op("INT_SLESS", start, limit),
        False,
    )
    odd_iteration = Condition(
        Expression.binary_op(
            "INT_NOTEQUAL",
            Expression.binary_op("INT_AND", start, Expression.constant(1, 4)),
            Expression.constant(0, 4),
        ),
        False,
    )
    final_iter = Condition(
        Expression.binary_op(
            "INT_EQUAL",
            limit,
            Expression.binary_op("INT_ADD", start, Expression.constant(1, 4)),
        ),
        False,
    )

    expr = Expression.binary_op(
        "INT_ADD",
        Expression.binary_op("INT_SUB", Expression.memory(trace, size=4), start),
        Expression.memory(steps_addr, size=4),
    )
    effects = [
        StoreEffect(
            location=_loc("param_1", 0, 4),
            value=Expression.binary_op(
                "INT_ADD",
                Expression.memory(trace, size=4),
                Expression.unary_op("INT_2COMP", start),
            ),
            conditions=[trace_nonnull, loop_active, odd_iteration, final_iter],
            order_key=5,
        ),
        StoreEffect(
            location=_loc("param_1", 4, 4),
            value=Expression.binary_op(
                "INT_ADD",
                Expression.memory(steps_addr, size=4),
                Expression.constant(1, 4),
            ),
            conditions=[trace_nonnull, loop_active, final_iter],
            order_key=6,
        ),
    ]
    params = [
        _param("param_1", size=8, is_signed=False),
        _param("param_2", size=4, index=1),
        _param("param_3", size=4, index=2),
    ]

    lowered = lower_post_state_expression_for_smt(
        expr,
        [trace_nonnull, loop_active, odd_iteration, final_iter],
        effects,
        params,
    )

    assert lowered is not None
    assert lowered.to_string() == "((MEM[param_1] - param_2) + (MEM[(param_1 + 4)] + 1))"


def test_formula_builder_lowers_symbolic_post_state_reads_before_smt_emission():
    trace = Expression.parameter("trace", 0, size=8)
    start = Expression.parameter("start", 1, size=4)
    limit = Expression.parameter("limit", 2, size=4)

    trace_nonnull = Condition(
        Expression.binary_op("INT_NOTEQUAL", trace, Expression.constant(0, 8)),
        False,
    )
    loop_active = Condition(
        Expression.binary_op("INT_SLESS", start, limit),
        False,
    )
    final_iter = Condition(
        Expression.binary_op(
            "INT_EQUAL",
            limit,
            Expression.binary_op("INT_ADD", start, Expression.constant(1, 4)),
        ),
        False,
    )
    odd_iteration = Condition(
        Expression.binary_op(
            "INT_NOTEQUAL",
            Expression.binary_op("INT_AND", start, Expression.constant(1, 4)),
            Expression.constant(0, 4),
        ),
        False,
    )
    even_iteration = odd_iteration.negate()

    params = [
        _param("trace", size=8, is_signed=False),
        _param("start", size=4, index=1),
        _param("limit", size=4, index=2),
    ]
    steps_addr = Expression.binary_op("INT_ADD", trace, Expression.constant(4, 8))
    value_expr = Expression.binary_op(
        "INT_ADD",
        post_state_read_expression_for_location(
            _loc("trace", 4, 4),
            params,
            symbolic=True,
        ),
        post_state_read_expression_for_location(
            _loc("trace", 0, 4),
            params,
            symbolic=True,
        ),
    )
    effects = [
        StoreEffect(
            location=_loc("trace", 0, 4),
            value=Expression.binary_op("INT_ADD", Expression.memory(trace, size=4), Expression.unary_op("INT_2COMP", start)),
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
            value=Expression.binary_op("INT_ADD", Expression.memory(steps_addr, size=4), Expression.constant(1, 4)),
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

    formula = FormulaBuilder(debug=False, exclude_ub=False).build_equivalence_formula_extended(
        analysis,
        analysis,
    ).formula

    assert "__locread__" not in formula
    assert "ite" in formula


def test_formula_builder_lowers_nested_symbolic_post_state_reads_before_smt_emission():
    trace = Expression.parameter("trace", 0, size=8)
    start = Expression.parameter("start", 1, size=4)
    limit = Expression.parameter("limit", 2, size=4)
    steps_addr = Expression.binary_op("INT_ADD", trace, Expression.constant(4, 8))
    odd_delta = Expression.unary_op("INT_2COMP", start)

    trace_nonnull = Condition(
        Expression.binary_op("INT_NOTEQUAL", trace, Expression.constant(0, 8)),
        False,
    )
    loop_active = Condition(
        Expression.binary_op("INT_SLESS", start, limit),
        False,
    )
    final_iter = Condition(
        Expression.binary_op(
            "INT_EQUAL",
            limit,
            Expression.binary_op("INT_ADD", start, Expression.constant(1, 4)),
        ),
        False,
    )
    odd_iteration = Condition(
        Expression.binary_op(
            "INT_NOTEQUAL",
            Expression.binary_op("INT_AND", start, Expression.constant(1, 4)),
            Expression.constant(0, 4),
        ),
        False,
    )
    even_iteration = odd_iteration.negate()

    params = [
        _param("trace", size=8, is_signed=False),
        _param("start", size=4, index=1),
        _param("limit", size=4, index=2),
    ]
    symbolic_expr = Expression.binary_op(
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
            value=Expression.binary_op("INT_ADD", Expression.memory(trace, size=4), odd_delta),
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
    explicit_expr = Expression.binary_op(
        "INT_ADD",
        Expression.binary_op(
            "INT_ADD",
            Expression.memory(steps_addr, size=4),
            Expression.constant(1, 4),
        ),
        Expression.binary_op(
            "INT_ADD",
            Expression.memory(trace, size=4),
            odd_delta,
        ),
    )
    analysis1 = FunctionReturnAnalysis(
        function_name="f1",
        entry_point="0x0",
        parameters=params,
        returns=[
            ReturnInfo(
                address="0x1",
                value=explicit_expr,
                conditions=[trace_nonnull, loop_active, odd_iteration, final_iter],
            )
        ],
        return_type="int",
    )
    analysis2 = FunctionReturnAnalysis(
        function_name="f2",
        entry_point="0x0",
        parameters=params,
        returns=[
            ReturnInfo(
                address="0x2",
                value=symbolic_expr,
                conditions=[trace_nonnull, loop_active, odd_iteration, final_iter],
            )
        ],
        return_type="int",
        effect_summary=EffectSummary(
            parameter_names=["trace", "start", "limit"],
            effects=effects,
        ),
    )

    formula = FormulaBuilder(debug=False, exclude_ub=False).build_equivalence_formula_extended(
        analysis1,
        analysis2,
    ).formula

    assert "__locread__" not in formula
    assert "return_2" in formula


def test_normalize_post_state_expression_collapses_ordered_alias_updates_to_post_state_memory():
    dst = Expression.parameter("dst", 0, size=8)
    src = Expression.parameter("src", 1, size=8)
    delta = Expression.parameter("delta", 2, size=4)
    dst_nonnull = Condition(
        Expression.binary_op("INT_NOTEQUAL", dst, Expression.constant(0, 8)),
        False,
    )
    src_nonnull = Condition(
        Expression.binary_op("INT_NOTEQUAL", src, Expression.constant(0, 8)),
        False,
    )
    alias_cond = Condition(
        Expression.binary_op("INT_EQUAL", dst, src),
        False,
    )
    effects = [
        StoreEffect(
            location=_loc("dst", 0, 4),
            value=Expression.binary_op("INT_ADD", Expression.memory(dst, size=4), delta),
            conditions=[dst_nonnull, src_nonnull],
            order_key=10,
        ),
        StoreEffect(
            location=_loc("src", 0, 4),
            value=Expression.binary_op(
                "INT_ADD",
                Expression.memory(src, size=4),
                Expression.constant(4294967295, 4),
            ),
            conditions=[dst_nonnull, src_nonnull],
            order_key=20,
        ),
    ]
    expr = Expression.binary_op(
        "INT_ADD",
        Expression.binary_op("INT_ADD", Expression.memory(dst, size=4), delta),
        Expression.constant(4294967295, 4),
    )
    params = [
        _param("dst", size=8, is_signed=False),
        _param("src", size=8, is_signed=False, index=1),
        _param("delta", size=4, index=2),
    ]
    conditions = [dst_nonnull, src_nonnull, alias_cond]

    collapsed = collapse_post_state_expr_to_canonical_memory(
        expr,
        effects,
        params,
        return_conditions=conditions,
    )
    normalized = normalize_post_state_expression(
        expr,
        conditions,
        effects,
        params,
    )

    assert collapsed is not None
    assert collapsed.to_string() == "MEM[dst]"
    assert normalized.to_string() == "MEM[dst]"


def test_normalize_post_state_expression_keeps_ordered_alias_update_when_alias_not_implied():
    dst = Expression.parameter("dst", 0, size=8)
    src = Expression.parameter("src", 1, size=8)
    delta = Expression.parameter("delta", 2, size=4)
    dst_nonnull = Condition(
        Expression.binary_op("INT_NOTEQUAL", dst, Expression.constant(0, 8)),
        False,
    )
    src_nonnull = Condition(
        Expression.binary_op("INT_NOTEQUAL", src, Expression.constant(0, 8)),
        False,
    )
    effects = [
        StoreEffect(
            location=_loc("dst", 0, 4),
            value=Expression.binary_op("INT_ADD", Expression.memory(dst, size=4), delta),
            conditions=[dst_nonnull, src_nonnull],
            order_key=10,
        ),
        StoreEffect(
            location=_loc("src", 0, 4),
            value=Expression.binary_op(
                "INT_ADD",
                Expression.memory(src, size=4),
                Expression.constant(4294967295, 4),
            ),
            conditions=[dst_nonnull, src_nonnull],
            order_key=20,
        ),
    ]
    expr = Expression.binary_op(
        "INT_ADD",
        Expression.binary_op("INT_ADD", Expression.memory(dst, size=4), delta),
        Expression.constant(4294967295, 4),
    )
    params = [
        _param("dst", size=8, is_signed=False),
        _param("src", size=8, is_signed=False, index=1),
        _param("delta", size=4, index=2),
    ]
    conditions = [dst_nonnull, src_nonnull]

    collapsed = collapse_post_state_expr_to_canonical_memory(
        expr,
        effects,
        params,
        return_conditions=conditions,
    )
    normalized = normalize_post_state_expression(
        expr,
        conditions,
        effects,
        params,
    )

    assert collapsed is None
    assert normalized.to_string() == "(MEM[dst] + 4294967295)"


def test_normalize_post_state_expression_stays_conservative_when_guards_do_not_match():
    value = Expression.parameter("value", 0, size=8)
    delta = Expression.parameter("delta", 1, size=4)
    negate = Expression.parameter("negate", 2, size=8)
    negate_zero = Condition(
        Expression.binary_op("INT_EQUAL", negate, Expression.constant(0, 8)),
        False,
    )
    other_guard = Condition(
        Expression.binary_op("INT_EQUAL", negate, Expression.constant(1, 8)),
        False,
    )
    expr = Expression.binary_op("INT_ADD", Expression.memory(value, size=4), delta)

    normalized = normalize_post_state_expression(
        expr,
        [negate_zero],
        [
            StoreEffect(
                location=_loc("value", 0, 4),
                value=Expression.binary_op("INT_ADD", Expression.memory(value, size=4), delta),
                conditions=[other_guard],
                order_key=5,
            ),
        ],
        [
            _param("value", size=8, is_signed=False),
            _param("delta", size=4, index=1),
            _param("negate", size=8, index=2),
        ],
    )

    assert normalized.to_string() == "(MEM[value] + delta)"


def test_normalize_post_state_expression_promotes_raw_memory_leaf_to_symbolic_post_state_read():
    ptr = Expression.parameter("ptr", 0, size=8)
    value = Expression.parameter("value", 1, size=4)
    ptr_nonnull = Condition(
        Expression.binary_op("INT_NOTEQUAL", ptr, Expression.constant(0, 8)),
        False,
    )

    normalized = normalize_post_state_expression(
        Expression.memory(ptr, size=4),
        [ptr_nonnull],
        [
            StoreEffect(
                location=_loc("ptr", 0, 4),
                value=Expression.unary_op("INT_2COMP", value),
                conditions=[ptr_nonnull],
                order_key=1,
            ),
        ],
        [
            _param("ptr", size=8, is_signed=False),
            _param("value", size=4, is_signed=True, index=1),
        ],
        symbolic_post_state=True,
    )

    assert normalized is not None
    assert normalized.expr_type == ExpressionType.MEMORY
    assert _runtime_location(normalized) == _loc("ptr", 0, 4)


def test_normalize_post_state_expression_replays_definite_simple_store_then_read():
    ptr = Expression.parameter("ptr", 0, size=8)
    value = Expression.parameter("value", 1, size=4)
    ptr_nonnull = Condition(
        Expression.binary_op("INT_NOTEQUAL", ptr, Expression.constant(0, 8)),
        False,
    )
    expr = Expression.binary_op(
        "INT_ADD",
        Expression.memory(ptr, size=4),
        Expression.constant(4294967295, 4),
    )

    normalized = normalize_post_state_expression(
        expr,
        [ptr_nonnull],
        [
            StoreEffect(
                location=_loc("ptr", 0, 4),
                value=Expression.binary_op("INT_ADD", value, Expression.constant(3, 4)),
                conditions=[ptr_nonnull],
                order_key=5,
            ),
        ],
        [
            _param("ptr", size=8, is_signed=False),
            _param("value", size=4, is_signed=True, index=1),
        ],
    )

    assert normalized.to_string() == "((value + 3) + 4294967295)"


def test_normalize_post_state_expression_rewrites_wide_param_store_then_read_per_branch():
    param_1 = Expression.parameter("param_1", 0, size=8)
    param_2 = Expression.parameter("param_2", 1, size=8)
    param_3 = Expression.parameter("param_3", 2, size=4)
    param_4 = Expression.parameter("param_4", 3, size=8)
    param_4_zero = Condition(
        Expression.binary_op("INT_EQUAL", param_4, Expression.constant(0, 8)),
        False,
    )
    param_4_nonzero = param_4_zero.negate()
    param_2_lo = Expression.binary_op("SUBPIECE", param_2, Expression.constant(0, 4))
    param_2_lo.size = 4
    expr = Expression.binary_op(
        "INT_SUB",
        Expression.memory(param_1, size=4),
        param_2_lo,
    )

    normalized_zero = normalize_post_state_expression(
        expr,
        [param_4_zero],
        [
            StoreEffect(
                location=_loc("param_1", 0, 4),
                value=Expression.binary_op(
                    "INT_ADD",
                    Expression.binary_op(
                        "INT_ADD",
                        Expression.binary_op(
                            "INT_MULT",
                            param_2_lo,
                            Expression.constant(2, 4),
                        ),
                        Expression.constant(11, 4),
                    ),
                    param_3,
                ),
                conditions=[param_4_zero],
                order_key=5,
            ),
            StoreEffect(
                location=_loc("param_1", 0, 4),
                value=Expression.binary_op("INT_XOR", param_2_lo, param_3),
                conditions=[param_4_nonzero],
                order_key=5,
            ),
        ],
        [
            _param("param_1", size=8, is_signed=False),
            _param("param_2", size=8, is_signed=False, index=1),
            _param("param_3", size=4, index=2),
            _param("param_4", size=8, is_signed=False, index=3),
        ],
    )
    normalized_nonzero = normalize_post_state_expression(
        expr,
        [param_4_nonzero],
        [
            StoreEffect(
                location=_loc("param_1", 0, 4),
                value=Expression.binary_op(
                    "INT_ADD",
                    Expression.binary_op(
                        "INT_ADD",
                        Expression.binary_op(
                            "INT_MULT",
                            param_2_lo,
                            Expression.constant(2, 4),
                        ),
                        Expression.constant(11, 4),
                    ),
                    param_3,
                ),
                conditions=[param_4_zero],
                order_key=5,
            ),
            StoreEffect(
                location=_loc("param_1", 0, 4),
                value=Expression.binary_op("INT_XOR", param_2_lo, param_3),
                conditions=[param_4_nonzero],
                order_key=5,
            ),
        ],
        [
            _param("param_1", size=8, is_signed=False),
            _param("param_2", size=8, is_signed=False, index=1),
            _param("param_3", size=4, index=2),
            _param("param_4", size=8, is_signed=False, index=3),
        ],
    )

    assert normalized_zero.to_string() == (
        "(((((param_2 & 4294967295) * 2) + 11) + param_3) - (param_2 & 4294967295))"
    )
    assert normalized_nonzero.to_string() == (
        "(((param_2 & 4294967295) ^ param_3) - (param_2 & 4294967295))"
    )


def test_expression_expander_prefers_canonical_post_state_memory_after_observed_load_rewrite():
    value = Expression.parameter("value", 0, size=8)
    delta = Expression.parameter("delta", 1, size=4)
    negate = Expression.parameter("negate", 2, size=8)
    negate_zero = Condition(
        Expression.binary_op("INT_EQUAL", negate, Expression.constant(0, 8)),
        False,
    )
    negate_nonzero = negate_zero.negate()

    effect_summary = EffectSummary(
        parameter_names=["value", "delta", "negate"],
        effects=[
            StoreEffect(
                location=_loc("value", 0, 4),
                value=Expression.binary_op("INT_ADD", Expression.memory(value, size=4), delta),
                conditions=[negate_zero],
                order_key=5,
            ),
            StoreEffect(
                location=_loc("value", 0, 4),
                value=Expression.binary_op("INT_SUB", delta, Expression.memory(value, size=4)),
                conditions=[negate_nonzero],
                order_key=5,
            ),
        ],
    )

    expander = ExpressionExpander(
        tracer=None,
        condition_tracker=None,
        debug=False,
        effect_summary=effect_summary,
        parameters=[
            _param("value", size=8, is_signed=False),
            _param("delta", size=4, index=1),
            _param("negate", size=8, index=2),
        ],
    )

    canonicalized = expander._canonicalize_traced_expression(
        Expression.memory(value, size=4, read_order_key=9),
        [negate_zero],
    )

    assert canonicalized.to_string() == "MEM[value]"


def test_expression_expander_keeps_root_composite_observed_effect_value_until_return_normalization():
    value = Expression.parameter("value", 0, size=8)
    value_nonnull = Condition(
        Expression.binary_op("INT_NOTEQUAL", value, Expression.constant(0, 8)),
        False,
    )
    observed = Expression.memory(
        value,
        size=4,
        read_order_key=19,
        runtime_ref=_observed_read("value", index=0, size=4, order_key=19),
    )
    effect_summary = EffectSummary(
        parameter_names=["value"],
        effects=[
            StoreEffect(
                location=_loc("value", 0, 4),
                value=Expression.binary_op(
                    "INT_ADD",
                    Expression.memory(value, size=4),
                    Expression.constant(4294967295, 4),
                ),
                conditions=[value_nonnull],
                order_key=21,
            ),
        ],
    )

    expander = ExpressionExpander(
        tracer=None,
        condition_tracker=None,
        debug=False,
        effect_summary=effect_summary,
        parameters=[_param("value", size=8, is_signed=False)],
    )

    canonicalized = expander._canonicalize_traced_expression(
        Expression.binary_op(
            "INT_ADD",
            observed,
            Expression.constant(4294967295, 4),
        ),
        [value_nonnull],
    )

    assert canonicalized.to_string() == "(MEM[value] + 4294967295)"


def test_expression_expander_collapses_nested_multiequal_after_phi_handler_prunes_to_memory_leaf():
    a = Expression.parameter("a", 0, size=8)
    b = Expression.parameter("b", 1, size=8)
    swap_taken = Condition(
        Expression.binary_op("INT_SLESS", Expression.memory(b, size=4), Expression.memory(a, size=4)),
        False,
    )
    effect_summary = EffectSummary(
        parameter_names=["a", "b"],
        effects=[
            StoreEffect(
                location=_loc("a", 0, 4),
                value=Expression.memory(b, size=4),
                conditions=[swap_taken],
                order_key=1,
            ),
            StoreEffect(
                location=_loc("b", 0, 4),
                value=Expression.memory(a, size=4),
                conditions=[swap_taken],
                order_key=2,
            ),
        ],
    )

    class FakeMultiequalOp:
        def getMnemonic(self):
            return "MULTIEQUAL"

    class FakeVarnode:
        def __init__(self, def_op):
            self._def_op = def_op

        def getSize(self):
            return 4

        def getDef(self):
            return self._def_op

    class FakeTracer:
        def _trace_pcode_op(self, _op, depth=0, use_cache=False):
            return Expression.memory(a, size=4)

    expander = ExpressionExpander(
        FakeTracer(),
        condition_tracker=None,
        debug=False,
        effect_summary=effect_summary,
        parameters=[
            _param("a", size=8, is_signed=False),
            _param("b", size=8, is_signed=False, index=1),
        ],
    )

    expanded = expander._expand_input_varnode(
        FakeVarnode(FakeMultiequalOp()),
        [swap_taken],
        depth=0,
    )

    assert len(expanded) == 1
    assert expanded[0].value.to_string() == "MEM[b]"


def test_expression_expander_uses_multiequal_canonical_location_per_branch():
    a = Expression.parameter("a", 0, size=8)
    b = Expression.parameter("b", 1, size=8)
    swap_taken = Condition(
        Expression.binary_op("INT_SLESS", Expression.memory(b, size=4), Expression.memory(a, size=4)),
        False,
    )
    no_swap = swap_taken.negate()
    effect_summary = EffectSummary(
        parameter_names=["a", "b"],
        effects=[
            StoreEffect(
                location=_loc("a", 0, 4),
                value=Expression.memory(b, size=4),
                conditions=[swap_taken],
                order_key=1,
            ),
            StoreEffect(
                location=_loc("b", 0, 4),
                value=Expression.memory(a, size=4),
                conditions=[swap_taken],
                order_key=2,
            ),
        ],
    )

    pred_no_swap = object()
    pred_swap = object()

    class FakeInputVarnode:
        def __init__(self, expr):
            self.expr = expr

        def getDef(self):
            return None

    class FakeParent:
        def getInSize(self):
            return 2

        def getIn(self, index):
            return [pred_no_swap, pred_swap][index]

    class FakeMultiequalOp:
        def getParent(self):
            return FakeParent()

        def getNumInputs(self):
            return 2

        def getInput(self, index):
            return [
                FakeInputVarnode(Expression.memory(b, size=4)),
                FakeInputVarnode(Expression.memory(a, size=4)),
            ][index]

    class FakeBlockInfo:
        def __init__(self, index):
            self.index = index

    class FakeConditionTracker:
        def get_block_by_hash(self, block):
            if block is pred_no_swap:
                return FakeBlockInfo(3)
            if block is pred_swap:
                return FakeBlockInfo(4)
            return None

        def get_all_valid_paths_to_block(self, target_block):
            return [[]]

    class FakeTracer:
        def trace_varnode(self, varnode, depth=0, use_cache=False):
            return varnode.expr

        def _get_op_key(self, _op):
            return "fake-multiequal"

    expander = ExpressionExpander(
        FakeTracer(),
        condition_tracker=FakeConditionTracker(),
        debug=False,
        effect_summary=effect_summary,
        parameters=[
            _param("a", size=8, is_signed=False),
            _param("b", size=8, is_signed=False, index=1),
        ],
    )
    expander._get_edge_condition = lambda from_block_info, to_block: (
        no_swap if from_block_info.index == 3 else swap_taken
    )

    expanded = expander._expand_multiequal_internal(
        FakeMultiequalOp(),
        [],
        depth=0,
    )

    observed = {
        (ev.value.to_string(), tuple(cond.to_string() for cond in ev.conditions))
        for ev in expanded
    }
    assert observed == {
        ("MEM[b]", (no_swap.to_string(),)),
        ("MEM[b]", (swap_taken.to_string(),)),
    }


def test_expression_expander_keeps_multiequal_location_leaf_when_outer_update_reuses_it():
    value = Expression.parameter("value", 0, size=8)
    delta = Expression.parameter("delta", 1, size=4)
    negate = Expression.parameter("negate", 2, size=4)
    negate_zero = Condition(
        Expression.binary_op("INT_EQUAL", negate, Expression.constant(0, 4)),
        False,
    )
    negate_nonzero = negate_zero.negate()
    effect_summary = EffectSummary(
        parameter_names=["value", "delta", "negate"],
        effects=[
            StoreEffect(
                location=_loc("value", 0, 4),
                value=Expression.binary_op("INT_ADD", Expression.memory(value, size=4), delta),
                conditions=[negate_zero],
                order_key=5,
            ),
            StoreEffect(
                location=_loc("value", 0, 4),
                value=Expression.binary_op("INT_SUB", delta, Expression.memory(value, size=4)),
                conditions=[negate_nonzero],
                order_key=5,
            ),
        ],
    )

    pred_zero = object()
    pred_nonzero = object()

    class FakeInputVarnode:
        def __init__(self, expr=None, def_op=None, size=4):
            self.expr = expr
            self._def_op = def_op
            self._size = size

        def getDef(self):
            return self._def_op

        def getSize(self):
            return self._size

        def getHigh(self):
            return None

    class FakeParent:
        def getInSize(self):
            return 2

        def getIn(self, index):
            return [pred_zero, pred_nonzero][index]

    class FakeMultiequalOp:
        def getParent(self):
            return FakeParent()

        def getNumInputs(self):
            return 2

        def getInput(self, index):
            return [
                FakeInputVarnode(Expression.memory(value, size=4)),
                FakeInputVarnode(Expression.memory(value, size=4)),
            ][index]

        def getMnemonic(self):
            return "MULTIEQUAL"

    phi = FakeMultiequalOp()

    class FakeOutput:
        def getSize(self):
            return 4

    class FakeAddOp:
        def getMnemonic(self):
            return "INT_ADD"

        def getNumInputs(self):
            return 2

        def getInput(self, index):
            return [
                FakeInputVarnode(def_op=phi, size=4),
                FakeInputVarnode(expr=delta, size=4),
            ][index]

        def getOutput(self):
            return FakeOutput()

    class FakeBlockInfo:
        def __init__(self, index):
            self.index = index

    class FakeConditionTracker:
        def get_block_by_hash(self, block):
            if block is pred_zero:
                return FakeBlockInfo(3)
            if block is pred_nonzero:
                return FakeBlockInfo(4)
            return None

        def get_all_valid_paths_to_block(self, target_block):
            return [[]]

    class FakeTracer:
        def trace_varnode(self, varnode, depth=0, use_cache=False):
            return varnode.expr

        def _trace_pcode_op(self, _op, depth=0, use_cache=False):
            raise AssertionError("recursive multiequal expansion should handle this case")

        def _get_op_order_key(self, _op):
            return 10

    expander = ExpressionExpander(
        FakeTracer(),
        condition_tracker=FakeConditionTracker(),
        debug=False,
        effect_summary=effect_summary,
        parameters=[
            _param("value", size=8, is_signed=False),
            _param("delta", size=4, index=1),
            _param("negate", size=4, index=2),
        ],
    )
    expander._get_edge_condition = lambda from_block_info, to_block: (
        negate_zero if from_block_info.index == 3 else negate_nonzero
    )

    expanded = expander._expand_input_operation(
        FakeAddOp(),
        [],
        depth=0,
    )

    assert len(expanded) == 1
    assert expanded[0].conditions == []
    assert expanded[0].value.to_string() == "(MEM[value] + delta)"


def test_return_analyzer_keeps_canonical_post_state_return_unchanged():
    a = Expression.parameter("a", 0, size=8)
    b = Expression.parameter("b", 1, size=8)
    swap_taken = Condition(
        Expression.binary_op("INT_SLESS", Expression.memory(b, size=4), Expression.memory(a, size=4)),
        False,
    )
    effect_summary = EffectSummary(
        parameter_names=["a", "b"],
        effects=[
            StoreEffect(
                location=_loc("a", 0, 4),
                value=Expression.memory(b, size=4),
                conditions=[swap_taken],
                order_key=1,
            ),
            StoreEffect(
                location=_loc("b", 0, 4),
                value=Expression.memory(a, size=4),
                conditions=[swap_taken],
                order_key=2,
            ),
        ],
    )
    analyzer = ReturnAnalyzer(program=object(), debug=False)
    analyzer._current_effect_summary = effect_summary
    analyzer._current_parameters = [
        _param("a", size=8, is_signed=False),
        _param("b", size=8, is_signed=False, index=1),
    ]
    normalized = analyzer._normalize_expanded_return_value(
        Expression.binary_op("INT_SUB", Expression.memory(b, size=4), Expression.memory(a, size=4)),
        [swap_taken],
    )

    assert normalized.to_string() == "(MEM[b] - MEM[a])"


def test_return_analyzer_reduces_phi_bearing_expanded_return_without_recanonicalizing():
    a = Expression.parameter("param_1", 0, size=8)
    b = Expression.parameter("param_2", 1, size=8)
    nonnull_a = Condition(Expression.binary_op("INT_NOTEQUAL", a, Expression.constant(0, 8)), False)
    nonnull_b = Condition(Expression.binary_op("INT_NOTEQUAL", b, Expression.constant(0, 8)), False)
    swap_taken = Condition(
        Expression.binary_op("INT_SLESS", Expression.memory(b, size=4), Expression.memory(a, size=4)),
        False,
    )
    composite_less = Condition.combine_and([nonnull_a, nonnull_b, swap_taken])
    composite_not_less = Condition.combine_and([nonnull_a, nonnull_b, swap_taken.negate()])
    value = Expression.binary_op(
        "INT_SUB",
        Expression.phi(
            [
                (composite_less, Expression.memory(b, size=4)),
                (composite_not_less, Expression.memory(a, size=4)),
            ]
        ),
        Expression.phi(
            [
                (composite_less, Expression.memory(a, size=4)),
                (composite_not_less, Expression.memory(b, size=4)),
            ]
        ),
    )
    value.operands[0].size = 4
    value.operands[1].size = 4
    analyzer = ReturnAnalyzer(program=object(), debug=False)
    analyzer._current_effect_summary = EffectSummary(
        parameter_names=["param_1", "param_2"],
        effects=[
            StoreEffect(
                location=_loc("param_1", 0, 4),
                value=Expression.memory(b, size=4),
                conditions=[swap_taken],
                order_key=1,
            ),
            StoreEffect(
                location=_loc("param_2", 0, 4),
                value=Expression.memory(a, size=4),
                conditions=[swap_taken],
                order_key=2,
            ),
        ],
    )
    analyzer._current_parameters = [
        _param("param_1", size=8, is_signed=False),
        _param("param_2", size=8, is_signed=False, index=1),
    ]

    normalized_less = analyzer._normalize_expanded_return_value(
        value,
        [nonnull_a, nonnull_b, swap_taken],
    )
    normalized_not_less = analyzer._normalize_expanded_return_value(
        value,
        [nonnull_a, nonnull_b, swap_taken.negate()],
    )

    assert normalized_less.to_string() == "(MEM[param_2] - MEM[param_1])"
    assert normalized_not_less.to_string() == "(MEM[param_1] - MEM[param_2])"


def test_return_analyzer_prefers_definite_branch_store_value_over_canonical_post_state_memory():
    param_1 = Expression.parameter("param_1", 0, size=8)
    param_2 = Expression.parameter("param_2", 1, size=8)
    param_3 = Expression.parameter("param_3", 2, size=4)
    param_4 = Expression.parameter("param_4", 3, size=8)
    param_4_zero = Condition(
        Expression.binary_op("INT_EQUAL", param_4, Expression.constant(0, 8)),
        False,
    )
    param_4_nonzero = param_4_zero.negate()
    param_2_lo = Expression.binary_op("SUBPIECE", param_2, Expression.constant(0, 4))
    param_2_lo.size = 4
    expr = Expression.binary_op(
        "INT_SUB",
        Expression.memory(param_1, size=4),
        param_2_lo,
    )

    analyzer = ReturnAnalyzer(program=object(), debug=False)
    analyzer._current_effect_summary = EffectSummary(
        parameter_names=["param_1", "param_2", "param_3", "param_4"],
        effects=[
            StoreEffect(
                location=_loc("param_1", 0, 4),
                value=Expression.binary_op(
                    "INT_ADD",
                    Expression.binary_op(
                        "INT_ADD",
                        Expression.binary_op(
                            "INT_MULT",
                            param_2_lo,
                            Expression.constant(2, 4),
                        ),
                        Expression.constant(11, 4),
                    ),
                    param_3,
                ),
                conditions=[param_4_zero],
                order_key=5,
            ),
            StoreEffect(
                location=_loc("param_1", 0, 4),
                value=Expression.binary_op("INT_XOR", param_2_lo, param_3),
                conditions=[param_4_nonzero],
                order_key=5,
            ),
        ],
    )
    analyzer._current_parameters = [
        _param("param_1", size=8, is_signed=False),
        _param("param_2", size=8, is_signed=False, index=1),
        _param("param_3", size=4, index=2),
        _param("param_4", size=8, is_signed=False, index=3),
    ]

    normalized_zero = analyzer._normalize_expanded_return_value(
        expr,
        [param_4_zero],
    )
    normalized_nonzero = analyzer._normalize_expanded_return_value(
        expr,
        [param_4_nonzero],
    )

    assert normalized_zero.to_string() == (
        "(((((param_2 & 4294967295) * 2) + 11) + param_3) - (param_2 & 4294967295))"
    )
    assert normalized_nonzero.to_string() == (
        "(((param_2 & 4294967295) ^ param_3) - (param_2 & 4294967295))"
    )


def test_return_analyzer_canonicalizes_partially_replayed_post_state_before_reapplying_effects():
    stats = Expression.parameter("param_1", 0, size=8)
    a = Expression.parameter("param_2", 1, size=4)
    b = Expression.parameter("param_3", 2, size=4)
    delta = Expression.parameter("param_4", 3, size=4)
    nonnull = Condition(
        Expression.binary_op("INT_NOTEQUAL", stats, Expression.constant(0, 8)),
        False,
    )
    count_addr = Expression.binary_op("INT_ADD", stats, Expression.constant(4, 8))
    partially_replayed = Expression.binary_op(
        "INT_ADD",
        Expression.binary_op(
            "INT_ADD",
            Expression.binary_op("INT_ADD", a, b),
            delta,
        ),
        Expression.binary_op(
            "INT_ADD",
            Expression.binary_op("INT_ADD", Expression.memory(count_addr, size=4), Expression.constant(1, 4)),
            Expression.constant(1, 4),
        ),
    )

    analyzer = ReturnAnalyzer(program=object(), debug=False)
    analyzer._current_effect_summary = EffectSummary(
        parameter_names=["param_1", "param_2", "param_3", "param_4"],
        effects=[
            StoreEffect(
                location=_loc("param_1", 0, 4),
                value=Expression.binary_op("INT_ADD", a, b),
                conditions=[nonnull],
                order_key=1,
            ),
            StoreEffect(
                location=_loc("param_1", 4, 4),
                value=Expression.binary_op("INT_ADD", Expression.memory(count_addr, size=4), Expression.constant(1, 4)),
                conditions=[nonnull],
                order_key=2,
            ),
            StoreEffect(
                location=_loc("param_1", 0, 4),
                value=Expression.binary_op("INT_ADD", Expression.memory(stats, size=4), delta),
                conditions=[nonnull],
                order_key=3,
            ),
            StoreEffect(
                location=_loc("param_1", 4, 4),
                value=Expression.binary_op("INT_ADD", Expression.memory(count_addr, size=4), Expression.constant(1, 4)),
                conditions=[nonnull],
                order_key=4,
            ),
        ],
    )
    analyzer._current_parameters = [
        _param("param_1", size=8, is_signed=False),
        _param("param_2", size=4, index=1),
        _param("param_3", size=4, index=2),
        _param("param_4", size=4, index=3),
    ]

    normalized = analyzer._normalize_expanded_return_value(partially_replayed, [nonnull])

    assert expression_contains_post_state_reads(normalized) is False
    assert normalized.to_string() == "(((param_2 + param_3) + param_4) + ((MEM[(param_1 + 4)] + 1) + 1))"

    lowered = lower_post_state_expression_for_smt(
        normalized,
        [nonnull],
        analyzer._current_effect_summary.effects,
        analyzer._current_parameters,
    )

    assert lowered.to_string() == "(((param_2 + param_3) + param_4) + ((MEM[(param_1 + 4)] + 1) + 1))"


def test_return_analyzer_falls_back_to_definite_replay_when_symbolic_roundtrip_is_rejected():
    trace = Expression.parameter("param_1", 0, size=8)
    start = Expression.parameter("param_2", 1, size=4)
    limit = Expression.parameter("param_3", 2, size=4)
    steps_addr = Expression.binary_op("INT_ADD", trace, Expression.constant(4, 8))

    trace_nonnull = Condition(
        Expression.binary_op("INT_NOTEQUAL", trace, Expression.constant(0, 8)),
        False,
    )
    loop_active = Condition(
        Expression.binary_op("INT_SLESS", start, limit),
        False,
    )
    odd_iteration = Condition(
        Expression.binary_op(
            "INT_NOTEQUAL",
            Expression.binary_op("INT_AND", start, Expression.constant(1, 4)),
            Expression.constant(0, 4),
        ),
        False,
    )
    final_iter = Condition(
        Expression.binary_op(
            "INT_EQUAL",
            limit,
            Expression.binary_op("INT_ADD", start, Expression.constant(1, 4)),
        ),
        False,
    )

    expr = Expression.binary_op(
        "INT_ADD",
        Expression.binary_op("INT_SUB", Expression.memory(trace, size=4), start),
        Expression.memory(steps_addr, size=4),
    )

    analyzer = ReturnAnalyzer(program=object(), debug=False)
    analyzer._current_effect_summary = EffectSummary(
        parameter_names=["param_1", "param_2", "param_3"],
        effects=[
            StoreEffect(
                location=_loc("param_1", 0, 4),
                value=Expression.binary_op(
                    "INT_ADD",
                    Expression.memory(trace, size=4),
                    Expression.unary_op("INT_2COMP", start),
                ),
                conditions=[trace_nonnull, loop_active, odd_iteration, final_iter],
                order_key=5,
            ),
            StoreEffect(
                location=_loc("param_1", 4, 4),
                value=Expression.binary_op(
                    "INT_ADD",
                    Expression.memory(steps_addr, size=4),
                    Expression.constant(1, 4),
                ),
                conditions=[trace_nonnull, loop_active, final_iter],
                order_key=6,
            ),
        ],
    )
    analyzer._current_parameters = [
        _param("param_1", size=8, is_signed=False),
        _param("param_2", size=4, index=1),
        _param("param_3", size=4, index=2),
    ]

    normalized = analyzer._normalize_expanded_return_value(
        expr,
        [trace_nonnull, loop_active, odd_iteration, final_iter],
    )

    assert normalized.to_string() == "((MEM[param_1] - param_2) + (MEM[(param_1 + 4)] + 1))"


def test_return_analyzer_keeps_symbolic_root_post_state_read_when_roundtrip_matches_materialized_leaf():
    ptr = Expression.parameter("param_1", 0, size=8)
    value = Expression.parameter("param_2", 1, size=4)
    flag = Expression.parameter("param_3", 2, size=4)
    ptr_nonnull = Condition(
        Expression.binary_op("INT_NOTEQUAL", ptr, Expression.constant(0, 8)),
        False,
    )
    flag_zero = Condition(
        Expression.binary_op("INT_EQUAL", flag, Expression.constant(0, 4)),
        False,
    )

    analyzer = ReturnAnalyzer(program=object(), debug=False)
    analyzer._current_effect_summary = EffectSummary(
        parameter_names=["param_1", "param_2", "param_3"],
        effects=[
            StoreEffect(
                location=_loc("param_1", 0, 4),
                value=Expression.unary_op("INT_2COMP", value),
                conditions=[ptr_nonnull, flag_zero],
                order_key=1,
            ),
        ],
    )
    analyzer._current_parameters = [
        _param("param_1", size=8, is_signed=False),
        _param("param_2", size=4, is_signed=True, index=1),
        _param("param_3", size=4, is_signed=False, index=2),
    ]

    normalized = analyzer._normalize_expanded_return_value(
        Expression.memory(ptr, size=4),
        [ptr_nonnull, flag_zero],
    )

    assert normalized is not None
    assert normalized.expr_type == ExpressionType.MEMORY
    assert _runtime_location(normalized) == _loc("param_1", 0, 4)

    lowered = lower_post_state_expression_for_smt(
        normalized,
        [ptr_nonnull, flag_zero],
        analyzer._current_effect_summary.effects,
        analyzer._current_parameters,
    )

    assert lowered.to_string() == "(-param_2)"


def test_expression_expander_canonicalizes_direct_traced_memory_leaf_via_effect_summary():
    ptr = Expression.parameter("ptr", 0, size=8)
    value = Expression.parameter("value", 1, size=4)
    ptr_nonnull = Condition(
        Expression.binary_op("INT_NOTEQUAL", ptr, Expression.constant(0, 8)),
        False,
    )
    effect_summary = EffectSummary(
        parameter_names=["ptr", "value"],
        effects=[
            StoreEffect(
                location=_loc("ptr", 0, 4),
                value=Expression.unary_op("INT_2COMP", value),
                conditions=[ptr_nonnull],
                order_key=1,
            ),
        ],
    )

    class FakeTracer:
        def _trace_pcode_op(self, _op, depth=0, use_cache=False):
            return Expression.memory(ptr, size=4)

    class FakeOp:
        pass

    expander = ExpressionExpander(
        FakeTracer(),
        condition_tracker=None,
        debug=False,
        effect_summary=effect_summary,
        parameters=[
            _param("ptr", size=8, is_signed=False),
            _param("value", size=4, is_signed=True, index=1),
        ],
    )

    canonicalized = expander._trace_operation_expression(FakeOp(), [ptr_nonnull], depth=0, output_size=4)

    assert canonicalized is not None
    assert canonicalized.to_string() == "MEM[ptr]"


def test_expression_expander_reduces_full_operation_trace_under_active_conditions_regression():
    a = Expression.parameter("a", 0, size=8)
    b = Expression.parameter("b", 1, size=8)
    swap_taken = Condition(
        Expression.binary_op("INT_SLESS", Expression.memory(b, size=4), Expression.memory(a, size=4)),
        False,
    )
    no_swap = Condition(swap_taken.expression, True)
    expr = Expression.binary_op(
        "INT_SUB",
        Expression.phi(
            [
                (no_swap, Expression.memory(a, size=4)),
                (swap_taken, Expression.memory(b, size=4)),
            ]
        ),
        Expression.phi(
            [
                (no_swap, Expression.memory(b, size=4)),
                (swap_taken, Expression.memory(a, size=4)),
            ]
        ),
    )
    expr.operands[0].size = 4
    expr.operands[1].size = 4
    effect_summary = EffectSummary(
        parameter_names=["a", "b"],
        effects=[
            StoreEffect(
                location=_loc("a", 0, 4),
                value=Expression.memory(b, size=4),
                conditions=[swap_taken],
                order_key=1,
            ),
            StoreEffect(
                location=_loc("b", 0, 4),
                value=Expression.memory(a, size=4),
                conditions=[swap_taken],
                order_key=2,
            ),
        ],
    )

    class FakeTracer:
        def _trace_pcode_op(self, _op, depth=0, use_cache=False):
            return expr

    class FakeOp:
        def getMnemonic(self):
            return "INT_SUB"

        def getOutput(self):
            class Out:
                def getSize(self):
                    return 4
            return Out()

    expander = ExpressionExpander(
        FakeTracer(),
        condition_tracker=None,
        debug=False,
        effect_summary=effect_summary,
        parameters=[
            _param("a", size=8, is_signed=False),
            _param("b", size=8, is_signed=False, index=1),
        ],
    )

    direct = expander._trace_operation_expression(FakeOp(), [no_swap], 0, output_size=4)

    assert direct is not None
    assert direct.to_string() == "(MEM[a] - MEM[b])"


def test_expression_expander_rewrites_observed_loads_before_post_state_canonicalization_duplicate_path():
    a = Expression.parameter("a", 0, size=8)
    b = Expression.parameter("b", 1, size=8)
    nonnull_a = Condition(Expression.binary_op("INT_NOTEQUAL", a, Expression.constant(0, 8)), False)
    nonnull_b = Condition(Expression.binary_op("INT_NOTEQUAL", b, Expression.constant(0, 8)), False)
    swap_taken = Condition(
        Expression.binary_op("INT_SLESS", Expression.memory(b, size=4), Expression.memory(a, size=4)),
        False,
    )
    effect_summary = EffectSummary(
        parameter_names=["a", "b"],
        effects=[
            StoreEffect(
                location=_loc("a", 0, 4),
                value=Expression.memory(b, size=4),
                conditions=[swap_taken],
                order_key=10,
            ),
            StoreEffect(
                location=_loc("b", 0, 4),
                value=Expression.memory(a, size=4),
                conditions=[swap_taken],
                order_key=11,
            ),
        ],
    )
    traced = Expression.binary_op(
        "INT_SUB",
        Expression.memory(a, size=4, read_order_key=20),
        Expression.memory(b, size=4, read_order_key=21),
    )

    class FakeTracer:
        pass

    expander = ExpressionExpander(
        FakeTracer(),
        condition_tracker=None,
        debug=False,
        effect_summary=effect_summary,
        parameters=[
            _param("a", size=8, is_signed=False),
            _param("b", size=8, is_signed=False, index=1),
        ],
    )

    canonicalized = expander._canonicalize_traced_expression(
        traced,
        [nonnull_a, nonnull_b],
    )

    assert canonicalized.to_string() == "(MEM[a] - MEM[b])"


def test_phi_handler_merge_preserves_same_value_with_distinct_conditions():
    a = Expression.parameter("a", 0, size=8)
    swap_taken = Condition(
        Expression.binary_op("INT_NOTEQUAL", a, Expression.constant(0, 8)),
        False,
    )
    no_swap = swap_taken.negate()

    class FakeTracer:
        debug = False

    handler = PhiHandler(FakeTracer(), condition_tracker=None)
    merged = handler._merge_branches(
        [
            PhiExpandedBranch([swap_taken], Expression.memory(a, size=4)),
            PhiExpandedBranch([no_swap], Expression.memory(a, size=4)),
        ]
    )

    assert len(merged) == 2


def test_expression_expander_infers_multiequal_location_by_branch_match():
    a = Expression.parameter("a", 0, size=8)
    b = Expression.parameter("b", 1, size=8)
    swap_taken = Condition(
        Expression.binary_op("INT_SLESS", Expression.memory(b, size=4), Expression.memory(a, size=4)),
        False,
    )
    no_swap = swap_taken.negate()
    effect_summary = EffectSummary(
        parameter_names=["a", "b"],
        effects=[
            StoreEffect(
                location=_loc("a", 0, 4),
                value=Expression.memory(b, size=4),
                conditions=[swap_taken],
                order_key=1,
            ),
            StoreEffect(
                location=_loc("b", 0, 4),
                value=Expression.memory(a, size=4),
                conditions=[swap_taken],
                order_key=2,
            ),
        ],
    )

    class FakeTracer:
        debug = False

    expander = ExpressionExpander(
        FakeTracer(),
        condition_tracker=None,
        debug=False,
        effect_summary=effect_summary,
        parameters=[
            _param("a", size=8, is_signed=False),
            _param("b", size=8, is_signed=False, index=1),
        ],
    )

    inferred = expander._infer_multiequal_canonical_location(
        [
            ExpandedValue(Expression.memory(a, size=4), [swap_taken]),
            ExpandedValue(Expression.memory(b, size=4), [no_swap]),
        ],
        depth=0,
    )

    assert inferred == _loc("b", 0, 4)


def test_expression_expander_infers_multiequal_location_by_identical_observed_load():
    a = Expression.parameter("a", 0, size=8)
    b = Expression.parameter("b", 1, size=8)
    swap_taken = Condition(
        Expression.binary_op("INT_SLESS", Expression.memory(b, size=4), Expression.memory(a, size=4)),
        False,
    )
    no_swap = swap_taken.negate()
    effect_summary = EffectSummary(
        parameter_names=["a", "b"],
        effects=[
            StoreEffect(
                location=_loc("a", 0, 4),
                value=Expression.memory(b, size=4),
                conditions=[swap_taken],
                order_key=1,
            ),
            StoreEffect(
                location=_loc("b", 0, 4),
                value=Expression.memory(a, size=4),
                conditions=[swap_taken],
                order_key=2,
            ),
        ],
    )

    class FakeTracer:
        debug = False

    expander = ExpressionExpander(
        FakeTracer(),
        condition_tracker=None,
        debug=False,
        effect_summary=effect_summary,
        parameters=[
            _param("a", size=8, is_signed=False),
            _param("b", size=8, is_signed=False, index=1),
        ],
    )

    inferred = expander._infer_multiequal_canonical_location(
        [
            ExpandedValue(Expression.memory(a, size=4), [swap_taken]),
            ExpandedValue(Expression.memory(a, size=4), [no_swap]),
        ],
        depth=0,
    )

    assert inferred == _loc("a", 0, 4)


def test_expression_expander_reduces_full_operation_trace_under_active_conditions():
    a = Expression.parameter("a", 0, size=8)
    b = Expression.parameter("b", 1, size=8)
    swap_taken = Condition(
        Expression.binary_op("INT_SLESS", Expression.memory(b, size=4), Expression.memory(a, size=4)),
        False,
    )
    no_swap = Condition(swap_taken.expression, True)
    expr = Expression.binary_op(
        "INT_SUB",
        Expression.phi(
            [
                (no_swap, Expression.memory(a, size=4)),
                (swap_taken, Expression.memory(b, size=4)),
            ]
        ),
        Expression.phi(
            [
                (no_swap, Expression.memory(b, size=4)),
                (swap_taken, Expression.memory(a, size=4)),
            ]
        ),
    )
    expr.operands[0].size = 4
    expr.operands[1].size = 4
    effect_summary = EffectSummary(
        parameter_names=["a", "b"],
        effects=[
            StoreEffect(
                location=_loc("a", 0, 4),
                value=Expression.memory(b, size=4),
                conditions=[swap_taken],
                order_key=1,
            ),
            StoreEffect(
                location=_loc("b", 0, 4),
                value=Expression.memory(a, size=4),
                conditions=[swap_taken],
                order_key=2,
            ),
        ],
    )

    class FakeTracer:
        def _trace_pcode_op(self, _op, depth=0, use_cache=False):
            return expr

    class FakeOp:
        def getMnemonic(self):
            return "INT_SUB"

        def getOutput(self):
            class Out:
                def getSize(self):
                    return 4
            return Out()

    expander = ExpressionExpander(
        FakeTracer(),
        condition_tracker=None,
        debug=False,
        effect_summary=effect_summary,
        parameters=[
            _param("a", size=8, is_signed=False),
            _param("b", size=8, is_signed=False, index=1),
        ],
    )

    direct = expander._trace_operation_expression(FakeOp(), [no_swap], 0, output_size=4)

    assert direct is not None
    assert direct.to_string() == "(MEM[a] - MEM[b])"


def test_expression_expander_rewrites_observed_loads_before_post_state_canonicalization():
    a = Expression.parameter("a", 0, size=8)
    b = Expression.parameter("b", 1, size=8)
    nonnull_a = Condition(Expression.binary_op("INT_NOTEQUAL", a, Expression.constant(0, 8)), False)
    nonnull_b = Condition(Expression.binary_op("INT_NOTEQUAL", b, Expression.constant(0, 8)), False)
    swap_taken = Condition(
        Expression.binary_op("INT_SLESS", Expression.memory(b, size=4), Expression.memory(a, size=4)),
        False,
    )
    effect_summary = EffectSummary(
        parameter_names=["a", "b"],
        effects=[
            StoreEffect(
                location=_loc("a", 0, 4),
                value=Expression.memory(b, size=4),
                conditions=[swap_taken],
                order_key=10,
            ),
            StoreEffect(
                location=_loc("b", 0, 4),
                value=Expression.memory(a, size=4),
                conditions=[swap_taken],
                order_key=11,
            ),
        ],
    )
    traced = Expression.binary_op(
        "INT_SUB",
        Expression.memory(a, size=4, read_order_key=20),
        Expression.memory(b, size=4, read_order_key=21),
    )

    class FakeTracer:
        pass

    expander = ExpressionExpander(
        FakeTracer(),
        condition_tracker=None,
        debug=False,
        effect_summary=effect_summary,
        parameters=[
            _param("a", size=8, is_signed=False),
            _param("b", size=8, is_signed=False, index=1),
        ],
    )

    canonicalized = expander._canonicalize_traced_expression(
        traced,
        [nonnull_a, nonnull_b],
    )

    assert canonicalized.to_string() == "(MEM[a] - MEM[b])"


def test_expression_expander_keeps_symbolic_post_state_identity_after_observed_load_rewrite():
    a = Expression.parameter("a", 0, size=8)
    b = Expression.parameter("b", 1, size=8)
    nonnull_a = Condition(Expression.binary_op("INT_NOTEQUAL", a, Expression.constant(0, 8)), False)
    nonnull_b = Condition(Expression.binary_op("INT_NOTEQUAL", b, Expression.constant(0, 8)), False)
    swap_taken = Condition(
        Expression.binary_op("INT_SLESS", Expression.memory(b, size=4), Expression.memory(a, size=4)),
        False,
    )
    expr = Expression.binary_op(
        "INT_SUB",
        Expression.memory(a, size=4, read_order_key=20),
        Expression.memory(b, size=4, read_order_key=21),
    )
    effect_summary = EffectSummary(
        parameter_names=["a", "b"],
        effects=[
            StoreEffect(
                location=_loc("a", 0, 4),
                value=Expression.memory(b, size=4),
                conditions=[swap_taken],
                order_key=10,
            ),
            StoreEffect(
                location=_loc("b", 0, 4),
                value=Expression.memory(a, size=4),
                conditions=[swap_taken],
                order_key=11,
            ),
        ],
    )

    class FakeTracer:
        debug = False

    expander = ExpressionExpander(
        FakeTracer(),
        condition_tracker=None,
        debug=False,
        effect_summary=effect_summary,
        parameters=[
            _param("a", size=8, is_signed=False),
            _param("b", size=8, is_signed=False, index=1),
        ],
    )

    canonicalized = expander._canonicalize_traced_expression(expr, [nonnull_a, nonnull_b])

    assert canonicalized is not None
    assert expression_contains_post_state_reads(canonicalized)
    assert _runtime_location(canonicalized.operands[0]) == _loc("a", 0, 4)
    assert _runtime_location(canonicalized.operands[1]) == _loc("b", 0, 4)
    assert _runtime_snapshot(canonicalized.operands[0]) == _runtime_snapshot(canonicalized.operands[1])


def test_promote_observed_loads_to_post_state_reads_shares_snapshot_for_swap_pair():
    a = Expression.parameter("a", 0, size=8)
    b = Expression.parameter("b", 1, size=8)
    nonnull_a = Condition(Expression.binary_op("INT_NOTEQUAL", a, Expression.constant(0, 8)), False)
    nonnull_b = Condition(Expression.binary_op("INT_NOTEQUAL", b, Expression.constant(0, 8)), False)
    swap_taken = Condition(
        Expression.binary_op("INT_SLESS", Expression.memory(b, size=4), Expression.memory(a, size=4)),
        False,
    )
    expr = Expression.binary_op(
        "INT_SUB",
        Expression.memory(
            a,
            size=4,
            read_order_key=20,
            runtime_ref=ObservedMemoryReadRef(order_key=20, location=_loc("a", 0, 4)),
        ),
        Expression.memory(
            b,
            size=4,
            read_order_key=21,
            runtime_ref=ObservedMemoryReadRef(order_key=21, location=_loc("b", 0, 4)),
        ),
    )
    effects = [
        StoreEffect(
            location=_loc("a", 0, 4),
            value=Expression.memory(b, size=4),
            conditions=[swap_taken],
            order_key=10,
        ),
        StoreEffect(
            location=_loc("b", 0, 4),
            value=Expression.memory(a, size=4),
            conditions=[swap_taken],
            order_key=11,
        ),
    ]

    promoted = promote_observed_loads_to_post_state_reads(
        expr,
        [nonnull_a, nonnull_b],
        effects,
        [_param("a", size=8, is_signed=False), _param("b", size=8, is_signed=False, index=1)],
        symbolic_post_state=True,
    )

    assert promoted is not None
    assert expression_contains_post_state_reads(promoted)
    assert isinstance(getattr(promoted.operands[0], "runtime_ref", None), PostStateReadRef)
    assert isinstance(getattr(promoted.operands[1], "runtime_ref", None), PostStateReadRef)
    assert _runtime_location(promoted.operands[0]) == _loc("a", 0, 4)
    assert _runtime_location(promoted.operands[1]) == _loc("b", 0, 4)
    assert isinstance(_runtime_snapshot(promoted.operands[0]), PostStateSnapshotRef)
    assert _runtime_snapshot(promoted.operands[0]) == _runtime_snapshot(promoted.operands[1])

    lowered = lower_post_state_expression_for_smt(
        promoted,
        [nonnull_a, nonnull_b],
        effects,
        [_param("a", size=8, is_signed=False), _param("b", size=8, is_signed=False, index=1)],
    )

    assert lowered is not None
    assert expression_contains_post_state_reads(lowered) is False


def test_expression_expander_keeps_canonical_memory_without_read_order_key_unchanged():
    a = Expression.parameter("a", 0, size=8)
    b = Expression.parameter("b", 1, size=8)
    swap_taken = Condition(
        Expression.binary_op("INT_SLESS", Expression.memory(b, size=4), Expression.memory(a, size=4)),
        False,
    )
    effect_summary = EffectSummary(
        parameter_names=["a", "b"],
        effects=[
            StoreEffect(
                location=_loc("a", 0, 4),
                value=Expression.memory(b, size=4),
                conditions=[swap_taken],
                order_key=10,
            ),
            StoreEffect(
                location=_loc("b", 0, 4),
                value=Expression.memory(a, size=4),
                conditions=[swap_taken],
                order_key=11,
            ),
        ],
    )
    canonical = Expression.binary_op(
        "INT_SUB",
        Expression.memory(b, size=4),
        Expression.memory(a, size=4),
    )

    class FakeTracer:
        pass

    expander = ExpressionExpander(
        FakeTracer(),
        condition_tracker=None,
        debug=False,
        effect_summary=effect_summary,
        parameters=[
            _param("a", size=8, is_signed=False),
            _param("b", size=8, is_signed=False, index=1),
        ],
    )

    canonicalized = expander._canonicalize_traced_expression(
        canonical,
        [swap_taken],
    )

    assert canonicalized.to_string() == "(MEM[b] - MEM[a])"


def test_expression_expander_does_not_replay_plain_memory_leaf_inside_iteration_delta_wrapper():
    trace = Expression.parameter("param_1", 0, size=8)
    start = Expression.parameter("param_2", 1, size=4)
    limit = Expression.parameter("param_3", 2, size=4)
    steps_addr = Expression.binary_op("INT_ADD", trace, Expression.constant(4, 8))

    trace_nonnull = Condition(
        Expression.binary_op("INT_NOTEQUAL", trace, Expression.constant(0, 8)),
        False,
    )
    loop_active = Condition(
        Expression.binary_op("INT_SLESS", start, limit),
        False,
    )
    even_iteration = Condition(
        Expression.binary_op(
            "INT_EQUAL",
            Expression.binary_op("INT_AND", start, Expression.constant(1, 4)),
            Expression.constant(0, 4),
        ),
        False,
    )
    final_iter = Condition(
        Expression.binary_op(
            "INT_EQUAL",
            limit,
            Expression.binary_op("INT_ADD", start, Expression.constant(1, 4)),
        ),
        False,
    )
    traced = Expression.binary_op(
        "INT_SUB",
        Expression.binary_op("INT_ADD", limit, Expression.memory(steps_addr, size=4)),
        start,
    )
    effect_summary = EffectSummary(
        parameter_names=["param_1", "param_2", "param_3"],
        effects=[
            StoreEffect(
                location=_loc("param_1", 4, 4),
                value=Expression.binary_op(
                    "INT_ADD",
                    Expression.memory(steps_addr, size=4),
                    Expression.constant(1, 4),
                ),
                conditions=[trace_nonnull, loop_active, final_iter],
                order_key=6,
            ),
        ],
    )

    class FakeTracer:
        pass

    expander = ExpressionExpander(
        FakeTracer(),
        condition_tracker=None,
        debug=False,
        effect_summary=effect_summary,
        parameters=[
            _param("param_1", size=8, is_signed=False),
            _param("param_2", size=4, index=1),
            _param("param_3", size=4, index=2),
        ],
    )

    canonicalized = expander._canonicalize_traced_expression(
        traced,
        [trace_nonnull, loop_active, even_iteration, final_iter],
    )

    assert canonicalized.to_string() == "MEM[(param_1 + 4)]"


def test_expression_expander_ignores_identity_only_observed_load_rewrite_in_iteration_delta_wrapper():
    trace = Expression.parameter("param_1", 0, size=8)
    start = Expression.parameter("param_2", 1, size=4)
    limit = Expression.parameter("param_3", 2, size=4)
    steps_addr = Expression.binary_op("INT_ADD", trace, Expression.constant(4, 8))

    trace_nonnull = Condition(
        Expression.binary_op("INT_NOTEQUAL", trace, Expression.constant(0, 8)),
        False,
    )
    loop_active = Condition(
        Expression.binary_op("INT_SLESS", start, limit),
        False,
    )
    even_iteration = Condition(
        Expression.binary_op(
            "INT_EQUAL",
            Expression.binary_op("INT_AND", start, Expression.constant(1, 4)),
            Expression.constant(0, 4),
        ),
        False,
    )
    final_iter = Condition(
        Expression.binary_op(
            "INT_EQUAL",
            limit,
            Expression.binary_op("INT_ADD", start, Expression.constant(1, 4)),
        ),
        False,
    )
    traced = Expression.binary_op(
        "INT_SUB",
        Expression.binary_op(
            "INT_ADD",
            limit,
            Expression.memory(steps_addr, size=4, read_order_key=42),
        ),
        start,
    )
    effect_summary = EffectSummary(
        parameter_names=["param_1", "param_2", "param_3"],
        effects=[
            StoreEffect(
                location=_loc("param_1", 4, 4),
                value=Expression.binary_op(
                    "INT_ADD",
                    Expression.memory(steps_addr, size=4),
                    Expression.constant(1, 4),
                ),
                conditions=[trace_nonnull, loop_active, final_iter],
                order_key=6,
            ),
        ],
    )

    class FakeTracer:
        pass

    expander = ExpressionExpander(
        FakeTracer(),
        condition_tracker=None,
        debug=False,
        effect_summary=effect_summary,
        parameters=[
            _param("param_1", size=8, is_signed=False),
            _param("param_2", size=4, index=1),
            _param("param_3", size=4, index=2),
        ],
    )

    canonicalized = expander._canonicalize_traced_expression(
        traced,
        [trace_nonnull, loop_active, even_iteration, final_iter],
    )

    assert canonicalized.to_string() == "((param_3 + MEM[(param_1 + 4)]) - param_2)"


def test_return_analyzer_collapses_even_iteration_wrapper_with_observed_step_load_to_symbolic_post_state():
    trace = Expression.parameter("param_1", 0, size=8)
    start = Expression.parameter("param_2", 1, size=4)
    limit = Expression.parameter("param_3", 2, size=4)
    steps_addr = Expression.binary_op("INT_ADD", trace, Expression.constant(4, 8))

    trace_nonnull = Condition(
        Expression.binary_op("INT_NOTEQUAL", trace, Expression.constant(0, 8)),
        False,
    )
    loop_active = Condition(
        Expression.binary_op("INT_SLESS", start, limit),
        False,
    )
    even_iteration = Condition(
        Expression.binary_op(
            "INT_EQUAL",
            Expression.binary_op("INT_AND", start, Expression.constant(1, 4)),
            Expression.constant(0, 4),
        ),
        False,
    )
    final_iter = Condition(
        Expression.binary_op(
            "INT_EQUAL",
            limit,
            Expression.binary_op("INT_ADD", start, Expression.constant(1, 4)),
        ),
        False,
    )
    expr = Expression.binary_op(
        "INT_ADD",
        Expression.binary_op("INT_ADD", Expression.memory(trace, size=4), start),
        Expression.binary_op(
            "INT_SUB",
            Expression.binary_op(
                "INT_ADD",
                limit,
                Expression.memory(steps_addr, size=4, read_order_key=42),
            ),
            start,
        ),
    )

    analyzer = ReturnAnalyzer(program=object(), debug=False)
    analyzer._current_effect_summary = EffectSummary(
        parameter_names=["param_1", "param_2", "param_3"],
        effects=[
            StoreEffect(
                location=_loc("param_1", 0, 4),
                value=Expression.binary_op(
                    "INT_ADD",
                    Expression.memory(trace, size=4),
                    start,
                ),
                conditions=[trace_nonnull, loop_active, even_iteration, final_iter],
                order_key=5,
            ),
            StoreEffect(
                location=_loc("param_1", 4, 4),
                value=Expression.binary_op(
                    "INT_ADD",
                    Expression.memory(steps_addr, size=4),
                    Expression.constant(1, 4),
                ),
                conditions=[trace_nonnull, loop_active, final_iter],
                order_key=6,
            ),
        ],
    )
    analyzer._current_parameters = [
        _param("param_1", size=8, is_signed=False),
        _param("param_2", size=4, index=1),
        _param("param_3", size=4, index=2),
    ]

    normalized = analyzer._normalize_expanded_return_value(
        expr,
        [trace_nonnull, loop_active, even_iteration, final_iter],
    )

    assert expression_contains_post_state_reads(normalized)
    assert normalized.to_string() == "(MEM[param_1] + MEM[(param_1 + 4)])"


def test_return_analyzer_normalizes_observed_load_returns_to_symbolic_post_state():
    a = Expression.parameter("param_1", 0, size=8)
    b = Expression.parameter("param_2", 1, size=8)
    nonnull_a = Condition(
        Expression.binary_op("INT_NOTEQUAL", a, Expression.constant(0, 8)),
        False,
    )
    nonnull_b = Condition(
        Expression.binary_op("INT_NOTEQUAL", b, Expression.constant(0, 8)),
        False,
    )
    swap_taken = Condition(
        Expression.binary_op("INT_SLESS", Expression.memory(b, size=4), Expression.memory(a, size=4)),
        False,
    )
    expr = Expression.binary_op(
        "INT_SUB",
        Expression.memory(a, size=4, read_order_key=20),
        Expression.memory(b, size=4, read_order_key=21),
    )

    analyzer = ReturnAnalyzer(program=object(), debug=False)
    analyzer._current_parameters = [
        _param("param_1", size=8, is_signed=False),
        _param("param_2", size=8, is_signed=False, index=1),
    ]
    effect_summary = EffectSummary(
        parameter_names=["param_1", "param_2"],
        effects=[
            StoreEffect(
                location=_loc("param_1", 0, 4),
                value=Expression.memory(b, size=4),
                conditions=[swap_taken],
                order_key=10,
            ),
            StoreEffect(
                location=_loc("param_2", 0, 4),
                value=Expression.memory(a, size=4),
                conditions=[swap_taken],
                order_key=11,
            ),
        ],
    )

    normalized = analyzer._normalize_return_value_with_effect_summary(
        expr,
        [nonnull_a, nonnull_b],
        effect_summary,
    )

    assert normalized is not None
    assert expression_contains_post_state_reads(normalized)
    assert expression_contains_post_state_reads(normalized.operands[0])
    assert expression_contains_post_state_reads(normalized.operands[1])

    lowered = lower_post_state_expression_for_smt(
        normalized,
        [nonnull_a, nonnull_b],
        effect_summary.effects,
        analyzer._current_parameters,
    )

    assert lowered is not None
    assert expression_contains_post_state_reads(lowered) is False
    assert lowered.operands[0].expr_type == ExpressionType.PHI
    assert lowered.operands[1].expr_type == ExpressionType.PHI


def test_return_analyzer_normalizes_single_arithmetic_update_rhs_to_post_state():
    value = Expression.parameter("value", 0, size=8)
    delta = Expression.parameter("delta", 1, size=4)
    negate = Expression.parameter("negate", 2, size=4)
    value_nonnull = Condition(
        Expression.binary_op("INT_NOTEQUAL", value, Expression.constant(0, 8)),
        False,
    )
    negate_zero = Condition(
        Expression.binary_op("INT_EQUAL", negate, Expression.constant(0, 4)),
        False,
    )
    negate_nonzero = negate_zero.negate()

    analyzer = ReturnAnalyzer(program=object(), debug=False)
    analyzer._current_parameters = [
        _param("value", size=8, is_signed=False),
        _param("delta", size=4, index=1),
        _param("negate", size=4, index=2),
    ]
    analyzer._current_effect_summary = EffectSummary(
        parameter_names=["value", "delta", "negate"],
        effects=[
            StoreEffect(
                location=_loc("value", 0, 4),
                value=Expression.binary_op("INT_ADD", Expression.memory(value, size=4), delta),
                conditions=[value_nonnull, negate_zero],
                order_key=5,
            ),
            StoreEffect(
                location=_loc("value", 0, 4),
                value=Expression.binary_op("INT_SUB", delta, Expression.memory(value, size=4)),
                conditions=[value_nonnull, negate_nonzero],
                order_key=5,
            ),
        ],
    )

    normalized_zero = analyzer._normalize_expanded_return_value(
        Expression.binary_op("INT_ADD", Expression.memory(value, size=4), delta),
        [value_nonnull, negate_zero],
    )
    normalized_nonzero = analyzer._normalize_expanded_return_value(
        Expression.binary_op("INT_SUB", delta, Expression.memory(value, size=4)),
        [value_nonnull, negate_nonzero],
    )

    assert normalized_zero.to_string() == "MEM[value]"
    assert normalized_nonzero.to_string() == "MEM[value]"
    assert _runtime_location(normalized_zero) == _loc("value", 0, 4)
    assert _runtime_location(normalized_nonzero) == _loc("value", 0, 4)

    lowered_zero = lower_post_state_expression_for_smt(
        normalized_zero,
        [value_nonnull, negate_zero],
        analyzer._current_effect_summary.effects,
        analyzer._current_parameters,
    )
    lowered_nonzero = lower_post_state_expression_for_smt(
        normalized_nonzero,
        [value_nonnull, negate_nonzero],
        analyzer._current_effect_summary.effects,
        analyzer._current_parameters,
    )

    assert lowered_zero.to_string() == "(MEM[value] + delta)"
    assert lowered_nonzero.to_string() == "(delta - MEM[value])"


def test_expression_matches_stale_post_state_replay_for_same_location_self_update():
    value = Expression.parameter("value", 0, size=8)
    delta = Expression.parameter("delta", 1, size=4)
    negate = Expression.parameter("negate", 2, size=4)
    value_nonnull = Condition(
        Expression.binary_op("INT_NOTEQUAL", value, Expression.constant(0, 8)),
        False,
    )
    negate_zero = Condition(
        Expression.binary_op("INT_EQUAL", negate, Expression.constant(0, 4)),
        False,
    )
    effects = [
        StoreEffect(
            location=_loc("value", 0, 4),
            value=Expression.binary_op("INT_ADD", Expression.memory(value, size=4), delta),
            conditions=[value_nonnull, negate_zero],
            order_key=5,
        ),
    ]
    params = [
        _param("value", size=8, is_signed=False),
        _param("delta", size=4, index=1),
        _param("negate", size=4, index=2),
    ]
    symbolic_post_state = post_state_read_expression_for_location(
        _loc("value", 0, 4),
        params,
        symbolic=True,
    )
    stale_replay = Expression.binary_op(
        "INT_ADD",
        delta,
        Expression.binary_op("INT_ADD", Expression.memory(value, size=4), delta),
    )

    assert expression_matches_stale_post_state_replay(
        stale_replay,
        symbolic_post_state,
        [value_nonnull, negate_zero],
        effects,
        params,
    )


def test_return_analyzer_accepts_symbolic_post_state_for_stale_self_update_replay():
    value = Expression.parameter("value", 0, size=8)
    delta = Expression.parameter("delta", 1, size=4)
    negate = Expression.parameter("negate", 2, size=4)
    value_nonnull = Condition(
        Expression.binary_op("INT_NOTEQUAL", value, Expression.constant(0, 8)),
        False,
    )
    negate_zero = Condition(
        Expression.binary_op("INT_EQUAL", negate, Expression.constant(0, 4)),
        False,
    )

    analyzer = ReturnAnalyzer(program=object(), debug=False)
    analyzer._current_parameters = [
        _param("value", size=8, is_signed=False),
        _param("delta", size=4, index=1),
        _param("negate", size=4, index=2),
    ]
    analyzer._current_effect_summary = EffectSummary(
        parameter_names=["value", "delta", "negate"],
        effects=[
            StoreEffect(
                location=_loc("value", 0, 4),
                value=Expression.binary_op("INT_ADD", Expression.memory(value, size=4), delta),
                conditions=[value_nonnull, negate_zero],
                order_key=5,
            ),
        ],
    )

    stale_replay = Expression.binary_op(
        "INT_ADD",
        delta,
        Expression.binary_op("INT_ADD", Expression.memory(value, size=4), delta),
    )

    normalized = analyzer._normalize_expanded_return_value(
        stale_replay,
        [value_nonnull, negate_zero],
    )

    assert normalized.to_string() == "MEM[value]"
    assert _runtime_location(normalized) == _loc("value", 0, 4)

    lowered = lower_post_state_expression_for_smt(
        normalized,
        [value_nonnull, negate_zero],
        analyzer._current_effect_summary.effects,
        analyzer._current_parameters,
    )

    assert lowered.to_string() == "(MEM[value] + delta)"


def test_return_analyzer_accepts_symbolic_post_state_for_negate_effect_value_wrapper():
    value = Expression.parameter("value", 0, size=8)
    delta = Expression.parameter("delta", 1, size=4)
    negate = Expression.parameter("negate", 2, size=4)
    value_nonnull = Condition(
        Expression.binary_op("INT_NOTEQUAL", value, Expression.constant(0, 8)),
        False,
    )
    negate_nonzero = Condition(
        Expression.binary_op("INT_NOTEQUAL", negate, Expression.constant(0, 4)),
        False,
    )

    analyzer = ReturnAnalyzer(program=object(), debug=False)
    analyzer._current_parameters = [
        _param("value", size=8, is_signed=False),
        _param("delta", size=4, index=1),
        _param("negate", size=4, index=2),
    ]
    analyzer._current_effect_summary = EffectSummary(
        parameter_names=["value", "delta", "negate"],
        effects=[
            StoreEffect(
                location=_loc("value", 0, 4),
                value=Expression.binary_op("INT_SUB", delta, Expression.memory(value, size=4)),
                conditions=[value_nonnull, negate_nonzero],
                order_key=5,
            ),
        ],
    )

    negate_effect_wrapper = Expression.binary_op(
        "INT_ADD",
        Expression.unary_op("INT_2COMP", Expression.memory(value, size=4)),
        delta,
    )

    normalized = analyzer._normalize_expanded_return_value(
        negate_effect_wrapper,
        [value_nonnull, negate_nonzero],
    )

    assert normalized.to_string() == "MEM[value]"
    assert _runtime_location(normalized) == _loc("value", 0, 4)

    lowered = lower_post_state_expression_for_smt(
        normalized,
        [value_nonnull, negate_nonzero],
        analyzer._current_effect_summary.effects,
        analyzer._current_parameters,
    )

    assert lowered.to_string() == "(delta - MEM[value])"


def test_return_analyzer_does_not_merge_complementary_symbolic_post_state_cases_when_lowerings_differ():
    value = Expression.parameter("value", 0, size=8)
    delta = Expression.parameter("delta", 1, size=4)
    negate = Expression.parameter("negate", 2, size=4)
    value_nonnull = Condition(
        Expression.binary_op("INT_NOTEQUAL", value, Expression.constant(0, 8)),
        False,
    )
    negate_zero = Condition(
        Expression.binary_op("INT_EQUAL", negate, Expression.constant(0, 4)),
        False,
    )
    negate_nonzero = Condition(
        Expression.binary_op("INT_NOTEQUAL", negate, Expression.constant(0, 4)),
        False,
    )

    analyzer = ReturnAnalyzer(program=object(), debug=False)
    analyzer._current_parameters = [
        _param("value", size=8, is_signed=False),
        _param("delta", size=4, index=1),
        _param("negate", size=4, index=2),
    ]
    analyzer._current_effect_summary = EffectSummary(
        parameter_names=["value", "delta", "negate"],
        effects=[
            StoreEffect(
                location=_loc("value", 0, 4),
                value=Expression.binary_op("INT_ADD", Expression.memory(value, size=4), delta),
                conditions=[value_nonnull, negate_zero],
                order_key=5,
            ),
            StoreEffect(
                location=_loc("value", 0, 4),
                value=Expression.binary_op("INT_SUB", delta, Expression.memory(value, size=4)),
                conditions=[value_nonnull, negate_nonzero],
                order_key=6,
            ),
        ],
    )

    symbolic_post_state = post_state_read_expression_for_location(
        _loc("value", 0, 4),
        analyzer._current_parameters,
        symbolic=True,
    )

    left = ReturnInfo(
        address="ret",
        value=symbolic_post_state,
        conditions=[value_nonnull, negate_zero],
        branch_index=1,
        pcode_identity="ret:t1",
    )
    right = ReturnInfo(
        address="ret",
        value=symbolic_post_state,
        conditions=[value_nonnull, negate_nonzero],
        branch_index=2,
        pcode_identity="ret:t1",
    )

    assert analyzer._merge_return_info_pair(left, right, [left, right], 0, 1) is None


def test_return_analyzer_accepts_semantically_lossless_swap_snapshot_rewrite():
    a = Expression.parameter("a", 0, size=8)
    b = Expression.parameter("b", 1, size=8)
    nonnull_a = Condition(Expression.binary_op("INT_NOTEQUAL", a, Expression.constant(0, 8)), False)
    nonnull_b = Condition(Expression.binary_op("INT_NOTEQUAL", b, Expression.constant(0, 8)), False)
    swap_taken = Condition(
        Expression.binary_op("INT_SLESS", Expression.memory(b, size=4), Expression.memory(a, size=4)),
        False,
    )
    original = Expression.binary_op(
        "INT_SUB",
        Expression.memory(
            a,
            size=4,
            read_order_key=20,
            runtime_ref=ObservedMemoryReadRef(order_key=20, location=_loc("a", 0, 4)),
        ),
        Expression.memory(
            b,
            size=4,
            read_order_key=21,
            runtime_ref=ObservedMemoryReadRef(order_key=21, location=_loc("b", 0, 4)),
        ),
    )
    effect_summary = EffectSummary(
        parameter_names=["a", "b"],
        effects=[
            StoreEffect(
                location=_loc("a", 0, 4),
                value=Expression.memory(b, size=4),
                conditions=[swap_taken],
                order_key=10,
            ),
            StoreEffect(
                location=_loc("b", 0, 4),
                value=Expression.memory(a, size=4),
                conditions=[swap_taken],
                order_key=11,
            ),
        ],
    )

    analyzer = ReturnAnalyzer(program=object(), debug=False)
    analyzer._current_parameters = [
        _param("a", size=8, is_signed=False),
        _param("b", size=8, is_signed=False, index=1),
    ]
    rewritten = promote_observed_loads_to_post_state_reads(
        original,
        [nonnull_a, nonnull_b],
        effect_summary.effects,
        analyzer._current_parameters,
        symbolic_post_state=True,
    )

    assert rewritten is not None
    assert analyzer._accept_effect_sensitive_rewrite(
        original,
        rewritten,
        [nonnull_a, nonnull_b],
        effect_summary,
        rewrite_kind="observed-load",
    ) is True


def test_return_analyzer_effect_sensitive_rewrite_does_not_double_apply_outer_delta():
    value = Expression.parameter("value", 0, size=8)
    delta = Expression.parameter("delta", 1, size=4)
    negate = Expression.parameter("negate", 2, size=4)
    value_nonnull = Condition(
        Expression.binary_op("INT_NOTEQUAL", value, Expression.constant(0, 8)),
        False,
    )
    negate_zero = Condition(
        Expression.binary_op("INT_EQUAL", negate, Expression.constant(0, 4)),
        False,
    )
    negate_nonzero = negate_zero.negate()

    analyzer = ReturnAnalyzer(program=object(), debug=False)
    analyzer._current_parameters = [
        _param("value", size=8, is_signed=False),
        _param("delta", size=4, index=1),
        _param("negate", size=4, index=2),
    ]
    analyzer._current_effect_summary = EffectSummary(
        parameter_names=["value", "delta", "negate"],
        effects=[
            StoreEffect(
                location=_loc("value", 0, 4),
                value=Expression.binary_op("INT_ADD", Expression.memory(value, size=4), delta),
                conditions=[value_nonnull, negate_zero],
                order_key=5,
            ),
            StoreEffect(
                location=_loc("value", 0, 4),
                value=Expression.binary_op("INT_SUB", delta, Expression.memory(value, size=4)),
                conditions=[value_nonnull, negate_nonzero],
                order_key=5,
            ),
        ],
    )

    results = analyzer._build_return_infos_from_expansions(
        "00100000",
        [
            ExpandedValue(
                Expression.binary_op("INT_ADD", Expression.memory(value, size=4), delta),
                [value_nonnull, negate_nonzero],
            )
        ],
        return_index=0,
    )

    assert len(results) == 1
    assert results[0].value.to_string() == "(delta - MEM[value])"


def test_return_analyzer_materializes_normalized_composite_effect_value_at_root():
    dst = Expression.parameter("dst", 0, size=8)
    src = Expression.parameter("src", 1, size=8)
    copy_flag = Expression.parameter("copy_flag", 2, size=4)
    dst_nonnull = Condition(
        Expression.binary_op("INT_NOTEQUAL", dst, Expression.constant(0, 8)),
        False,
    )
    src_nonnull = Condition(
        Expression.binary_op("INT_NOTEQUAL", src, Expression.constant(0, 8)),
        False,
    )
    accumulate_taken = Condition(
        Expression.binary_op("INT_EQUAL", copy_flag, Expression.constant(0, 4)),
        False,
    )

    analyzer = ReturnAnalyzer(program=object(), debug=False)
    analyzer._current_parameters = [
        _param("dst", size=8, is_signed=False),
        _param("src", size=8, is_signed=False, index=1),
        _param("copy_flag", size=4, is_signed=False, index=2),
    ]
    effect_summary = EffectSummary(
        parameter_names=["dst", "src", "copy_flag"],
        effects=[
            StoreEffect(
                location=_loc("dst", 0, 4),
                value=Expression.binary_op(
                    "INT_ADD",
                    Expression.memory(dst, size=4, read_order_key=10),
                    Expression.memory(src, size=4, read_order_key=11),
                ),
                conditions=[dst_nonnull, src_nonnull, accumulate_taken],
                order_key=7,
            ),
        ],
    )

    stale_replayed = Expression.binary_op(
        "INT_ADD",
        Expression.binary_op(
            "INT_ADD",
            Expression.memory(dst, size=4, runtime_ref=_loc("dst", 0, 4)),
            Expression.memory(src, size=4, runtime_ref=_loc("src", 0, 4)),
        ),
        Expression.memory(src, size=4, runtime_ref=_loc("src", 0, 4)),
    )

    normalized = analyzer._normalize_return_value_with_effect_summary(
        stale_replayed,
        [dst_nonnull, src_nonnull, accumulate_taken],
        effect_summary,
    )

    assert normalized is not None
    assert normalized.to_string() == "(MEM[dst] + MEM[src])"
    assert isinstance(getattr(normalized, "runtime_ref", None), PostStateValueRef)
    assert normalized.runtime_ref.location == _loc("dst", 0, 4)


def test_return_analyzer_rewrite_prefers_precise_object_state_carrier_for_observed_effect_value():
    dst = Expression.parameter("dst", 0, size=8)
    src = Expression.parameter("src", 1, size=8)
    copy_flag = Expression.parameter("copy_flag", 2, size=4)
    dst_nonnull = Condition(
        Expression.binary_op("INT_NOTEQUAL", dst, Expression.constant(0, 8)),
        False,
    )
    src_nonnull = Condition(
        Expression.binary_op("INT_NOTEQUAL", src, Expression.constant(0, 8)),
        False,
    )
    accumulate_taken = Condition(
        Expression.binary_op("INT_EQUAL", copy_flag, Expression.constant(0, 4)),
        False,
    )

    analyzer = ReturnAnalyzer(program=object(), debug=False)
    analyzer._current_parameters = [
        _param("dst", size=8, is_signed=False),
        _param("src", size=8, is_signed=False, index=1),
        _param("copy_flag", size=4, is_signed=False, index=2),
    ]
    effect_summary = EffectSummary(
        parameter_names=["dst", "src", "copy_flag"],
        effects=[
            StoreEffect(
                location=_loc("dst", 0, 4),
                value=Expression.binary_op(
                    "INT_ADD",
                    Expression.memory(
                        dst,
                        size=4,
                        read_order_key=10,
                        runtime_ref=_observed_read("dst", index=0, size=4, order_key=10),
                    ),
                    Expression.memory(
                        src,
                        size=4,
                        read_order_key=11,
                        runtime_ref=_observed_read("src", index=0, size=4, order_key=11),
                    ),
                ),
                conditions=[dst_nonnull, src_nonnull, accumulate_taken],
                order_key=7,
            ),
        ],
    )
    original = Expression.binary_op(
        "INT_ADD",
        Expression.memory(
            dst,
            size=4,
            read_order_key=10,
            runtime_ref=_observed_read("dst", index=0, size=4, order_key=10),
        ),
        Expression.memory(
            src,
            size=4,
            read_order_key=11,
            runtime_ref=_observed_read("src", index=0, size=4, order_key=11),
        ),
    )

    rewritten = analyzer._rewrite_effect_sensitive_return_value(
        original,
        [dst_nonnull, src_nonnull, accumulate_taken],
        effect_summary,
    )

    assert rewritten is not None
    assert rewritten.to_string() == "(MEM[dst] + MEM[src])"
    assert isinstance(getattr(rewritten, "runtime_ref", None), PostStateValueRef)
    assert rewritten.runtime_ref.location == _loc("dst", 0, 4)


def test_build_return_infos_materializes_observed_effect_value_before_generic_rewrite():
    dst = Expression.parameter("dst", 0, size=8)
    src = Expression.parameter("src", 1, size=8)
    copy_flag = Expression.parameter("copy_flag", 2, size=4)
    dst_nonnull = Condition(
        Expression.binary_op("INT_NOTEQUAL", dst, Expression.constant(0, 8)),
        False,
    )
    src_nonnull = Condition(
        Expression.binary_op("INT_NOTEQUAL", src, Expression.constant(0, 8)),
        False,
    )
    accumulate_taken = Condition(
        Expression.binary_op("INT_EQUAL", copy_flag, Expression.constant(0, 4)),
        False,
    )

    analyzer = ReturnAnalyzer(program=object(), debug=False)
    analyzer._current_parameters = [
        _param("dst", size=8, is_signed=False),
        _param("src", size=8, is_signed=False, index=1),
        _param("copy_flag", size=4, is_signed=False, index=2),
    ]
    analyzer._current_effect_summary = EffectSummary(
        parameter_names=["dst", "src", "copy_flag"],
        effects=[
            StoreEffect(
                location=_loc("dst", 0, 4),
                value=Expression.binary_op(
                    "INT_ADD",
                    Expression.memory(
                        dst,
                        size=4,
                        read_order_key=10,
                        runtime_ref=_observed_read("dst", index=0, size=4, order_key=10),
                    ),
                    Expression.memory(
                        src,
                        size=4,
                        read_order_key=11,
                        runtime_ref=_observed_read("src", index=0, size=4, order_key=11),
                    ),
                ),
                conditions=[dst_nonnull, src_nonnull, accumulate_taken],
                order_key=7,
            ),
        ],
    )

    results = analyzer._build_return_infos_from_expansions(
        "00100000",
        [
            ExpandedValue(
                Expression.binary_op(
                    "INT_ADD",
                    Expression.memory(
                        dst,
                        size=4,
                        read_order_key=10,
                        runtime_ref=_observed_read("dst", index=0, size=4, order_key=10),
                    ),
                    Expression.memory(
                        src,
                        size=4,
                        read_order_key=11,
                        runtime_ref=_observed_read("src", index=0, size=4, order_key=11),
                    ),
                ),
                [dst_nonnull, src_nonnull, accumulate_taken],
            )
        ],
        return_index=0,
    )

    assert len(results) == 1
    assert results[0].value.to_string() == "(MEM[dst] + MEM[src])"
    assert isinstance(getattr(results[0].value, "runtime_ref", None), PostStateValueRef)
    assert results[0].value.runtime_ref.location == _loc("dst", 0, 4)


def test_return_analyzer_splits_effect_sensitive_observed_load_returns_into_cases():
    a = Expression.parameter("param_1", 0, size=8)
    b = Expression.parameter("param_2", 1, size=8)
    nonnull_a = Condition(
        Expression.binary_op("INT_NOTEQUAL", a, Expression.constant(0, 8)),
        False,
    )
    nonnull_b = Condition(
        Expression.binary_op("INT_NOTEQUAL", b, Expression.constant(0, 8)),
        False,
    )
    swap_taken = Condition(
        Expression.binary_op("INT_SLESS", Expression.memory(b, size=4), Expression.memory(a, size=4)),
        False,
    )
    expr = Expression.binary_op(
        "INT_SUB",
        Expression.memory(a, size=4, read_order_key=20),
        Expression.memory(b, size=4, read_order_key=21),
    )

    analyzer = ReturnAnalyzer(program=object(), debug=False)
    analyzer._current_parameters = [
        _param("param_1", size=8, is_signed=False),
        _param("param_2", size=8, is_signed=False, index=1),
    ]
    analyzer._current_effect_summary = EffectSummary(
        parameter_names=["param_1", "param_2"],
        effects=[
            StoreEffect(
                location=_loc("param_1", 0, 4),
                value=Expression.memory(b, size=4),
                conditions=[swap_taken],
                order_key=10,
            ),
            StoreEffect(
                location=_loc("param_2", 0, 4),
                value=Expression.memory(a, size=4),
                conditions=[swap_taken],
                order_key=11,
            ),
        ],
    )

    results = analyzer._build_return_infos_from_expansions(
        "00100000",
        [ExpandedValue(expr, [nonnull_a, nonnull_b])],
        return_index=0,
    )

    assert len(results) == 2
    rendered = {
        info.value.to_string(): " ".join(cond.to_string() for cond in info.conditions)
        for info in results
    }
    assert rendered.keys() == {"(MEM[param_1] - MEM[param_2])", "(MEM[param_2] - MEM[param_1])"}
    assert "(param_1 != 0)" in rendered["(MEM[param_1] - MEM[param_2])"]
    assert "(param_2 != 0)" in rendered["(MEM[param_1] - MEM[param_2])"]
    assert "(not (MEM[param_2] < MEM[param_1]))" in rendered["(MEM[param_1] - MEM[param_2])"]
    assert "(param_1 != 0)" in rendered["(MEM[param_2] - MEM[param_1])"]
    assert "(param_2 != 0)" in rendered["(MEM[param_2] - MEM[param_1])"]
    assert "(MEM[param_2] < MEM[param_1])" in rendered["(MEM[param_2] - MEM[param_1])"]


def test_return_analyzer_keeps_already_split_observed_swap_case():
    a = Expression.parameter("param_1", 0, size=8)
    b = Expression.parameter("param_2", 1, size=8)
    nonnull_a = Condition(
        Expression.binary_op("INT_NOTEQUAL", a, Expression.constant(0, 8)),
        False,
    )
    nonnull_b = Condition(
        Expression.binary_op("INT_NOTEQUAL", b, Expression.constant(0, 8)),
        False,
    )
    swap_taken = Condition(
        Expression.binary_op("INT_SLESS", Expression.memory(b, size=4), Expression.memory(a, size=4)),
        False,
    )
    expr = Expression.binary_op(
        "INT_SUB",
        Expression.memory(
            b,
            size=4,
            runtime_ref=_observed_read("param_2", index=1, size=4, order_key=20),
        ),
        Expression.memory(
            a,
            size=4,
            runtime_ref=_observed_read("param_1", index=0, size=4, order_key=21),
        ),
    )

    analyzer = ReturnAnalyzer(program=object(), debug=False)
    analyzer._current_parameters = [
        _param("param_1", size=8, is_signed=False),
        _param("param_2", size=8, is_signed=False, index=1),
    ]
    analyzer._current_effect_summary = EffectSummary(
        parameter_names=["param_1", "param_2"],
        effects=[
            StoreEffect(
                location=_loc("param_1", 0, 4),
                value=Expression.memory(b, size=4),
                conditions=[swap_taken],
                order_key=10,
            ),
            StoreEffect(
                location=_loc("param_2", 0, 4),
                value=Expression.memory(a, size=4),
                conditions=[swap_taken],
                order_key=11,
            ),
        ],
    )

    results = analyzer._build_return_infos_from_expansions(
        "00100000",
        [ExpandedValue(expr, [nonnull_a, nonnull_b, swap_taken])],
        return_index=0,
    )

    assert len(results) == 1
    assert results[0].value.to_string() == "(MEM[param_2] - MEM[param_1])"
    assert {cond.to_string() for cond in results[0].conditions} == {
        "(param_1 != 0)",
        "(param_2 != 0)",
        "(MEM[param_2] < MEM[param_1])",
    }


def test_rewrite_observed_loads_uses_runtime_ref_provenance_when_read_order_key_is_missing():
    a = Expression.parameter("param_1", 0, size=8)
    b = Expression.parameter("param_2", 1, size=8)
    nonnull_a = Condition(
        Expression.binary_op("INT_NOTEQUAL", a, Expression.constant(0, 8)),
        False,
    )
    nonnull_b = Condition(
        Expression.binary_op("INT_NOTEQUAL", b, Expression.constant(0, 8)),
        False,
    )
    swap_taken = Condition(
        Expression.binary_op("INT_SLESS", Expression.memory(b, size=4), Expression.memory(a, size=4)),
        False,
    )
    expr = Expression.binary_op(
        "INT_SUB",
        Expression.memory(
            a,
            size=4,
            runtime_ref=_observed_read("param_1", index=0, size=4, order_key=20),
        ),
        Expression.memory(
            b,
            size=4,
            runtime_ref=_observed_read("param_2", index=1, size=4, order_key=21),
        ),
    )
    effects = [
        StoreEffect(
            location=_loc("param_1", 0, 4),
            value=Expression.memory(b, size=4),
            conditions=[swap_taken],
            order_key=10,
        ),
        StoreEffect(
            location=_loc("param_2", 0, 4),
            value=Expression.memory(a, size=4),
            conditions=[swap_taken],
            order_key=11,
        ),
    ]

    rewritten = rewrite_observed_loads_from_effects(
        expr,
        [nonnull_a, nonnull_b, swap_taken],
        effects,
        [_param("param_1", size=8, is_signed=False), _param("param_2", size=8, is_signed=False, index=1)],
    )

    assert rewritten is not None
    assert rewritten.to_string() == "(MEM[param_2] - MEM[param_1])"


def test_expression_expander_prefers_observed_rewrite_over_flat_raw_normalization(monkeypatch):
    import scripts.function_tracer_pcode.transform.expander as expander_module

    a = Expression.parameter("a", 0, size=8)
    b = Expression.parameter("b", 1, size=8)
    nonnull_a = Condition(Expression.binary_op("INT_NOTEQUAL", a, Expression.constant(0, 8)), False)
    nonnull_b = Condition(Expression.binary_op("INT_NOTEQUAL", b, Expression.constant(0, 8)), False)
    swap_taken = Condition(
        Expression.binary_op("INT_SLESS", Expression.memory(b, size=4), Expression.memory(a, size=4)),
        False,
    )
    traced = Expression.binary_op(
        "INT_SUB",
        Expression.memory(
            a,
            size=4,
            runtime_ref=_observed_read("a", index=0, size=4, order_key=20),
        ),
        Expression.memory(
            b,
            size=4,
            runtime_ref=_observed_read("b", index=1, size=4, order_key=21),
        ),
    )
    swapped = Expression.binary_op(
        "INT_SUB",
        Expression.memory(b, size=4),
        Expression.memory(a, size=4),
    )
    flattened = Expression.binary_op(
        "INT_SUB",
        Expression.memory(a, size=4),
        Expression.memory(b, size=4),
    )

    class FakeTracer:
        pass

    expander = ExpressionExpander(
        FakeTracer(),
        condition_tracker=None,
        debug=False,
        effect_summary=EffectSummary(
            parameter_names=["a", "b"],
            effects=[
                StoreEffect(
                    location=_loc("a", 0, 4),
                    value=Expression.memory(b, size=4),
                    conditions=[swap_taken],
                    order_key=10,
                )
            ],
        ),
        parameters=[
            _param("a", size=8, is_signed=False),
            _param("b", size=8, is_signed=False, index=1),
        ],
    )

    monkeypatch.setattr(
        expander_module,
        "rewrite_observed_loads_from_effects",
        lambda expr, *_args, **_kwargs: swapped if expr is traced else expr,
    )
    monkeypatch.setattr(
        expander_module,
        "normalize_post_state_expression",
        lambda expr, *_args, **_kwargs: flattened if expr is traced else expr,
    )

    canonicalized = expander._canonicalize_traced_expression(
        traced,
        [nonnull_a, nonnull_b],
    )

    assert canonicalized.to_string() == "(MEM[b] - MEM[a])"


def test_expression_expander_uses_whole_operation_shortcut_before_recursive_cartesian_combine(monkeypatch):
    a = Expression.parameter("a", 0, size=8)
    b = Expression.parameter("b", 1, size=8)
    nonnull_a = Condition(Expression.binary_op("INT_NOTEQUAL", a, Expression.constant(0, 8)), False)
    nonnull_b = Condition(Expression.binary_op("INT_NOTEQUAL", b, Expression.constant(0, 8)), False)
    swap_taken = Condition(
        Expression.binary_op("INT_SLESS", Expression.memory(b, size=4), Expression.memory(a, size=4)),
        False,
    )
    traced = Expression.binary_op(
        "INT_SUB",
        Expression.memory(
            a,
            size=4,
            runtime_ref=_observed_read("a", index=0, size=4, order_key=20),
        ),
        Expression.memory(
            b,
            size=4,
            runtime_ref=_observed_read("b", index=1, size=4, order_key=21),
        ),
    )

    class FakeDef:
        def getMnemonic(self):
            return "MULTIEQUAL"

    class FakeInput:
        def getDef(self):
            return FakeDef()

    class FakeTracer:
        debug = False

        def _trace_pcode_op(self, _op, depth=0, use_cache=False):
            return traced

    class FakeOp:
        def getMnemonic(self):
            return "INT_SUB"

        def getNumInputs(self):
            return 2

        def getInput(self, index):
            return FakeInput()

        def getOutput(self):
            class Out:
                def getSize(self):
                    return 4
            return Out()

    expander = ExpressionExpander(
        FakeTracer(),
        condition_tracker=None,
        debug=False,
        effect_summary=EffectSummary(
            parameter_names=["a", "b"],
            effects=[
                StoreEffect(
                    location=_loc("a", 0, 4),
                    value=Expression.memory(b, size=4),
                    conditions=[swap_taken],
                    order_key=10,
                ),
                StoreEffect(
                    location=_loc("b", 0, 4),
                    value=Expression.memory(a, size=4),
                    conditions=[swap_taken],
                    order_key=11,
                ),
            ],
        ),
        parameters=[
            _param("a", size=8, is_signed=False),
            _param("b", size=8, is_signed=False, index=1),
        ],
    )

    monkeypatch.setattr(
        expander,
        "_expand_input_varnode",
        lambda *_args, **_kwargs: (_ for _ in ()).throw(AssertionError("recursive combine should not run")),
    )

    expanded = expander._expand_input_operation(
        FakeOp(),
        [nonnull_a, nonnull_b],
        depth=0,
    )

    assert len(expanded) == 2
    rendered = {ev.value.to_string(): " ".join(cond.to_string() for cond in ev.conditions) for ev in expanded}
    assert rendered.keys() == {"(MEM[a] - MEM[b])", "(MEM[b] - MEM[a])"}


def test_return_analyzer_splits_effect_sensitive_canonical_memory_returns_without_observed_metadata():
    a = Expression.parameter("param_1", 0, size=8)
    b = Expression.parameter("param_2", 1, size=8)
    nonnull_a = Condition(
        Expression.binary_op("INT_NOTEQUAL", a, Expression.constant(0, 8)),
        False,
    )
    nonnull_b = Condition(
        Expression.binary_op("INT_NOTEQUAL", b, Expression.constant(0, 8)),
        False,
    )
    swap_taken = Condition(
        Expression.binary_op("INT_SLESS", Expression.memory(b, size=4), Expression.memory(a, size=4)),
        False,
    )
    expr = Expression.binary_op(
        "INT_SUB",
        Expression.memory(a, size=4),
        Expression.memory(b, size=4),
    )

    analyzer = ReturnAnalyzer(program=object(), debug=False)
    analyzer._current_parameters = [
        _param("param_1", size=8, is_signed=False),
        _param("param_2", size=8, is_signed=False, index=1),
    ]
    analyzer._current_effect_summary = EffectSummary(
        parameter_names=["param_1", "param_2"],
        effects=[
            StoreEffect(
                location=_loc("param_1", 0, 4),
                value=Expression.memory(b, size=4),
                conditions=[swap_taken],
                order_key=10,
            ),
            StoreEffect(
                location=_loc("param_2", 0, 4),
                value=Expression.memory(a, size=4),
                conditions=[swap_taken],
                order_key=11,
            ),
        ],
    )

    results = analyzer._build_return_infos_from_expansions(
        "00100004",
        [ExpandedValue(expr, [nonnull_a, nonnull_b])],
        return_index=0,
    )

    assert len(results) == 2
    rendered = {
        info.value.to_string(): " ".join(cond.to_string() for cond in info.conditions)
        for info in results
    }
    assert rendered.keys() == {"(MEM[param_1] - MEM[param_2])", "(MEM[param_2] - MEM[param_1])"}
    assert "(not (MEM[param_2] < MEM[param_1]))" in rendered["(MEM[param_1] - MEM[param_2])"]
    assert "(MEM[param_2] < MEM[param_1])" in rendered["(MEM[param_2] - MEM[param_1])"]


def test_return_analyzer_keeps_even_iteration_wrapper_when_definite_replay_would_change_meaning():
    trace = Expression.parameter("param_1", 0, size=8)
    start = Expression.parameter("param_2", 1, size=4)
    limit = Expression.parameter("param_3", 2, size=4)
    steps_addr = Expression.binary_op("INT_ADD", trace, Expression.constant(4, 8))

    trace_nonnull = Condition(
        Expression.binary_op("INT_NOTEQUAL", trace, Expression.constant(0, 8)),
        False,
    )
    loop_active = Condition(
        Expression.binary_op("INT_SLESS", start, limit),
        False,
    )
    even_iteration = Condition(
        Expression.binary_op(
            "INT_EQUAL",
            Expression.binary_op("INT_AND", start, Expression.constant(1, 4)),
            Expression.constant(0, 4),
        ),
        False,
    )
    final_iter = Condition(
        Expression.binary_op(
            "INT_EQUAL",
            limit,
            Expression.binary_op("INT_ADD", start, Expression.constant(1, 4)),
        ),
        False,
    )
    expr = Expression.binary_op(
        "INT_ADD",
        Expression.binary_op("INT_ADD", Expression.memory(trace, size=4), start),
        Expression.binary_op(
            "INT_SUB",
            Expression.binary_op(
                "INT_ADD",
                limit,
                Expression.memory(steps_addr, size=4),
            ),
            start,
        ),
    )
    wrapped_steps_effect = Expression.binary_op(
        "INT_SUB",
        Expression.binary_op(
            "INT_ADD",
            limit,
            Expression.binary_op(
                "INT_ADD",
                Expression.binary_op(
                    "INT_ADD",
                    Expression.memory(steps_addr, size=4),
                    Expression.constant(1, 4),
                ),
                Expression.binary_op("INT_SUB", start, start),
            ),
        ),
        start,
    )

    analyzer = ReturnAnalyzer(program=object(), debug=False)
    analyzer._current_effect_summary = EffectSummary(
        parameter_names=["param_1", "param_2", "param_3"],
        effects=[
            StoreEffect(
                location=_loc("param_1", 0, 4),
                value=Expression.binary_op(
                    "INT_ADD",
                    Expression.memory(trace, size=4),
                    start,
                ),
                conditions=[trace_nonnull, loop_active, even_iteration, final_iter],
                order_key=5,
            ),
            StoreEffect(
                location=_loc("param_1", 4, 4),
                value=wrapped_steps_effect,
                conditions=[trace_nonnull, loop_active, even_iteration, final_iter],
                order_key=6,
            ),
        ],
    )
    analyzer._current_parameters = [
        _param("param_1", size=8, is_signed=False),
        _param("param_2", size=4, index=1),
        _param("param_3", size=4, index=2),
    ]

    normalized = analyzer._normalize_expanded_return_value(
        expr,
        [trace_nonnull, loop_active, even_iteration, final_iter],
    )

    assert normalized.to_string() == "((MEM[param_1] + param_2) + ((param_3 + MEM[(param_1 + 4)]) - param_2))"


def test_expression_expander_expands_observed_load_phi_difference_into_cases():
    a = Expression.parameter("a", 0, size=8)
    b = Expression.parameter("b", 1, size=8)
    nonnull_a = Condition(Expression.binary_op("INT_NOTEQUAL", a, Expression.constant(0, 8)), False)
    nonnull_b = Condition(Expression.binary_op("INT_NOTEQUAL", b, Expression.constant(0, 8)), False)
    swap_taken = Condition(
        Expression.binary_op("INT_SLESS", Expression.memory(b, size=4), Expression.memory(a, size=4)),
        False,
    )
    traced = Expression.binary_op(
        "INT_SUB",
        Expression.memory(a, size=4, read_order_key=20),
        Expression.memory(b, size=4, read_order_key=21),
    )
    effect_summary = EffectSummary(
        parameter_names=["a", "b"],
        effects=[
            StoreEffect(
                location=_loc("a", 0, 4),
                value=Expression.memory(b, size=4),
                conditions=[swap_taken],
                order_key=10,
            ),
            StoreEffect(
                location=_loc("b", 0, 4),
                value=Expression.memory(a, size=4),
                conditions=[swap_taken],
                order_key=11,
            ),
        ],
    )

    class FakeTracer:
        def _trace_pcode_op(self, _op, depth=0, use_cache=False):
            return traced

    class FakeOp:
        def getMnemonic(self):
            return "INT_SUB"

        def getNumInputs(self):
            return 2

        def getInput(self, index):
            class In:
                def getDef(self):
                    return None
            return In()

        def getOutput(self):
            class Out:
                def getSize(self):
                    return 4
            return Out()

    expander = ExpressionExpander(
        FakeTracer(),
        condition_tracker=None,
        debug=False,
        effect_summary=effect_summary,
        parameters=[
            _param("a", size=8, is_signed=False),
            _param("b", size=8, is_signed=False, index=1),
        ],
    )

    expanded = expander._expand_input_operation(
        FakeOp(),
        [nonnull_a, nonnull_b],
        depth=0,
    )

    assert len(expanded) == 2
    rendered = {ev.value.to_string(): " ".join(cond.to_string() for cond in ev.conditions) for ev in expanded}
    assert rendered.keys() == {"(MEM[a] - MEM[b])", "(MEM[b] - MEM[a])"}
    assert "(a != 0)" in rendered["(MEM[a] - MEM[b])"]
    assert "(b != 0)" in rendered["(MEM[a] - MEM[b])"]
    assert "(not (MEM[b] < MEM[a]))" in rendered["(MEM[a] - MEM[b])"]
    assert "(a != 0)" in rendered["(MEM[b] - MEM[a])"]
    assert "(b != 0)" in rendered["(MEM[b] - MEM[a])"]
    assert "(MEM[b] < MEM[a])" in rendered["(MEM[b] - MEM[a])"]


def test_expression_expander_multiequal_shortcut_defers_flattened_observed_load_rewrite(monkeypatch):
    import scripts.function_tracer_pcode.transform.expander as expander_module

    a = Expression.parameter("a", 0, size=8)
    b = Expression.parameter("b", 1, size=8)
    nonnull_a = Condition(Expression.binary_op("INT_NOTEQUAL", a, Expression.constant(0, 8)), False)
    nonnull_b = Condition(Expression.binary_op("INT_NOTEQUAL", b, Expression.constant(0, 8)), False)
    swap_taken = Condition(
        Expression.binary_op("INT_SLESS", Expression.memory(b, size=4), Expression.memory(a, size=4)),
        False,
    )
    traced = Expression.binary_op(
        "INT_SUB",
        Expression.memory(a, size=4, read_order_key=20),
        Expression.memory(b, size=4, read_order_key=21),
    )
    flattened = Expression.binary_op(
        "INT_SUB",
        Expression.memory(a, size=4),
        Expression.memory(b, size=4),
    )
    rewritten_phi = Expression.binary_op(
        "INT_SUB",
        Expression.phi(
            [
                (swap_taken, Expression.memory(b, size=4)),
                (None, Expression.memory(a, size=4)),
            ]
        ),
        Expression.phi(
            [
                (swap_taken, Expression.memory(a, size=4)),
                (None, Expression.memory(b, size=4)),
            ]
        ),
    )
    rewritten_phi.operands[0].size = 4
    rewritten_phi.operands[1].size = 4
    effect_summary = EffectSummary(
        parameter_names=["a", "b"],
        effects=[
            StoreEffect(
                location=_loc("a", 0, 4),
                value=Expression.memory(b, size=4),
                conditions=[swap_taken],
                order_key=10,
            ),
            StoreEffect(
                location=_loc("b", 0, 4),
                value=Expression.memory(a, size=4),
                conditions=[swap_taken],
                order_key=11,
            ),
        ],
    )

    class FakeTracer:
        def trace_varnode(self, _varnode, depth=0, use_cache=False):
            return traced

    expander = ExpressionExpander(
        FakeTracer(),
        condition_tracker=None,
        debug=False,
        effect_summary=effect_summary,
        parameters=[
            _param("a", size=8, is_signed=False),
            _param("b", size=8, is_signed=False, index=1),
        ],
    )

    monkeypatch.setattr(
        expander,
        "_canonicalize_traced_expression",
        lambda _expr, _conditions: flattened,
    )
    monkeypatch.setattr(
        expander_module,
        "rewrite_observed_loads_from_effects",
        lambda _expr, _conditions, _effects, _parameters: rewritten_phi,
    )

    result = expander._trace_and_canonicalize_input_value(
        object(),
        [nonnull_a, nonnull_b],
        depth=0,
    )

    assert result is None


def test_canonicalize_post_state_subexpressions_rewrites_phi_operand_to_memory_location():
    a = Expression.parameter("a", 0, size=8)
    b = Expression.parameter("b", 1, size=8)
    swap_taken = Condition(
        Expression.binary_op("INT_SLESS", Expression.memory(b, size=4), Expression.memory(a, size=4)),
        False,
    )
    expr = Expression.binary_op(
        "INT_SUB",
        Expression.memory(a, size=4),
        Expression.phi(
            [
                (swap_taken, Expression.memory(a, size=4)),
                (None, Expression.memory(b, size=4)),
            ]
        ),
    )
    expr.operands[1].size = 4
    effects = [
        StoreEffect(
            location=_loc("a", 0, 4),
            value=Expression.memory(b, size=4),
            conditions=[swap_taken],
            order_key=1,
        ),
        StoreEffect(
            location=_loc("b", 0, 4),
            value=Expression.memory(a, size=4),
            conditions=[swap_taken],
            order_key=2,
        ),
    ]

    normalized = canonicalize_post_state_subexpressions(
        expr,
        [swap_taken],
        effects,
        [
            _param("a", size=8, is_signed=False),
            _param("b", size=8, is_signed=False, index=1),
        ],
    )

    assert normalized.to_string() == "(MEM[a] - MEM[b])"


def test_effect_summary_does_not_reapply_alias_equivalent_store_inside_rhs():
    dst = Expression.parameter("dst", 0, size=8)
    src = Expression.parameter("src", 1, size=8)
    delta = Expression.parameter("delta", 2, size=4)
    alias_cond = Condition(
        Expression.binary_op("INT_EQUAL", dst, src),
        False,
    )
    original = Expression.memory(src, size=4)
    effect = StoreEffect(
        location=_loc("dst", 0, 4),
        value=Expression.binary_op("INT_ADD", Expression.memory(dst, size=4), delta),
        conditions=[alias_cond],
        order_key=4,
    )

    rewritten = rewrite_loads_from_effects(
        original,
        [alias_cond],
        [effect],
        [
            _param("dst", size=8, is_signed=False),
            _param("src", size=8, is_signed=False, index=1),
            _param("delta", size=4, index=2),
        ],
    )

    assert rewritten.to_string() == "(MEM[dst] + delta)"


def test_effect_summary_does_not_reapply_when_expr_matches_phi_branch_value():
    dst = Expression.parameter("dst", 0, size=8)
    src = Expression.parameter("src", 1, size=8)
    choose_src = Expression.parameter("choose_src", 2, size=4)
    choose_true = Condition(
        Expression.binary_op("INT_NOTEQUAL", choose_src, Expression.constant(0, 4)),
        False,
    )
    choose_false = choose_true.negate()
    original = Expression.binary_op("INT_ADD", Expression.memory(dst, size=4), Expression.constant(1, 4))
    effect = StoreEffect(
        location=_loc("dst", 0, 4),
        value=Expression.phi(
            [
                (choose_true, Expression.memory(src, size=4)),
                (None, Expression.binary_op("INT_ADD", Expression.memory(dst, size=4), Expression.constant(1, 4))),
            ]
        ),
        conditions=[],
        order_key=3,
    )

    rewritten = rewrite_loads_from_effects(
        original,
        [choose_false],
        [effect],
        [
            _param("dst", size=8, is_signed=False),
            _param("src", size=8, is_signed=False, index=1),
            _param("choose_src", size=4, index=2),
        ],
    )

    assert rewritten.to_string() == "(MEM[dst] + 1)"


def test_effect_summary_does_not_reapply_when_expr_matches_true_phi_branch_value():
    dst = Expression.parameter("dst", 0, size=8)
    src = Expression.parameter("src", 1, size=8)
    choose_src = Expression.parameter("choose_src", 2, size=4)
    choose_true = Condition(
        Expression.binary_op("INT_NOTEQUAL", choose_src, Expression.constant(0, 4)),
        False,
    )
    original = Expression.memory(src, size=4)
    effect = StoreEffect(
        location=_loc("dst", 0, 4),
        value=Expression.phi(
            [
                (choose_true, Expression.memory(src, size=4)),
                (None, Expression.binary_op("INT_ADD", Expression.memory(dst, size=4), Expression.constant(1, 4))),
            ]
        ),
        conditions=[],
        order_key=3,
    )

    rewritten = rewrite_loads_from_effects(
        original,
        [choose_true],
        [effect],
        [
            _param("dst", size=8, is_signed=False),
            _param("src", size=8, is_signed=False, index=1),
            _param("choose_src", size=4, index=2),
        ],
    )

    assert rewritten.to_string() == "MEM[src]"


def test_effect_summary_resolves_callind_target_from_traced_constant():
    class FakeVarnode:
        def __init__(self, is_constant=False):
            self._is_constant = is_constant

        def isConstant(self):
            return self._is_constant

    class FakeAddressSpace:
        def getAddress(self, value):
            return value

    class FakeAddressFactory:
        def getDefaultAddressSpace(self):
            return FakeAddressSpace()

    class FakeFunction:
        def __init__(self, name):
            self._name = name

        def getName(self):
            return self._name

    class FakeFunctionManager:
        def getFunctionAt(self, addr):
            if addr == 0x401000:
                return FakeFunction("callee")
            return None

    class FakeProgram:
        def getAddressFactory(self):
            return FakeAddressFactory()

        def getFunctionManager(self):
            return FakeFunctionManager()

    class FakeTracer:
        def __init__(self):
            self.program = FakeProgram()

        def _get_function_name(self, _addr_varnode):
            return "UNKNOWN_FUNC"

        def trace_varnode(self, _varnode, use_cache=False):
            return Expression.constant(0x401000, 8)

    class FakeOp:
        def __init__(self):
            self._input = FakeVarnode(is_constant=False)

        def getNumInputs(self):
            return 1

        def getInput(self, index):
            assert index == 0
            return self._input

        def getMnemonic(self):
            return "CALLIND"

    assert _resolve_call_target_name(FakeTracer(), FakeOp()) == "callee"


def test_effect_summary_resolves_call_target_from_traced_constant():
    class FakeVarnode:
        def __init__(self, is_constant=False):
            self._is_constant = is_constant

        def isConstant(self):
            return self._is_constant

    class FakeAddressSpace:
        def getAddress(self, value):
            return value

    class FakeAddressFactory:
        def getDefaultAddressSpace(self):
            return FakeAddressSpace()

    class FakeFunction:
        def __init__(self, name):
            self._name = name

        def getName(self):
            return self._name

    class FakeFunctionManager:
        def getFunctionAt(self, addr):
            if addr == 0x401000:
                return FakeFunction("callee")
            return None

        def getFunctionContaining(self, addr):
            return self.getFunctionAt(addr)

    class FakeProgram:
        def getAddressFactory(self):
            return FakeAddressFactory()

        def getFunctionManager(self):
            return FakeFunctionManager()

    class FakeTracer:
        def __init__(self):
            self.program = FakeProgram()

        def _get_function_name(self, _addr_varnode):
            return "UNKNOWN_FUNC"

        def trace_varnode(self, _varnode, use_cache=False):
            return Expression.constant(0x401000, 8)

    class FakeOp:
        def __init__(self):
            self._input = FakeVarnode(is_constant=False)

        def getNumInputs(self):
            return 1

        def getInput(self, index):
            assert index == 0
            return self._input

        def getMnemonic(self):
            return "CALL"

    assert _resolve_call_target_name(FakeTracer(), FakeOp()) == "callee"


def test_effect_summary_prefers_traced_constant_over_synthetic_fun_name():
    class FakeVarnode:
        def __init__(self, is_constant=False):
            self._is_constant = is_constant

        def isConstant(self):
            return self._is_constant

    class FakeAddressSpace:
        def getAddress(self, value):
            return value

    class FakeAddressFactory:
        def getDefaultAddressSpace(self):
            return FakeAddressSpace()

    class FakeFunction:
        def __init__(self, name):
            self._name = name

        def getName(self):
            return self._name

    class FakeFunctionManager:
        def getFunctionAt(self, addr):
            if addr == 0x401000:
                return FakeFunction("callee")
            return None

        def getFunctionContaining(self, addr):
            return self.getFunctionAt(addr)

    class FakeProgram:
        def getAddressFactory(self):
            return FakeAddressFactory()

        def getFunctionManager(self):
            return FakeFunctionManager()

    class FakeTracer:
        def __init__(self):
            self.program = FakeProgram()

        def _get_function_name(self, _addr_varnode):
            return "FUN_401000"

        def trace_varnode(self, _varnode, use_cache=False):
            return Expression.constant(0x401000, 8)

    class FakeOp:
        def __init__(self):
            self._input = FakeVarnode(is_constant=False)

        def getNumInputs(self):
            return 1

        def getInput(self, index):
            assert index == 0
            return self._input

        def getMnemonic(self):
            return "CALL"

    assert _resolve_call_target_name(FakeTracer(), FakeOp()) == "callee"


def test_effect_summary_returns_code_address_target_ref_for_raw_local_target():
    class FakeVarnode:
        def __init__(self):
            self._address = None

        def getAddress(self):
            return self._address

    class FakeAddressSpace:
        def getAddress(self, value):
            return value

    class FakeAddressFactory:
        def getDefaultAddressSpace(self):
            return FakeAddressSpace()

    class FakeFunctionManager:
        def getFunctionAt(self, _addr):
            return None

        def getFunctionContaining(self, _addr):
            return None

    class FakeProgram:
        def getAddressFactory(self):
            return FakeAddressFactory()

        def getFunctionManager(self):
            return FakeFunctionManager()

    class FakeTracer:
        def __init__(self):
            self.program = FakeProgram()

        def _get_function_name(self, _addr_varnode):
            return "UNKNOWN_FUNC"

        def trace_varnode(self, _varnode, use_cache=False):
            return Expression.constant(0x401234, 8)

    class FakeOp:
        def __init__(self):
            self._input = FakeVarnode()

        def getNumInputs(self):
            return 1

        def getInput(self, index):
            assert index == 0
            return self._input

        def getMnemonic(self):
            return "CALLIND"

    target_ref = _resolve_call_target_ref(FakeTracer(), FakeOp())

    assert target_ref is not None
    assert target_ref.is_code_address() is True
    assert target_ref.address_offset == 0x401234
    assert target_ref.display_name() == "ADDR_401234"


def test_call_effect_summary_policy_accepts_simple_param_store_summary():
    summary = EffectSummary(
        parameter_names=["ptr", "value"],
        effects=[
            StoreEffect(
                location=_loc("ptr", 0, 4),
                value=Expression.binary_op(
                    "INT_ADD",
                    Expression.memory(Expression.parameter("ptr", 0, size=8), size=4),
                    Expression.parameter("value", 1, size=4),
                ),
                conditions=[],
                order_key=1,
            )
        ],
    )

    assert is_call_effect_summary_allowed(summary)


def test_call_effect_summary_policy_rejects_nested_call_values():
    summary = EffectSummary(
        parameter_names=["ptr"],
        effects=[
            StoreEffect(
                location=_loc("ptr", 0, 4),
                value=Expression.call("callee", [Expression.parameter("ptr", 0, size=8)]),
                conditions=[],
                order_key=1,
            )
        ],
    )

    assert not is_call_effect_summary_allowed(summary)


def test_call_effect_summary_policy_rejects_unsupported_nested_calls():
    summary = EffectSummary(
        parameter_names=["ptr"],
        effects=[
            StoreEffect(
                location=_loc("ptr", 0, 4),
                value=Expression.constant(1, 4),
                conditions=[],
                order_key=1,
            )
        ],
        has_unsupported_call=True,
    )

    assert not is_call_effect_summary_allowed(summary)


def test_call_effect_summary_policy_rejects_incomplete_summary():
    summary = EffectSummary(
        parameter_names=["ptr"],
        effects=[
            StoreEffect(
                location=_loc("ptr", 0, 4),
                value=Expression.constant(1, 4),
                conditions=[],
                order_key=1,
            )
        ],
        incomplete_reasons=("effect_summary_path_coverage_incomplete",),
    )

    assert not is_call_effect_summary_allowed(summary)


def test_expander_combines_load_inputs_into_memory_expression():
    tracer = type("Tracer", (), {"debug": False})()
    expander = ExpressionExpander(tracer, condition_tracker=None, debug=False)

    result = expander._combine_input_expansions_with_conditions(
        "LOAD",
        [
            [ExpandedValue(Expression.constant(0x1B1, 4), [])],
            [ExpandedValue(Expression.parameter("ptr", 0, size=8), [])],
        ],
        [],
        0,
        output_size=4,
    )

    assert len(result) == 1
    assert result[0].value.expr_type.name == "MEMORY"
    assert result[0].value.to_string() == "MEM[ptr]"


def test_expander_resolves_indirect_stack_slot_read_via_effect_summary():
    class FakeOutputVarnode:
        def getHigh(self):
            return None

    class FakeTracer:
        debug = False

        def _get_storage_info_from_varnode(self, _varnode):
            return StorageInfo(**_stack_storage(-0x1C, size_bytes=4))

    expander = ExpressionExpander(
        FakeTracer(),
        condition_tracker=None,
        debug=False,
        effect_summary=EffectSummary(
            parameter_names=["a", "b"],
            effects=[
                StoreEffect(
                    location=_loc("__locbase__stackframe", -0x1C, 4),
                    value=Expression.binary_op(
                        "INT_ADD",
                        Expression.parameter("a", 0, size=4),
                        Expression.parameter("b", 1, size=4),
                    ),
                    conditions=[],
                    order_key=1,
                )
            ],
        ),
        parameters=[
            _param("a", size=4, is_signed=False, index=0),
            _param("b", size=4, is_signed=False, index=1),
        ],
    )

    result = expander._combine_input_expansions_with_conditions(
        "INDIRECT",
        [
            [ExpandedValue(Expression.constant(0, 4), [])],
            [ExpandedValue(Expression.constant(0x28, 4), [])],
        ],
        [],
        0,
        output_size=4,
        output_varnode=FakeOutputVarnode(),
    )

    assert len(result) == 1
    assert result[0].value.to_string() == "(a + b)"


def test_type_fixer_does_not_pattern_fix_pointer_types():
    fixer = object.__new__(TypeFixer)
    fixer.config = TypeFixerConfig()
    fixer.debug = False

    assert fixer._should_fix_type(resolve_mock_data_type("undefined4"))
    assert not fixer._should_fix_type("undefined4 *")


def test_tracer_get_function_name_accepts_ram_address_varnode():
    class _FakeFunction:
        def __init__(self, name):
            self._name = name

        def getName(self):
            return self._name

    class _FakeFunctionManager:
        def __init__(self, containing):
            self._containing = containing

        def getFunctionAt(self, _addr):
            return None

        def getFunctionContaining(self, _addr):
            return self._containing

    class _FakeProgram:
        def __init__(self, containing):
            self._manager = _FakeFunctionManager(containing)

        def getFunctionManager(self):
            return self._manager

    class _FakeSpace:
        def isRegisterSpace(self):
            return False

        def isUniqueSpace(self):
            return False

        def isConstantSpace(self):
            return False

    class _FakeAddress:
        def __init__(self, offset):
            self._offset = offset
            self._space = _FakeSpace()

        def getAddressSpace(self):
            return self._space

        def getOffset(self):
            return self._offset

    class _FakeVarnode:
        def __init__(self, offset):
            self._address = _FakeAddress(offset)

        def isConstant(self):
            return False

        def getAddress(self):
            return self._address

    tracer = object.__new__(PcodeTracer)
    tracer.program = _FakeProgram(_FakeFunction("mem_void_write_if_needed"))

    resolved = tracer._get_function_name(_FakeVarnode(0x120001514))

    assert resolved == "mem_void_write_if_needed"

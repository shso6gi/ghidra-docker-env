# -*- coding: utf-8 -*-

from scripts.function_tracer_pcode.analysis.memory_resolver import (
    collect_memory_bit_widths_from_analysis,
    concretize_readonly_loads,
)
from scripts.function_tracer_pcode.analysis.effect_summary import (
    CanonicalLocation,
    StoreEffect,
    _resolve_call_target_name,
    subtract_implied_conditions,
    is_call_effect_summary_allowed,
    build_void_effect_summary_expr,
    canonicalize_param_location,
    canonicalize_post_state_subexpressions,
    collapse_post_state_expr_to_canonical_memory,
    collapse_pruned_post_state_memory_leaf_to_canonical_memory,
    rewrite_loads_from_effects,
    rewrite_observed_loads_from_effects,
    summarize_store_effects,
    substitute_location,
    _choose_effect_substitution_args,
    _resolve_call_argument_expression,
    _normalize_call_argument_expression,
    EffectSummary,
)
from scripts.function_tracer_pcode.analysis.analyzer import ReturnAnalyzer
from scripts.function_tracer_pcode.analysis.phi_resolver import ExpandedBranch as PhiExpandedBranch, PhiHandler
from scripts.function_tracer_pcode.analysis.tracer import PcodeTracer
from scripts.function_tracer_pcode.equivalence.typing.fixer import TypeFixer, TypeFixerConfig
from scripts.function_tracer_pcode.equivalence.arch.mips64 import MIPS64Handler
from scripts.function_tracer_pcode.equivalence.formula.builder import FormulaBuilder
from scripts.function_tracer_pcode.model import Condition, Expression, FunctionReturnAnalysis, ReturnInfo
from scripts.function_tracer_pcode.model.storage import StorageInfo
from scripts.function_tracer_pcode.transform.expander import ExpressionExpander, ExpandedValue


def _param(
    name: str,
    size: int = 4,
    is_signed: bool = True,
    index: int = 0,
    storage=None,
):
    result = {"name": name, "size": size, "is_signed": is_signed, "index": index}
    if storage is not None:
        result["storage"] = storage
    return result


def _reg_storage(base_name: str, size_bytes: int = 8, register_name: str = None):
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
        parameters=[{"name": "param_1", "data_type": "long", "size": 8, "is_signed": True}],
        returns=[],
    )
    analysis2 = FunctionReturnAnalysis(
        function_name="f2",
        entry_point="0x0",
        parameters=[{"name": "param_1", "data_type": "long", "size": 8, "is_signed": True}],
        returns=[],
    )

    handler._analyze_parameter_usage = lambda analysis: {"param_1": ("signed", 32)}

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
        Expression.variable("PTR_00112058", size=8),
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


def test_memory_resolver_concretizes_jump_table_when_additive_index_is_wrapped_by_mul_one():
    param = Expression.parameter("param_1", 0, size=8)
    subpiece = Expression.binary_op("SUBPIECE", param, Expression.constant(0, 4))
    subpiece.size = 4
    index_expr = Expression.unary_op("INT_SEXT", subpiece)
    index_expr.size = 8
    address_expr = Expression.binary_op(
        "INT_ADD",
        Expression.variable("PTR_00112058", size=8),
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
        Expression.variable("PTR_00112058", size=8),
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
        Expression.variable("PTR___DT_MIPS_BASE_ADDRESS_120011050", size=8),
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
        location=CanonicalLocation("ptr", 0, 4),
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
            location=CanonicalLocation("ptr", 0, 4),
            value=value,
            conditions=[positive],
            order_key=2,
        ),
        StoreEffect(
            location=CanonicalLocation("ptr", 0, 4),
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
    addr_expr = Expression.variable("ptr", size=8)

    location = canonicalize_param_location(
        addr_expr,
        [_param("ptr", size=8, is_signed=False)],
        size=4,
    )

    assert location == CanonicalLocation("ptr", 0, 4)


def test_effect_summary_accepts_variable_plus_constant_parameter_addresses():
    addr_expr = Expression.binary_op(
        "INT_ADD",
        Expression.variable("box", size=8),
        Expression.constant(4, 8),
    )

    location = canonicalize_param_location(
        addr_expr,
        [_param("box", size=8, is_signed=False)],
        size=4,
    )

    assert location == CanonicalLocation("box", 4, 4)


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

    assert location == CanonicalLocation("param_1", 0, 4)


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
        CanonicalLocation("a", 0, 4),
        ["a", "b"],
        call_args,
        [
            _param("param_1", size=8, is_signed=False, storage=_reg_storage("A0")),
            _param("param_2", size=8, is_signed=False, index=1, storage=_reg_storage("A1")),
        ],
    )

    assert substituted == CanonicalLocation("param_1", 0, 4)


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


def test_normalize_call_argument_expression_falls_back_to_positional_parameter():
    unresolved = Expression.variable("opaque_arg", size=8)

    normalized = _normalize_call_argument_expression(
        unresolved,
        1,
        [
            _param("param_1", size=8, is_signed=False, index=0),
            _param("param_2", size=8, is_signed=False, index=1),
        ],
    )

    assert normalized.expr_type.name == "PARAMETER"
    assert normalized.name == "param_2"


def test_choose_effect_substitution_args_retries_with_positional_parameters():
    chosen = _choose_effect_substitution_args(
        CanonicalLocation("a", 0, 4),
        ["a", "b"],
        [Expression.variable("opaque0", size=8), Expression.variable("opaque1", size=8)],
        [
            _param("param_1", size=8, is_signed=False, index=0),
            _param("param_2", size=8, is_signed=False, index=1),
        ],
    )

    assert chosen[0].expr_type.name == "PARAMETER"
    assert chosen[0].name == "param_1"
    assert chosen[1].expr_type.name == "PARAMETER"
    assert chosen[1].name == "param_2"


def test_summarize_store_effects_recovers_argumentless_call_via_matching_parameter_storage():
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

        def _get_function_name(self, _varnode):
            return "callee"

        def get_all_pcode_ops(self):
            return [self._op]

        def _get_storage_info_from_varnode(self, _varnode):
            return None

    call_op = FakeCallOp()
    captured_args = {}

    def _direct_call_summary(_name, args):
        captured_args["args"] = list(args)
        return EffectSummary(
            parameter_names=["a", "b"],
            effects=[
                StoreEffect(
                    location=CanonicalLocation("a", 0, 4),
                    value=Expression.memory(Expression.parameter("b", 1, size=8), size=4),
                    conditions=[],
                    order_key=1,
                ),
                StoreEffect(
                    location=CanonicalLocation("b", 0, 4),
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
        resolve_callee_parameters=lambda _name: [
            _param("a", size=8, is_signed=False, index=0, storage=_reg_storage("x0", register_name="x0")),
            _param("b", size=8, is_signed=False, index=1, storage=_reg_storage("x1", register_name="x1")),
        ],
        debug=False,
    )

    assert [arg.name for arg in captured_args["args"]] == ["param_1", "param_2"]
    assert len(summary.effects) == 2
    assert summary.effects[0].location == CanonicalLocation("param_1", 0, 4)
    assert summary.effects[0].value.to_string() == "MEM[param_2]"
    assert summary.effects[1].location == CanonicalLocation("param_2", 0, 4)
    assert summary.effects[1].value.to_string() == "MEM[param_1]"


def test_effect_summary_accepts_mul_by_one_wrapped_parameter_addresses():
    addr_expr = Expression.binary_op(
        "INT_MULT",
        Expression.constant(1, 8),
        Expression.binary_op(
            "INT_ADD",
            Expression.variable("box", size=8),
            Expression.constant(4, 8),
        ),
    )

    location = canonicalize_param_location(
        addr_expr,
        [_param("box", size=8, is_signed=False)],
        size=4,
    )

    assert location == CanonicalLocation("box", 4, 4)


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

    assert location == CanonicalLocation("ptr", 0, 4)


def test_effect_summary_keeps_load_when_multiple_writes_overlap():
    ptr = Expression.parameter("ptr", 0, size=8)
    original = Expression.memory(ptr, size=4)
    effects = [
        StoreEffect(
            location=CanonicalLocation("ptr", 0, 4),
            value=Expression.constant(1, 4),
            conditions=[],
            order_key=2,
        ),
        StoreEffect(
            location=CanonicalLocation("ptr", 0, 4),
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
            location=CanonicalLocation("ptr", 0, 4),
            value=Expression.parameter("v_true", 2, size=4),
            conditions=[positive],
            order_key=2,
        ),
        StoreEffect(
            location=CanonicalLocation("ptr", 0, 4),
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
        location=CanonicalLocation("box", 4, 4),
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
        location=CanonicalLocation("box", 4, 4),
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


def test_call_effect_summary_policy_accepts_interdependent_swap_writes():
    summary = EffectSummary(
        parameter_names=["a", "b"],
        effects=[
            StoreEffect(
                location=CanonicalLocation("a", 0, 4),
                value=Expression.memory(Expression.parameter("b", 1, size=8), size=4),
                conditions=[],
                order_key=1,
            ),
            StoreEffect(
                location=CanonicalLocation("b", 0, 4),
                value=Expression.memory(Expression.parameter("a", 0, size=8), size=4),
                conditions=[],
                order_key=2,
            ),
        ],
    )

    assert is_call_effect_summary_allowed(summary)


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
            location=CanonicalLocation("a", 0, 4),
            value=Expression.memory(b, size=4),
            conditions=[swap_taken],
            order_key=1,
        ),
        StoreEffect(
            location=CanonicalLocation("b", 0, 4),
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
            location=CanonicalLocation("a", 0, 4),
            value=Expression.memory(b, size=4),
            conditions=[swap_taken],
            order_key=10,
        ),
        StoreEffect(
            location=CanonicalLocation("b", 0, 4),
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
            location=CanonicalLocation("a", 0, 4),
            value=Expression.memory(b, size=4),
            conditions=[swap_taken],
            order_key=1,
        ),
        StoreEffect(
            location=CanonicalLocation("b", 0, 4),
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
                location=CanonicalLocation("a", 0, 4),
                value=Expression.memory(b, size=4),
                conditions=[swap_taken],
                order_key=1,
            ),
            StoreEffect(
                location=CanonicalLocation("b", 0, 4),
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
            location=CanonicalLocation("a", 0, 4),
            value=Expression.memory(b, size=4),
            conditions=[swap_taken],
            order_key=1,
        ),
        StoreEffect(
            location=CanonicalLocation("b", 0, 4),
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
            location=CanonicalLocation("a", 0, 4),
            value=Expression.memory(b, size=4),
            conditions=[swap_taken],
            order_key=1,
        ),
        StoreEffect(
            location=CanonicalLocation("b", 0, 4),
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
                location=CanonicalLocation("a", 0, 4),
                value=Expression.memory(b, size=4),
                conditions=[swap_taken],
                order_key=1,
            ),
            StoreEffect(
                location=CanonicalLocation("b", 0, 4),
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
                location=CanonicalLocation("a", 0, 4),
                value=Expression.memory(b, size=4),
                conditions=[swap_taken],
                order_key=1,
            ),
            StoreEffect(
                location=CanonicalLocation("b", 0, 4),
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
                location=CanonicalLocation("a", 0, 4),
                value=Expression.memory(b, size=4),
                conditions=[swap_taken],
                order_key=1,
            ),
            StoreEffect(
                location=CanonicalLocation("b", 0, 4),
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
            location=CanonicalLocation("a", 0, 4),
            value=Expression.memory(b, size=4),
            conditions=[swap_taken],
            order_key=1,
        ),
        StoreEffect(
            location=CanonicalLocation("b", 0, 4),
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
                location=CanonicalLocation("a", 0, 4),
                value=Expression.memory(b, size=4),
                conditions=[swap_taken],
                order_key=1,
            ),
            StoreEffect(
                location=CanonicalLocation("b", 0, 4),
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
                location=CanonicalLocation("a", 0, 4),
                value=Expression.memory(b, size=4),
                conditions=[swap_taken],
                order_key=1,
            ),
            StoreEffect(
                location=CanonicalLocation("b", 0, 4),
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
                location=CanonicalLocation("a", 0, 4),
                value=Expression.memory(b, size=4),
                conditions=[swap_taken],
                order_key=1,
            ),
            StoreEffect(
                location=CanonicalLocation("b", 0, 4),
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
    expander._get_edge_condition = lambda block_info, _parent: no_swap if block_info.index == 3 else swap_taken

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
        ("MEM[a]", (swap_taken.to_string(),)),
    }


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
                location=CanonicalLocation("a", 0, 4),
                value=Expression.memory(b, size=4),
                conditions=[swap_taken],
                order_key=1,
            ),
            StoreEffect(
                location=CanonicalLocation("b", 0, 4),
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
                location=CanonicalLocation("param_1", 0, 4),
                value=Expression.memory(b, size=4),
                conditions=[swap_taken],
                order_key=1,
            ),
            StoreEffect(
                location=CanonicalLocation("param_2", 0, 4),
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
                location=CanonicalLocation("a", 0, 4),
                value=Expression.memory(b, size=4),
                conditions=[swap_taken],
                order_key=1,
            ),
            StoreEffect(
                location=CanonicalLocation("b", 0, 4),
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
                location=CanonicalLocation("a", 0, 4),
                value=Expression.memory(b, size=4),
                conditions=[swap_taken],
                order_key=10,
            ),
            StoreEffect(
                location=CanonicalLocation("b", 0, 4),
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

    assert canonicalized.to_string() == "(PHI(MEM[b] if (MEM[b] < MEM[a]), MEM[a]) - PHI(MEM[a] if (MEM[b] < MEM[a]), MEM[b]))"


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
                location=CanonicalLocation("a", 0, 4),
                value=Expression.memory(b, size=4),
                conditions=[swap_taken],
                order_key=1,
            ),
            StoreEffect(
                location=CanonicalLocation("b", 0, 4),
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

    assert inferred == CanonicalLocation("b", 0, 4)


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
                location=CanonicalLocation("a", 0, 4),
                value=Expression.memory(b, size=4),
                conditions=[swap_taken],
                order_key=1,
            ),
            StoreEffect(
                location=CanonicalLocation("b", 0, 4),
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

    assert inferred == CanonicalLocation("a", 0, 4)


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
                location=CanonicalLocation("a", 0, 4),
                value=Expression.memory(b, size=4),
                conditions=[swap_taken],
                order_key=1,
            ),
            StoreEffect(
                location=CanonicalLocation("b", 0, 4),
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
                location=CanonicalLocation("a", 0, 4),
                value=Expression.memory(b, size=4),
                conditions=[swap_taken],
                order_key=10,
            ),
            StoreEffect(
                location=CanonicalLocation("b", 0, 4),
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

    assert canonicalized.to_string() == "(PHI(MEM[b] if (MEM[b] < MEM[a]), MEM[a]) - PHI(MEM[a] if (MEM[b] < MEM[a]), MEM[b]))"


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
                location=CanonicalLocation("a", 0, 4),
                value=Expression.memory(b, size=4),
                conditions=[swap_taken],
                order_key=10,
            ),
            StoreEffect(
                location=CanonicalLocation("b", 0, 4),
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
                location=CanonicalLocation("a", 0, 4),
                value=Expression.memory(b, size=4),
                conditions=[swap_taken],
                order_key=10,
            ),
            StoreEffect(
                location=CanonicalLocation("b", 0, 4),
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
    values = sorted(ev.value.to_string() for ev in expanded)
    assert values == ["(MEM[a] - MEM[b])", "(MEM[b] - MEM[a])"]
    assert any("(MEM[b] < MEM[a])" in " ".join(cond.to_string() for cond in ev.conditions) for ev in expanded)


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
            location=CanonicalLocation("a", 0, 4),
            value=Expression.memory(b, size=4),
            conditions=[swap_taken],
            order_key=1,
        ),
        StoreEffect(
            location=CanonicalLocation("b", 0, 4),
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
        location=CanonicalLocation("dst", 0, 4),
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
        location=CanonicalLocation("dst", 0, 4),
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
        location=CanonicalLocation("dst", 0, 4),
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


def test_call_effect_summary_policy_accepts_simple_param_store_summary():
    summary = EffectSummary(
        parameter_names=["ptr", "value"],
        effects=[
            StoreEffect(
                location=CanonicalLocation("ptr", 0, 4),
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
                location=CanonicalLocation("ptr", 0, 4),
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
                location=CanonicalLocation("ptr", 0, 4),
                value=Expression.constant(1, 4),
                conditions=[],
                order_key=1,
            )
        ],
        has_unsupported_call=True,
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


def test_type_fixer_does_not_pattern_fix_pointer_types():
    fixer = object.__new__(TypeFixer)
    fixer.config = TypeFixerConfig()
    fixer.debug = False

    assert fixer._should_fix_type("undefined4")
    assert not fixer._should_fix_type("undefined4 *")


def test_return_analyzer_find_function_by_name_resolves_fun_address_via_containing():
    class _FakeFunction:
        def __init__(self, name):
            self._name = name

        def getName(self):
            return self._name

    class _FakeFunctionManager:
        def __init__(self, containing):
            self._containing = containing

        def getFunctions(self, _forward):
            return []

        def getFunctionAt(self, _addr):
            return None

        def getFunctionContaining(self, _addr):
            return self._containing

    class _FakeAddressSpace:
        def getAddress(self, value):
            return value

    class _FakeAddressFactory:
        def getDefaultAddressSpace(self):
            return _FakeAddressSpace()

    class _FakeProgram:
        def __init__(self, containing):
            self._manager = _FakeFunctionManager(containing)
            self._factory = _FakeAddressFactory()

        def getFunctionManager(self):
            return self._manager

        def getAddressFactory(self):
            return self._factory

    analyzer = ReturnAnalyzer(_FakeProgram(_FakeFunction("mem_void_write_if_needed")), debug=False)

    resolved = analyzer._find_function_by_name("FUN_120001514")

    assert resolved is not None
    assert resolved.getName() == "mem_void_write_if_needed"


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

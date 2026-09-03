# -*- coding: utf-8 -*-

from scripts.function_tracer_pcode.analysis.effects.summary import (
    EffectSummary,
    StoreEffect,
    canonicalize_location,
    substitute_condition,
    substitute_location,
)
from scripts.function_tracer_pcode.analysis.returns.analyzer import ReturnAnalyzer
from scripts.function_tracer_pcode.analysis.tracer import PcodeTracer
from scripts.function_tracer_pcode.core import (
    CallTargetRef,
    CanonicalLocation,
    Condition,
    DeferredCallInfo,
    DeferredCallRef,
    Expression,
    FunctionReturnAnalysis,
    LocationBaseRef,
    ReturnInfo,
    StorageInfo,
)
from scripts.function_tracer_pcode.core.render_smt import collect_unknown_smt_declarations
from scripts.function_tracer_pcode.core.runtime_refs import PostStateReadRef
from scripts.function_tracer_pcode.proof.recursive_abstraction import abstract_recursive_calls
from scripts.function_tracer_pcode.semantics.transform.expander import ExpandedValue


def _param(name, index=0, size=4, storage=None):
    return {
        "name": name,
        "index": index,
        "size": size,
        "data_type": "int",
        "storage": storage,
    }


def _stack_storage(offset: int, size_bytes: int = 4):
    return {
        "is_register": False,
        "space_name": "stack",
        "offset": offset,
        "size": size_bytes,
        "size_bits": size_bytes * 8,
    }


def test_substitute_location_accepts_ptrsub_stack_actual_argument():
    caller_params = [_param("param_1", 0, 4), _param("param_2", 1, 4)]
    callee_location = CanonicalLocation(
        base_ref=LocationBaseRef.parameter("param_3", index=2),
        offset=0,
        size=4,
    )
    stack_base = Expression.variable(
        "sp",
        size=8,
        storage_info=StorageInfo(
            is_register=True,
            space_name="register",
            offset=0,
            size=8,
            size_bits=64,
            register_name="sp",
            base_register_name="sp",
            is_stack_pointer=True,
        ),
    )
    actual_addr = Expression.intrinsic(
        "PTRSUB",
        [stack_base, Expression.constant(-16, 8)],
        size=8,
    )

    caller_location = canonicalize_location(actual_addr, caller_params, size=4)
    assert caller_location == CanonicalLocation(
        base_ref=LocationBaseRef.stack_frame(),
        offset=-16,
        size=4,
    )

    substituted = substitute_location(
        callee_location,
        [LocationBaseRef.parameter("param_1", index=0), LocationBaseRef.parameter("param_2", index=1), LocationBaseRef.parameter("param_3", index=2)],
        [
            Expression.parameter("param_1", 0, size=4),
            Expression.parameter("param_2", 1, size=4),
            actual_addr,
        ],
        caller_params,
    )

    assert substituted == caller_location


def test_tracer_promotes_zero_based_indirect_to_symbolic_post_state_read():
    class _FakeAddress:
        def __init__(self, offset, space_name):
            self._offset = offset
            self._space_name = space_name

        def getOffset(self):
            return self._offset

        def getAddressSpace(self):
            return self

        def getName(self):
            return self._space_name

    class _FakeVarnode:
        def __init__(self, offset, size, space_name):
            self._offset = offset
            self._size = size
            self._space_name = space_name

        def getAddress(self):
            return _FakeAddress(self._offset, self._space_name)

        def getOffset(self):
            return self._offset

        def getSize(self):
            return self._size

        def getDef(self):
            return None

        def getHigh(self):
            return None

        def isConstant(self):
            return False

    class _FakeConstVarnode(_FakeVarnode):
        def __init__(self, value, size):
            super().__init__(value, size, "const")
            self._value = value

        def isConstant(self):
            return True

        def getOffset(self):
            return self._value

    class _FakeIndirectOp:
        def __init__(self, output):
            self._output = output
            self._inputs = [_FakeConstVarnode(0, 4), _FakeConstVarnode(53, 4)]

        def getMnemonic(self):
            return "INDIRECT"

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

        def getOutput(self):
            return self._output

        def getOpcode(self):
            return 61

    tracer = PcodeTracer(program=None, high_function=None, debug=False)
    output = _FakeVarnode(-0x28, 4, "stack")
    expr = tracer._trace_pcode_op_internal(_FakeIndirectOp(output), depth=0, use_cache=False)

    assert getattr(expr.runtime_ref, "location", None) == CanonicalLocation(
        base_ref=LocationBaseRef.stack_frame(),
        offset=-0x28,
        size=4,
    )
    assert isinstance(expr.runtime_ref, PostStateReadRef)


def test_tracer_promotes_same_slot_indirect_to_symbolic_post_state_read():
    class _FakeAddress:
        def __init__(self, offset, space_name):
            self._offset = offset
            self._space_name = space_name

        def getOffset(self):
            return self._offset

        def getAddressSpace(self):
            return self

        def getName(self):
            return self._space_name

    class _FakeVarnode:
        def __init__(self, offset, size, space_name):
            self._offset = offset
            self._size = size
            self._space_name = space_name

        def getAddress(self):
            return _FakeAddress(self._offset, self._space_name)

        def getOffset(self):
            return self._offset

        def getSize(self):
            return self._size

        def getDef(self):
            return None

        def getHigh(self):
            return None

        def isConstant(self):
            return False

    class _FakeConstVarnode(_FakeVarnode):
        def __init__(self, value, size):
            super().__init__(value, size, "const")
            self._value = value

        def isConstant(self):
            return True

        def getOffset(self):
            return self._value

    class _FakeIndirectOp:
        def __init__(self, output, base):
            self._output = output
            self._inputs = [base, _FakeConstVarnode(74, 4)]

        def getMnemonic(self):
            return "INDIRECT"

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

        def getOutput(self):
            return self._output

        def getOpcode(self):
            return 61

    tracer = PcodeTracer(program=None, high_function=None, debug=False)
    slot = _FakeVarnode(-0x2C, 4, "stack")
    expr = tracer._trace_pcode_op_internal(_FakeIndirectOp(slot, slot), depth=0, use_cache=False)

    assert getattr(expr.runtime_ref, "location", None) == CanonicalLocation(
        base_ref=LocationBaseRef.stack_frame(),
        offset=-0x2C,
        size=4,
    )
    assert isinstance(expr.runtime_ref, PostStateReadRef)


def test_tracer_does_not_promote_same_slot_indirect_for_readonly_global_slot():
    class _FakeAddress:
        def __init__(self, offset, space_name):
            self._offset = offset
            self._space_name = space_name

        def getOffset(self):
            return self._offset

        def getAddressSpace(self):
            return self

        def getName(self):
            return self._space_name

    class _FakeVarnode:
        def __init__(self, offset, size, space_name):
            self._offset = offset
            self._size = size
            self._space_name = space_name

        def getAddress(self):
            return _FakeAddress(self._offset, self._space_name)

        def getOffset(self):
            return self._offset

        def getSize(self):
            return self._size

        def getDef(self):
            return None

        def getHigh(self):
            return None

        def isConstant(self):
            return False

    class _FakeConstVarnode(_FakeVarnode):
        def __init__(self, value, size):
            super().__init__(value, size, "const")
            self._value = value

        def isConstant(self):
            return True

        def getOffset(self):
            return self._value

    class _FakeIndirectOp:
        def __init__(self, output, base):
            self._output = output
            self._inputs = [base, _FakeConstVarnode(74, 4)]

        def getMnemonic(self):
            return "INDIRECT"

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

        def getOutput(self):
            return self._output

        def getOpcode(self):
            return 61

    class _FakeBlock:
        def isWrite(self):
            return False

        def isVolatile(self):
            return False

    class _FakeMemory:
        def getBlock(self, _addr):
            return _FakeBlock()

    class _FakeProgram:
        def getMemory(self):
            return _FakeMemory()

    tracer = PcodeTracer(program=_FakeProgram(), high_function=None, debug=False)
    slot = _FakeVarnode(0x120013158, 8, "ram")
    fallback = Expression.variable("PTR___stack_chk_fail_slot", size=8)
    tracer.trace_varnode = lambda varnode, depth=0, use_cache=True: fallback if varnode is slot else Expression.constant(74, 4)
    expr = tracer._trace_pcode_op_internal(_FakeIndirectOp(slot, slot), depth=0, use_cache=False)

    assert not isinstance(getattr(expr, "runtime_ref", None), PostStateReadRef)
    assert "poststate" not in expr.to_string()


def test_return_infos_drop_cases_that_match_blocked_noreturn_path_conditions():
    analyzer = ReturnAnalyzer(program=None, debug=False)
    blocked_condition = Condition(
        Expression.binary_op(
            "INT_NOTEQUAL",
            Expression.parameter("guard_lhs", 0, size=8),
            Expression.parameter("guard_rhs", 1, size=8),
        ),
        False,
    )
    analyzer._current_blocked_return_path_conditions = [[blocked_condition]]

    safe_case = ExpandedValue(
        Expression.constant(7, 4),
        [],
    )
    blocked_case = ExpandedValue(
        Expression.constant(9, 4),
        [blocked_condition],
    )

    results = analyzer._build_return_infos_from_expansions(
        "test",
        [safe_case, blocked_case],
        0,
    )

    assert len(results) == 1
    assert results[0].value.value == 7


def test_recursive_abstraction_matches_runtime_location_backed_arguments():
    shared_location = CanonicalLocation(
        base_ref=LocationBaseRef.stack_frame(),
        offset=-0x10,
        size=4,
    )
    runtime_arg_left = Expression.variable("left_slot", size=4, runtime_ref=shared_location)
    runtime_arg_right = Expression.variable("right_slot", size=4, runtime_ref=shared_location)

    deferred_left = DeferredCallInfo(
        deferred_call_ref=DeferredCallRef(sequence=1),
        target_ref=CallTargetRef.from_name("callee"),
        arguments=[runtime_arg_left],
        call_target_expr=None,
    )
    deferred_right = DeferredCallInfo(
        deferred_call_ref=DeferredCallRef(sequence=2),
        target_ref=CallTargetRef.from_name("callee"),
        arguments=[runtime_arg_right],
        call_target_expr=None,
    )

    analysis_left = FunctionReturnAnalysis(
        function_name="lhs",
        entry_point="0x1000",
        parameters=[],
        returns=[ReturnInfo(address="0x1000", value=Expression.constant(0, 4), conditions=[], branch_index=0)],
        deferred_calls={deferred_left.deferred_call_ref.stable_key(): deferred_left},
    )
    analysis_right = FunctionReturnAnalysis(
        function_name="rhs",
        entry_point="0x2000",
        parameters=[],
        returns=[ReturnInfo(address="0x2000", value=Expression.constant(0, 4), conditions=[], branch_index=0)],
        deferred_calls={deferred_right.deferred_call_ref.stable_key(): deferred_right},
    )

    result = abstract_recursive_calls(analysis_left, analysis_right)

    assert result.applied is False


def test_effect_summary_with_unsupported_call_binding_is_decisive_sat_unsafe():
    analysis = FunctionReturnAnalysis(
        function_name="ptr_read_after_store",
        entry_point="0x1000",
        parameters=[_param("a", 0, 4)],
        returns=[ReturnInfo(address="0x1000", value=Expression.constant(0, 4), conditions=[], branch_index=0)],
        effect_summary=EffectSummary(
            parameter_names=["a"],
            effects=[
                StoreEffect(
                    location=CanonicalLocation(base_ref=LocationBaseRef.parameter("a", index=0), offset=0, size=4),
                    value=Expression.constant(1, 4),
                    conditions=[],
                    order_key=1,
                )
            ],
            has_unsupported_call=True,
        ),
    )

    assert "unsupported_call_effect_summary" in analysis.get_decisive_sat_unsafety_reasons()


def test_substitute_condition_accepts_scoped_parameter_identity_with_unscoped_replacement():
    scoped_param = Expression.parameter(
        "param_3",
        2,
        size=8,
        runtime_ref=LocationBaseRef.parameter(
            "param_3",
            index=2,
            owner_program_id=1,
            owner_entry_offset=0x1000,
        ),
    )
    condition = Condition(
        Expression.binary_op(
            "INT_NOTEQUAL",
            scoped_param,
            Expression.constant(0, 8),
        ),
        False,
    )
    stack_base = Expression.variable(
        "sp",
        size=8,
        storage_info=StorageInfo(
            is_register=True,
            space_name="register",
            offset=0,
            size=8,
            size_bits=64,
            register_name="sp",
            base_register_name="sp",
            is_stack_pointer=True,
        ),
    )
    actual_arg = Expression.intrinsic(
        "PTRSUB",
        [stack_base, Expression.constant(-32, 8)],
        size=8,
    )

    substituted = substitute_condition(
        condition,
        {("parameter", 2): actual_arg},
        [_param("param_1", 0, 4), _param("param_2", 1, 4)],
    )

    assert "param_3" not in substituted.to_string()


def test_collect_unknown_smt_declarations_includes_symbolic_post_state_variables():
    expr = Expression.variable(
        "poststate_stackframe_tail_n32_size_4",
        size=4,
        runtime_ref=PostStateReadRef(
            location=CanonicalLocation(
                base_ref=LocationBaseRef.stack_frame(),
                offset=-32,
                size=4,
            )
        ),
    )

    assert collect_unknown_smt_declarations(expr) == [
        ("poststate_stackframe_tail_n32_size_4", 32)
    ]

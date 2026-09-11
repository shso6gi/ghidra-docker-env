from typing import Optional

from conftest import resolve_mock_data_type

from scripts.function_tracer_pcode.analysis.memory_resolver import (
    collect_memory_bit_widths_from_analysis,
    concretize_readonly_loads,
)

import scripts.function_tracer_pcode.analysis.effects.summary as effect_summary_module

from scripts.function_tracer_pcode.analysis.effects.summary import (
    CallArgumentEvidence,
    CallArgumentWidthEvidence,
    CanonicalLocation,
    LocationStep,
    StoreEffect,
    _additive_signature,
    _build_parameter_replacements,
    _call_argument_evidence_storage_key,
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

from scripts.function_tracer_pcode.core import (
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

from scripts.function_tracer_pcode.analysis.returns.analyzer import ReturnAnalyzer

from scripts.function_tracer_pcode.analysis.phi_resolver import (
    ExpandedBranch as PhiExpandedBranch,
    PhiHandler,
)

from scripts.function_tracer_pcode.analysis.tracer import PcodeTracer

from scripts.function_tracer_pcode.semantics.typing.fixer import TypeFixer, TypeFixerConfig

from scripts.function_tracer_pcode.checker.arch.mips64 import MIPS64Handler

from scripts.function_tracer_pcode.proof.formula.builder import FormulaBuilder

from scripts.function_tracer_pcode.semantics.param_semantics import ParameterSemanticHint

from scripts.function_tracer_pcode.semantics.normalize.core import normalize_expression

from scripts.function_tracer_pcode.core import (
    Condition,
    Expression,
    ExpressionType,
    FunctionReturnAnalysis,
    ReturnInfo,
)

from scripts.function_tracer_pcode.core.storage import StorageInfo

from scripts.function_tracer_pcode.semantics.transform.expander import (
    ExpressionExpander,
    ExpandedValue,
)

def forbid_callee_summary(_target_ref, _arguments):
    """Issue #121: CALL / CALLIND を含まない fixture であることを固定する stub。

    ``summarize_store_effects`` は callable な ``direct_call_summary`` を必須に
    するが、block に call が無ければこの stub は呼ばれない。将来 fixture に
    call が混入したら、黙って summary が変わる代わりに test が失敗する。
    """
    raise AssertionError(
        "fixture contains no CALL/CALLIND; direct_call_summary must not be invoked"
    )

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

def _const_storage(size_bytes: int = 8):
    return {
        "is_register": False,
        "space_name": "const",
        "offset": 0,
        "size": size_bytes,
        "size_bits": size_bytes * 8,
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

def _readonly_format_string_expr(offset: int = 0x1004D0, *, can_execute: bool = False) -> Expression:
    return Expression.constant(
        offset,
        8,
        runtime_ref=AddressValueRef(
            address_offset=offset,
            source="test_rodata",
            display_hint="format",
            is_initialized=True,
            can_read=True,
            can_write=False,
            can_execute=can_execute,
            is_volatile=False,
        ),
    )

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

# Export private helpers as well; split tests retain the original module globals.
__all__ = [name for name in globals() if not name.startswith('__')]

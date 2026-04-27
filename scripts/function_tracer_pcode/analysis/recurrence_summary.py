# -*- coding: utf-8 -*-
"""Structural recurrence summaries for simple recursion/loop patterns."""

from __future__ import annotations

from collections import Counter
from dataclasses import dataclass
from typing import Any, Dict, Iterable, List, Optional, Sequence, Tuple

from ..model import (
    COUNTED_LOOP_SUM_OPCODE,
    READONLY_SUM_OPCODE,
    Condition,
    CountedLoopSummaryRef,
    Expression,
    ExpressionType,
    LoopBodyEffectRef,
    LoopCaseRef,
    LoopSideEffectProfileRef,
    LoopSummaryRef,
    LoopTermDescriptorRef,
    LocationBaseRef,
    PcodeBlockRef,
    PcodeOpRef,
    ReductionAccumulatorProof,
    ReadonlyReductionRef,
    ReadonlyReductionTermRef,
    ReadonlyReductionWitness,
    ReturnInfo,
)
from ..model.render_smt import collect_intrinsic_smt_declarations
from ..model.signature import is_integral_data_type, is_pointer_data_type
from ..model.runtime_refs import UnknownValueRef
from ..smt.interface import SolverStatus
from ..smt.solvers.z3 import Z3Solver
from ..equivalence.formula.returns import coerce_value_to_bitvec_width
from ..equivalence.formula.symbol_replace import build_symbol_replacer
from ..equivalence.formula.types import ParameterInfo
from .condition import ConditionSimplifier, ConditionNormalizer
from .condition.bitvector import eval_constant_raw
from .effect_summary import (
    CanonicalLocation,
    _expressions_equivalent_under_conditions,
    _reduce_expression_under_conditions,
    canonicalize_location,
)


def _runtime_expression_signature(expr: Optional[Expression]):
    if expr is None:
        return ("none",)
    return ConditionNormalizer.expression_signature(expr)


def _runtime_conditions_signature(conditions: Sequence[Condition]):
    return ConditionNormalizer.conditions_signature(conditions)


@dataclass(frozen=True)
class CountedLoopInduction:
    phi_op: object
    phi_output: object
    init_expr: Expression
    backedge_index: int
    step: int
    placeholder: Expression
    signed_guard: bool
    init_index: Optional[int] = None
    backedge_indices: Tuple[int, ...] = ()


@dataclass(frozen=True)
class CountedLoopAccumulator:
    phi_op: Optional[object]
    phi_output: Optional[object]
    init_expr: Expression
    backedge_index: int
    placeholder: Expression
    member_outputs: Tuple[object, ...] = ()
    member_placeholders: Tuple[Expression, ...] = ()
    update_varnode: Optional[object] = None
    update_block: Optional[object] = None
    init_index: Optional[int] = None
    backedge_indices: Tuple[int, ...] = ()


@dataclass(frozen=True)
class CountedLoopGuard:
    condition_expr: Expression
    bound_expr: Expression
    continue_on_true: bool
    body_block: object
    exit_block: object
    signed_comparison: bool
    entry_condition_expr: Optional[Expression] = None
    latch_block: Optional[object] = None


@dataclass(frozen=True)
class CountedLoopUpdateCase:
    conditions: Tuple[Condition, ...]
    update_expr: Expression
    delta_expr: Expression


@dataclass(frozen=True)
class ResidueLoopCase:
    modulus: int
    residue: int
    affine: Tuple[int, int]


class StructuralRecurrenceSummarizer:
    """
    Recover conservative closed-form summaries for simple scalar recurrences.

    The current implementation intentionally focuses on a sound, reusable subset:
    single-parameter, unit-step, additive self-recursive functions of the form

      f(n) = base                  when n <= L
      f(n) = f(n - 1) + (a*n + b)  when n > L

    If the pattern cannot be proved from the already recovered return cases and the
    function's direct self-call site, the summarizer declines and the caller falls
    back to the existing path-sensitive analysis.
    """

    _SIGNED_GT_OPS = {"INT_SLESS", "INT_SLESSEQUAL"}

    def __init__(self, tracer, debug: bool = False):
        self.tracer = tracer
        self.debug = debug

    def has_summary_candidate(self, function, high_function, analysis) -> bool:
        if function is None or high_function is None or analysis is None:
            return False
        if not getattr(analysis, "returns", None):
            return False

        function_name = getattr(function, "getName", lambda: "")()
        if len(getattr(analysis, "parameters", []) or []) == 1 and any(
            self._expression_contains_recursive_unknown(ret.value, function_name)
            for ret in (analysis.returns or [])
        ):
            return True

        if self._has_readonly_pointer_reduction_candidate(high_function, analysis):
            return True

        if self._has_counted_scalar_loop_candidate(high_function):
            return True

        if self._has_branch_accumulator_candidate(analysis):
            return True

        return False

    def try_summarize_function(self, function, high_function, analysis) -> Optional[Tuple[List[ReturnInfo], str]]:
        if function is None or high_function is None or analysis is None:
            return None

        if len(getattr(analysis, "parameters", []) or []) == 1:
            summary = self._try_summarize_linear_self_recursion(function, high_function, analysis)
            if summary is not None:
                return summary

        summary = self._try_summarize_readonly_pointer_reduction(function, high_function, analysis)
        if summary is not None:
            return summary

        summary = self._try_summarize_counted_scalar_loop(function, high_function, analysis)
        if summary is not None:
            return summary

        summary = self._try_summarize_branch_accumulator_loop(analysis)
        if summary is not None:
            return summary
        return None

    def try_summarize_pre_return_counted_scalar_loop(
        self,
        function,
        high_function,
        analysis,
        return_ops: Sequence,
    ) -> Optional[Tuple[List[ReturnInfo], str]]:
        if function is None or high_function is None or analysis is None:
            return None
        return_ops = list(return_ops or [])
        if not self._pre_return_counted_scalar_summary_is_cfg_safe(high_function, return_ops):
            return None
        if not self._analysis_is_safe_for_counted_scalar_summary(analysis):
            return None
        return self._build_counted_scalar_loop_summary(
            function,
            high_function,
            analysis,
            pre_return_ops=return_ops,
        )

    def _pre_return_counted_scalar_summary_is_cfg_safe(
        self,
        high_function,
        return_ops: Sequence,
    ) -> bool:
        if high_function is None:
            return False
        return_ops = list(return_ops or [])
        if not return_ops:
            self._debug("Declined pre-return counted loop summary: no RETURN ops")
            return False
        if any(self._safe_pcode_input_count(return_op) < 2 for return_op in return_ops):
            self._debug("Declined pre-return counted loop summary: RETURN without value")
            return False
        if not self._has_counted_scalar_loop_candidate(high_function):
            self._debug("Declined pre-return counted loop summary: no counted-loop CFG candidate")
            return False

        forbidden = {"CALL", "CALLIND", "BRANCHIND", "STORE"}
        return_blocks = {getattr(op, "getParent", lambda: None)() for op in return_ops}
        return_blocks.discard(None)
        if not return_blocks:
            return False
        terminal_blocks = []
        for block in self._iter_basic_blocks(high_function):
            if int(getattr(block, "getOutSize", lambda: 0)() or 0) == 0:
                terminal_blocks.append(block)
            for op in self._iter_block_ops(block):
                mnemonic = getattr(op, "getMnemonic", lambda: None)()
                if mnemonic in forbidden:
                    self._debug(f"Declined pre-return counted loop summary: forbidden op {mnemonic}")
                    return False
        if not terminal_blocks:
            self._debug("Declined pre-return counted loop summary: no terminal CFG blocks")
            return False
        if set(terminal_blocks) != return_blocks:
            self._debug(
                "Declined pre-return counted loop summary: terminal blocks are not exactly RETURN blocks "
                f"(terminal={len(terminal_blocks)}, returns={len(return_blocks)})"
            )
            return False
        return True

    def _has_readonly_pointer_reduction_candidate(
        self,
        high_function,
        analysis,
    ) -> bool:
        if analysis is None or not analysis.returns:
            return False
        if getattr(getattr(analysis, "effect_summary", None), "effects", None):
            return False
        if len(getattr(analysis, "parameters", []) or []) < 2:
            return False

        pointer_param, count_param = self._infer_readonly_pointer_reduction_parameters(
            analysis,
            high_function,
        )
        if pointer_param is None or count_param is None:
            return False

        positive_conditions = self._readonly_reduction_positive_conditions(
            analysis,
            pointer_param,
            count_param,
        )
        if ConditionSimplifier.object_centric_is_contradiction(positive_conditions):
            return False
        if not any(
            self._return_overlaps_conditions(ret, positive_conditions)
            for ret in (analysis.returns or [])
        ):
            return False

        accumulator_proof = self._detect_readonly_sum_accumulator_proof(
            high_function,
            analysis,
            pointer_param,
            count_param,
            positive_conditions=positive_conditions,
        )
        return accumulator_proof is not None

    def _has_counted_scalar_loop_candidate(self, high_function) -> bool:
        if high_function is None:
            return False
        for block in self._iter_basic_blocks(high_function):
            phis = [
                op for op in self._iter_block_ops(block)
                if getattr(op, "getMnemonic", lambda: None)() == "MULTIEQUAL"
            ]
            if len(phis) >= 2 and self._find_cbranch_op(block) is not None:
                return True
        return False

    def _try_summarize_counted_scalar_loop(
        self,
        function,
        high_function,
        analysis,
    ) -> Optional[Tuple[List[ReturnInfo], str]]:
        if function is None or high_function is None or analysis is None:
            return None
        if not self._analysis_is_safe_for_counted_scalar_summary(analysis):
            return None
        return self._build_counted_scalar_loop_summary(function, high_function, analysis)

    def _analysis_is_safe_for_counted_scalar_summary(self, analysis) -> bool:
        if analysis is None:
            return False
        effect_profile = self._build_loop_side_effect_profile(
            analysis=analysis,
        )
        if (
            effect_profile.calls
            or effect_profile.escapes
            or effect_profile.context_calls
            or effect_profile.context_escapes
        ):
            self._debug("Declined counted scalar loop summary: loop contains calls or escaping control flow")
            return False
        if getattr(analysis, "incomplete_control_flow", False):
            self._debug("Declined counted scalar loop summary: control flow is incomplete")
            return False
        return True

    def _loop_effect_profile_name(
        self,
        *,
        memory_reads: bool,
        memory_writes: bool,
        calls: bool,
        escapes: bool,
        conditional_guards: bool,
    ) -> str:
        if calls or escapes:
            return "effect_unknown"
        if memory_writes:
            return "effect_aware"
        if conditional_guards:
            return "pure_conditional"
        if memory_reads:
            return "pure_memory_read"
        return "pure"

    def _build_loop_side_effect_profile(
        self,
        *,
        analysis=None,
        high_function=None,
        loop_blocks: Optional[Sequence[object]] = None,
        ignored_branch_ops: Optional[Sequence[object]] = None,
        block_guard_conditions: Optional[Dict[object, Sequence[Condition]]] = None,
        block_guard_info: Optional[Dict[object, Dict[str, Any]]] = None,
        memory_reads: bool = False,
    ) -> LoopSideEffectProfileRef:
        descriptors: List[LoopBodyEffectRef] = []
        context_descriptors: List[LoopBodyEffectRef] = []
        has_memory_reads = bool(memory_reads)
        has_memory_writes = False
        has_calls = False
        has_escapes = False
        has_conditional_guards = False
        has_context_memory_writes = False
        has_context_calls = False
        has_context_escapes = False
        has_context_conditional_guards = False

        effect_summary = getattr(analysis, "effect_summary", None) if analysis is not None else None
        for effect in getattr(effect_summary, "effects", None) or []:
            has_context_memory_writes = True
            effect_conditions = tuple(getattr(effect, "conditions", None) or ())
            if effect_conditions:
                has_context_conditional_guards = True
            context_descriptors.append(
                LoopBodyEffectRef(
                    kind="memory_write",
                    source="function_effect_summary",
                    scope="function",
                    location=getattr(effect, "location", None),
                    value_expr=getattr(effect, "value", None),
                    guard_constraints=effect_conditions,
                    order_key=getattr(effect, "order_key", None),
                )
            )
        if getattr(effect_summary, "has_unsupported_call", False):
            has_context_calls = True
            has_context_escapes = True
            context_descriptors.append(
                LoopBodyEffectRef(
                    kind="unsupported_call",
                    source="function_effect_summary",
                    scope="function",
                )
            )
        if getattr(analysis, "incomplete_control_flow", False):
            has_context_escapes = True
            context_descriptors.append(
                LoopBodyEffectRef(
                    kind="incomplete_control_flow",
                    source="function_analysis",
                    scope="function",
                )
            )

        ignored_ids = {id(op) for op in (ignored_branch_ops or ()) if op is not None}
        pcode_scope = "loop" if loop_blocks is not None else "function"
        if loop_blocks is None and high_function is not None:
            loop_blocks = list(self._iter_basic_blocks(high_function))
        for block in loop_blocks or ():
            for op in self._iter_block_ops(block):
                mnemonic = getattr(op, "getMnemonic", lambda: None)()
                if mnemonic == "LOAD":
                    if pcode_scope == "loop":
                        has_memory_reads = True
                    continue
                if mnemonic == "STORE":
                    block_key = self._block_key(block)
                    guard_info = (block_guard_info or {}).get(block_key, {})
                    guard_conditions = tuple(
                        guard_info.get(
                            "common",
                            (block_guard_conditions or {}).get(block_key, ()),
                        )
                    )
                    path_condition_sets = tuple(
                        tuple(path_conditions or ())
                        for path_conditions in guard_info.get("paths", ())
                    )
                    store_effect = self._store_effect_ref_for_op(
                        op,
                        scope=pcode_scope,
                        guard_constraints=guard_conditions,
                        path_condition_sets=path_condition_sets,
                        guard_paths_incomplete=bool(guard_info.get("incomplete", False)),
                    )
                    if pcode_scope == "loop":
                        has_memory_writes = True
                        descriptors.append(store_effect)
                    else:
                        has_context_memory_writes = True
                        context_descriptors.append(store_effect)
                    continue
                if mnemonic in {"CALL", "CALLIND"}:
                    call_effect = LoopBodyEffectRef(
                        kind="call",
                        source="pcode_scan",
                        scope=pcode_scope,
                        target_ref=self._call_target_ref_for_op(op),
                        order_key=self._pcode_op_order_key(op),
                    )
                    if pcode_scope == "loop":
                        has_calls = True
                        has_escapes = True
                        descriptors.append(call_effect)
                    else:
                        has_context_calls = True
                        has_context_escapes = True
                        context_descriptors.append(call_effect)
                    continue
                if mnemonic == "BRANCHIND":
                    escape_effect = LoopBodyEffectRef(
                        kind="escape",
                        source="pcode_scan",
                        scope=pcode_scope,
                        order_key=self._pcode_op_order_key(op),
                    )
                    if pcode_scope == "loop":
                        has_escapes = True
                        descriptors.append(escape_effect)
                    else:
                        has_context_escapes = True
                        context_descriptors.append(escape_effect)
                    continue
                if mnemonic == "CBRANCH" and id(op) not in ignored_ids:
                    condition = self._condition_for_cbranch_op(op)
                    guard_effect = LoopBodyEffectRef(
                        kind="conditional_guard",
                        source="pcode_scan",
                        scope=pcode_scope,
                        guard_constraints=(condition,) if condition is not None else (),
                        order_key=self._pcode_op_order_key(op),
                    )
                    if pcode_scope == "loop":
                        has_conditional_guards = True
                        descriptors.append(guard_effect)
                    else:
                        has_context_conditional_guards = True
                        context_descriptors.append(guard_effect)

        guard_count = sum(1 for effect in descriptors if effect.kind == "conditional_guard")
        profile = self._loop_effect_profile_name(
            memory_reads=has_memory_reads,
            memory_writes=has_memory_writes,
            calls=has_calls,
            escapes=has_escapes,
            conditional_guards=has_conditional_guards,
        )
        return LoopSideEffectProfileRef(
            profile=profile,
            memory_reads=has_memory_reads,
            memory_writes=has_memory_writes,
            calls=has_calls,
            escapes=has_escapes,
            conditional_guards=has_conditional_guards,
            context_memory_writes=has_context_memory_writes,
            context_calls=has_context_calls,
            context_escapes=has_context_escapes,
            context_conditional_guards=has_context_conditional_guards,
            effect_count=len(descriptors),
            guard_count=guard_count,
            effect_descriptors=tuple(descriptors),
            context_descriptors=tuple(context_descriptors),
        )

    def _store_effect_ref_for_op(
        self,
        op,
        *,
        scope: str,
        guard_constraints: Sequence[Condition] = (),
        path_condition_sets: Sequence[Sequence[Condition]] = (),
        guard_paths_incomplete: bool = False,
    ) -> LoopBodyEffectRef:
        address_space = None
        address_expr = None
        value_expr = None
        unkeyable_reasons: List[str] = []
        input_count = self._safe_pcode_input_count(op)
        if input_count >= 3:
            address_space = self._store_address_space_ref_for_op(op)
            try:
                address_expr = self._build_pcode_expression(op.getInput(1), placeholders={})
            except RecursionError:
                address_expr = None
            try:
                value_expr = self._build_pcode_expression(op.getInput(2), placeholders={})
            except RecursionError:
                value_expr = None
        if address_space is None:
            unkeyable_reasons.append("store_address_space_unresolved")
        if address_expr is None or self._expression_is_unresolved(address_expr):
            address_expr = None
            unkeyable_reasons.append("store_address_unresolved")
        if value_expr is None or self._expression_is_unresolved(value_expr):
            value_expr = None
            unkeyable_reasons.append("store_value_unresolved")
        if guard_paths_incomplete:
            unkeyable_reasons.append("store_guard_paths_incomplete")
        return LoopBodyEffectRef(
            kind="memory_write",
            source="pcode_scan",
            scope=scope,
            address_space=address_space,
            location=address_expr,
            value_expr=value_expr,
            guard_constraints=tuple(guard_constraints or ()),
            path_condition_sets=tuple(
                tuple(path_conditions or ())
                for path_conditions in (path_condition_sets or ())
            ),
            guard_paths_incomplete=bool(guard_paths_incomplete),
            order_key=self._pcode_op_order_key(op),
            keyable=not unkeyable_reasons,
            unkeyable_reason=";".join(unkeyable_reasons) if unkeyable_reasons else None,
        )

    def _store_address_space_ref_for_op(self, op):
        if op is None or self._safe_pcode_input_count(op) < 1:
            return None
        space_varnode = op.getInput(0)

        address = getattr(space_varnode, "getAddress", lambda: None)()
        address_space = getattr(address, "getAddressSpace", lambda: None)() if address is not None else None
        input_space_ref = self._address_space_ref(address_space)
        offset = getattr(space_varnode, "getOffset", lambda: None)()
        size = getattr(space_varnode, "getSize", lambda: None)()
        offset_int = self._safe_int(offset)
        size_int = self._safe_int(size)
        target_space_ref = self._resolve_store_target_address_space_ref(offset_int)
        space_name = (input_space_ref or {}).get("space_name")
        space_id = (input_space_ref or {}).get("space_id")
        if space_name is None:
            name = getattr(space_varnode, "_name", None)
            if name:
                space_name = str(name)
        if target_space_ref is not None:
            return {
                "encoding": "ghidra_store_space_id",
                "space_name": target_space_ref.get("space_name"),
                "space_id": target_space_ref.get("space_id"),
                "space_type": target_space_ref.get("space_type"),
                "is_memory_space": target_space_ref.get("is_memory_space"),
                "is_register_space": target_space_ref.get("is_register_space"),
                "is_stack_space": target_space_ref.get("is_stack_space"),
                "pcode_input_space": input_space_ref,
                "pcode_space_id_constant": offset_int,
                "size": size_int,
            }
        if space_name is None and space_id is None and offset_int is None and size_int is None:
            name = getattr(space_varnode, "_name", None)
            if name:
                return {"space_name": str(name)}
            try:
                expr = self._build_pcode_expression(space_varnode, placeholders={})
            except RecursionError:
                expr = None
            if expr is not None and not self._expression_is_unresolved(expr):
                return expr
            return None
        return {
            "encoding": "pcode_input_space_metadata",
            "space_name": space_name,
            "space_id": space_id,
            "offset": offset_int,
            "size": size_int,
        }

    def _resolve_store_target_address_space_ref(self, space_id: Optional[int]) -> Optional[Dict[str, Any]]:
        if space_id is None:
            return None
        program = getattr(self.tracer, "program", None)
        address_factory_getter = getattr(program, "getAddressFactory", None)
        if not callable(address_factory_getter):
            return None
        try:
            address_factory = address_factory_getter()
        except (AttributeError, TypeError, ValueError, RuntimeError, LookupError):
            return None
        get_address_space = getattr(address_factory, "getAddressSpace", None)
        if not callable(get_address_space):
            return None
        try:
            address_space = get_address_space(int(space_id))
        except (AttributeError, TypeError, ValueError, RuntimeError, LookupError):
            return None
        return self._address_space_ref(address_space)

    def _address_space_ref(self, address_space) -> Optional[Dict[str, Any]]:
        if address_space is None:
            return None
        space_name = self._safe_call(address_space, "getName")
        space_id = self._safe_int(self._safe_call(address_space, "getSpaceID"))
        if space_name is None and space_id is None:
            return None
        return {
            "space_name": None if space_name is None else str(space_name),
            "space_id": space_id,
            "space_type": self._safe_int(self._safe_call(address_space, "getType")),
            "is_memory_space": self._safe_bool_call(address_space, "isMemorySpace"),
            "is_register_space": self._safe_bool_call(address_space, "isRegisterSpace"),
            "is_stack_space": self._safe_bool_call(address_space, "isStackSpace"),
        }

    def _safe_call(self, obj, method_name: str):
        method = getattr(obj, method_name, None)
        if not callable(method):
            return None
        try:
            return method()
        except (AttributeError, TypeError, ValueError, RuntimeError):
            return None

    def _safe_bool_call(self, obj, method_name: str) -> Optional[bool]:
        value = self._safe_call(obj, method_name)
        if value is None:
            return None
        return bool(value)

    def _safe_int(self, value) -> Optional[int]:
        if value is None:
            return None
        try:
            return int(value)
        except (TypeError, ValueError, OverflowError):
            return None

    def _pcode_op_order_key(self, op) -> Optional[int]:
        sequence = getattr(op, "getSeqnum", lambda: None)()
        if sequence is not None:
            order = getattr(sequence, "getOrder", lambda: None)()
            if order is not None:
                try:
                    return int(order)
                except (TypeError, ValueError):
                    pass
        order = getattr(op, "getOrder", lambda: None)()
        if order is not None:
            try:
                return int(order)
            except (TypeError, ValueError):
                return None
        return None

    def _call_target_ref_for_op(self, op):
        if op is None or self._safe_pcode_input_count(op) < 1:
            return None
        resolver = getattr(self.tracer, "resolve_call_target_ref", None)
        if not callable(resolver):
            return None
        try:
            return resolver(op.getInput(0))
        except (AttributeError, TypeError, ValueError, RecursionError):
            return None

    def _condition_for_cbranch_op(self, op) -> Optional[Condition]:
        if op is None or self._safe_pcode_input_count(op) < 2:
            return None
        try:
            expr = self._build_pcode_expression(op.getInput(1), placeholders={})
        except RecursionError:
            return None
        if expr is None or self._expression_is_unresolved(expr):
            return None
        return Condition(expr, False)

    def _build_counted_scalar_loop_summary(
        self,
        function,
        high_function,
        analysis,
        *,
        pre_return_ops: Optional[Sequence] = None,
    ) -> Optional[Tuple[List[ReturnInfo], str]]:
        if function is None or high_function is None:
            return None

        model = self._extract_counted_scalar_loop_model(high_function, analysis)
        if model is None:
            if pre_return_ops is not None:
                self._debug("Declined pre-return counted loop summary: no validated counted-loop model")
            return None

        induction, accumulator, guard, residue_cases = model
        update_cases = self._try_extract_counted_loop_update_cases_for_summary(accumulator, induction, guard)
        loop_cases = self._build_counted_loop_case_refs(update_cases)
        start_expr = induction.init_expr
        limit_expr = guard.bound_expr
        header_block = getattr(induction.phi_op, "getParent", lambda: None)()
        loop_body_blocks = self._collect_loop_body_blocks(
            header_block=header_block,
            guard=guard,
        )
        loop_block_guard_info = self._loop_block_guard_effect_info(
            header_block=header_block,
            guard=guard,
            loop_blocks=loop_body_blocks,
        )
        ignored_branch_ops = [
            self._find_cbranch_op(block)
            for block in (header_block, guard.latch_block)
            if block is not None
        ]
        side_effect_profile = self._build_loop_side_effect_profile(
            analysis=analysis,
            loop_blocks=loop_body_blocks,
            ignored_branch_ops=ignored_branch_ops,
            block_guard_info=loop_block_guard_info,
        )
        if side_effect_profile.calls or side_effect_profile.escapes:
            self._debug("Declined counted scalar loop summary: loop body contains calls or escaping control flow")
            return None
        entry_guard_expr = self._substitute_exact_expression(
            guard.condition_expr,
            induction.placeholder,
            start_expr,
        )
        derived_continue_condition = Condition(entry_guard_expr or guard.condition_expr, False)
        derived_base_condition = derived_continue_condition.negate()
        original_conditions = self._derive_direct_counted_loop_conditions(high_function, induction, guard)
        if original_conditions is None:
            continue_conditions = ConditionSimplifier.simplify_conditions_object_centric([derived_continue_condition])
            base_conditions = ConditionSimplifier.simplify_conditions_object_centric([derived_base_condition])
        else:
            base_conditions, continue_conditions = original_conditions
            base_conditions, continue_conditions = self._repair_two_way_partition_conditions(
                base_conditions,
                continue_conditions,
            )

        base_return_expr = self._canonicalize_zero_value_under_conditions(
            accumulator.init_expr,
            base_conditions,
        )
        loop_base_expr = self._canonicalize_zero_value_under_conditions(
            accumulator.init_expr,
            continue_conditions,
        )
        loop_value = self._build_counted_loop_summary_value(
            base_expr=loop_base_expr,
            start_expr=start_expr,
            limit_expr=limit_expr,
            induction_step=induction.step,
            residue_cases=residue_cases,
            result_size=loop_base_expr.size or accumulator.placeholder.size or 4,
            signed_loop=induction.signed_guard or guard.signed_comparison,
            side_effect_profile=side_effect_profile,
            guard_constraints=continue_conditions,
            cases=loop_cases,
        )
        if loop_value is None:
            return None

        anchor = next(iter((getattr(analysis, "returns", None) or [])), None)
        address = getattr(anchor, "address", getattr(function, "getEntryPoint", lambda: "0x0")())
        pcode_identity = getattr(anchor, "pcode_identity", None)
        pcode_order = getattr(anchor, "pcode_order", None)
        pcode_time = getattr(anchor, "pcode_time", None)

        summarized = [
            ReturnInfo(
                address=str(address),
                value=base_return_expr,
                conditions=base_conditions,
                branch_index=20_100,
                pcode_identity=pcode_identity,
                pcode_order=pcode_order,
                pcode_time=pcode_time,
            )
        ]
        summarized.append(
            ReturnInfo(
                address=str(address),
                value=loop_value,
                conditions=continue_conditions,
                branch_index=20_100 + len(summarized),
                pcode_identity=pcode_identity,
                pcode_order=pcode_order,
                pcode_time=pcode_time,
            )
        )
        loop_case = summarized[-1]
        canonical_value = self._canonicalize_peeled_counted_loop_value(
            loop_case.value,
            continue_conditions=continue_conditions,
            parameters=self._collect_summary_parameter_specs(
                loop_case.value,
                loop_base_expr,
                start_expr,
                limit_expr,
                *(cond.expression for cond in continue_conditions or [] if cond is not None),
            ),
            base_expr=loop_base_expr,
            limit_expr=limit_expr,
            induction_step=induction.step,
            residue_cases=residue_cases,
            result_size=loop_base_expr.size or accumulator.placeholder.size or 4,
            signed_loop=induction.signed_guard or guard.signed_comparison,
            side_effect_profile=side_effect_profile,
            guard_constraints=continue_conditions,
            cases=loop_cases,
        )
        canonical_value = self._canonicalize_zero_prefix_counted_loop_value(
            canonical_value,
            base_expr=loop_base_expr,
            limit_expr=limit_expr,
            induction_step=induction.step,
            residue_cases=residue_cases,
            result_size=loop_base_expr.size or accumulator.placeholder.size or 4,
            signed_loop=induction.signed_guard or guard.signed_comparison,
            side_effect_profile=side_effect_profile,
            guard_constraints=continue_conditions,
            cases=loop_cases,
        )
        if canonical_value is not None and not canonical_value.equals(loop_case.value):
            summarized[-1] = ReturnInfo(
                address=loop_case.address,
                value=canonical_value,
                conditions=list(loop_case.conditions or []),
                branch_index=loop_case.branch_index,
                pcode_identity=loop_case.pcode_identity,
                pcode_order=loop_case.pcode_order,
                pcode_time=loop_case.pcode_time,
            )
        effective_loop_value = summarized[-1].value
        effective_start_expr = start_expr
        if (
            effective_loop_value is not None
            and getattr(effective_loop_value, "expr_type", None) == ExpressionType.INTRINSIC
            and len(getattr(effective_loop_value, "operands", None) or []) == 3
        ):
            effective_start_expr = effective_loop_value.operands[1]
        self._debug(
            "Recovered counted scalar loop summary "
            f"(start={self._safe_expr_text(effective_start_expr)}, limit={self._safe_expr_text(limit_expr)}, "
            f"step={induction.step}, "
            f"cases={[(case.modulus, case.residue, case.affine) for case in residue_cases]})"
        )
        return summarized, "counted_scalar_loop_summary"

    def _safe_pcode_input_count(self, op) -> int:
        try:
            value = getattr(op, "getNumInputs", lambda: 0)()
            if not isinstance(value, (int, float, str, bytes)):
                return 0
            return int(value or 0)
        except Exception:
            return 0

    def _build_counted_loop_summary_value(
        self,
        *,
        base_expr: Expression,
        start_expr: Expression,
        limit_expr: Expression,
        induction_step: int,
        residue_cases: Sequence[ResidueLoopCase],
        result_size: int,
        signed_loop: bool,
        side_effect_profile: Optional[LoopSideEffectProfileRef] = None,
        guard_constraints: Sequence[Condition] = (),
        cases: Sequence[LoopCaseRef] = (),
    ) -> Optional[Expression]:
        if any(
            self._expression_is_unresolved(expr)
            for expr in (base_expr, start_expr, limit_expr)
        ):
            return None
        intrinsic = self._build_counted_loop_summary_intrinsic(
            base_expr=base_expr,
            start_expr=start_expr,
            limit_expr=limit_expr,
            induction_step=induction_step,
            residue_cases=residue_cases,
            result_size=result_size,
            signed_loop=signed_loop,
            side_effect_profile=side_effect_profile,
            guard_constraints=guard_constraints,
            cases=cases,
        )
        if intrinsic is not None:
            return intrinsic
        return None

    def _build_counted_loop_summary_intrinsic(
        self,
        *,
        base_expr: Expression,
        start_expr: Expression,
        limit_expr: Expression,
        induction_step: int,
        residue_cases: Sequence[ResidueLoopCase],
        result_size: int,
        signed_loop: bool,
        side_effect_profile: Optional[LoopSideEffectProfileRef] = None,
        guard_constraints: Sequence[Condition] = (),
        cases: Sequence[LoopCaseRef] = (),
    ) -> Optional[Expression]:
        if induction_step == 0 or not residue_cases:
            return None
        step_expr = Expression.constant(
            int(induction_step),
            size=max(1, int(getattr(start_expr, "size", 0) or getattr(limit_expr, "size", 0) or 4)),
        )
        term_descriptor = LoopTermDescriptorRef(
            kind="affine_residue",
            reduction_kind="sum",
            result_size=max(1, int(result_size or 0)),
            residue_cases=tuple(
                (
                    int(case.modulus),
                    int(case.residue),
                    int(case.affine[0]),
                    int(case.affine[1]),
                )
                for case in residue_cases
            ),
        )
        loop_summary = LoopSummaryRef(
            start_expr=start_expr,
            limit_expr=limit_expr,
            step_expr=step_expr,
            term_descriptor=term_descriptor,
            seed_terms=(),
            witnesses=(),
            side_effect_profile=side_effect_profile or LoopSideEffectProfileRef(profile="pure"),
            guard_constraints=tuple(guard_constraints or ()),
            cases=tuple(cases or ()),
            loop_var_unit="induction_value",
        )
        runtime_ref = CountedLoopSummaryRef(
            induction_step=int(induction_step),
            result_size=max(1, int(result_size or 0)),
            signed_loop=bool(signed_loop),
            residue_cases=term_descriptor.residue_cases,
            loop_summary=loop_summary,
        )
        intrinsic = Expression.intrinsic(
            "COUNTED_LOOP_SUM",
            [base_expr, start_expr, limit_expr],
            size=max(1, int(result_size or 0)),
            runtime_ref=runtime_ref,
            opcode=COUNTED_LOOP_SUM_OPCODE,
        )
        intrinsic.size = max(1, int(result_size or 0))
        return intrinsic

    def _canonicalize_zero_value_under_conditions(
        self,
        expr: Expression,
        conditions: Sequence[Condition],
    ) -> Expression:
        if expr is None:
            return expr
        zero = Expression.constant(0, size=max(1, int(getattr(expr, "size", 0) or 4)))
        if expr.equals(zero):
            return expr
        parameters = self._collect_summary_parameter_specs(
            expr,
            *(condition.expression for condition in conditions or [] if condition is not None),
        )
        if not self._prove_expression_equivalence_under_conditions(
            expr,
            zero,
            conditions,
            parameters,
        ):
            return expr
        self._debug(
            "Canonicalized counted loop summary base to zero under case conditions "
            f"(original={self._safe_expr_text(expr)})"
        )
        return zero

    def _canonicalize_zero_prefix_counted_loop_value(
        self,
        value: Optional[Expression],
        *,
        base_expr: Expression,
        limit_expr: Expression,
        induction_step: int,
        residue_cases: Sequence[ResidueLoopCase],
        result_size: int,
        signed_loop: bool,
        side_effect_profile: Optional[LoopSideEffectProfileRef] = None,
        guard_constraints: Sequence[Condition] = (),
        cases: Sequence[LoopCaseRef] = (),
    ) -> Optional[Expression]:
        if value is None or getattr(value, "expr_type", None) != ExpressionType.INTRINSIC:
            return value
        if getattr(value, "opcode", None) != COUNTED_LOOP_SUM_OPCODE and getattr(value, "name", None) != "COUNTED_LOOP_SUM":
            return value
        operands = list(getattr(value, "operands", None) or [])
        if len(operands) != 3:
            return value
        start_raw = self._raw_constant_value(operands[1])
        if start_raw is None:
            return value
        start = int(start_raw)
        if start <= 0 or start > 16 or int(induction_step) != 1:
            return value
        if not self._counted_loop_prefix_contributes_zero(start, residue_cases):
            return value
        zero_start = Expression.constant(
            0,
            size=max(1, int(getattr(operands[1], "size", 0) or getattr(limit_expr, "size", 0) or 4)),
        )
        canonical = self._build_counted_loop_summary_intrinsic(
            base_expr=base_expr,
            start_expr=zero_start,
            limit_expr=limit_expr,
            induction_step=induction_step,
            residue_cases=residue_cases,
            result_size=result_size,
            signed_loop=signed_loop,
            side_effect_profile=side_effect_profile,
            guard_constraints=guard_constraints,
            cases=cases,
        )
        if canonical is None:
            return value
        self._debug(
            "Canonicalized counted loop zero-contribution prefix to zero-start summary "
            f"(original start={start})"
        )
        return canonical

    def _counted_loop_prefix_contributes_zero(
        self,
        stop: int,
        residue_cases: Sequence[ResidueLoopCase],
    ) -> bool:
        if stop <= 0 or not residue_cases:
            return False
        for index in range(stop):
            matched = [
                case
                for case in residue_cases
                if int(case.modulus) > 0 and index % int(case.modulus) == int(case.residue)
            ]
            if len(matched) != 1:
                return False
            coeff, bias = matched[0].affine
            if int(coeff) * index + int(bias) != 0:
                return False
        return True

    def _canonicalize_peeled_counted_loop_value(
        self,
        value: Expression,
        *,
        continue_conditions: Sequence[Condition],
        parameters: Sequence[dict],
        base_expr: Expression,
        limit_expr: Expression,
        induction_step: int,
        residue_cases: Sequence[ResidueLoopCase],
        result_size: int,
        signed_loop: bool,
        side_effect_profile: Optional[LoopSideEffectProfileRef] = None,
        guard_constraints: Sequence[Condition] = (),
        cases: Sequence[LoopCaseRef] = (),
    ) -> Optional[Expression]:
        if value is None or getattr(value, "expr_type", None) != ExpressionType.INTRINSIC:
            return value
        if getattr(value, "opcode", None) != COUNTED_LOOP_SUM_OPCODE and getattr(value, "name", None) != "COUNTED_LOOP_SUM":
            return value
        operands = list(getattr(value, "operands", None) or [])
        if len(operands) != 3:
            return value
        start_expr = operands[1]
        if not self._looks_like_peeled_counted_loop_start(start_expr, limit_expr):
            return value

        zero_start = Expression.constant(
            0,
            size=max(1, int(getattr(start_expr, "size", 0) or getattr(limit_expr, "size", 0) or 4)),
        )
        canonical = self._build_counted_loop_summary_intrinsic(
            base_expr=base_expr,
            start_expr=zero_start,
            limit_expr=limit_expr,
            induction_step=induction_step,
            residue_cases=residue_cases,
            result_size=result_size,
            signed_loop=signed_loop,
            side_effect_profile=side_effect_profile,
            guard_constraints=guard_constraints,
            cases=cases,
        )
        if canonical is None:
            return value
        if not self._prove_expression_equivalence_under_conditions(
            value,
            canonical,
            continue_conditions,
            parameters,
        ):
            return value
        self._debug(
            "Canonicalized peeled counted loop start to zero-start counted summary "
            f"(original start={self._safe_expr_text(start_expr)})"
        )
        return canonical

    def _looks_like_peeled_counted_loop_start(
        self,
        start_expr: Optional[Expression],
        limit_expr: Optional[Expression],
    ) -> bool:
        if start_expr is None or limit_expr is None:
            return False
        if getattr(start_expr, "expr_type", None) != ExpressionType.PHI:
            return False
        branches = list(getattr(start_expr, "value", None) or [])
        if len(branches) < 2:
            return False

        limit_signature = _runtime_expression_signature(limit_expr)
        saw_zero = False
        saw_limit_dependent = False
        for _cond, branch_value in branches:
            if branch_value is None:
                continue
            if self._raw_constant_value(branch_value) == 0:
                saw_zero = True
                continue
            if self._expression_depends_on_signature(branch_value, limit_signature):
                saw_limit_dependent = True
        return saw_zero and saw_limit_dependent

    def _expression_depends_on_signature(
        self,
        expr: Optional[Expression],
        target_signature,
    ) -> bool:
        if expr is None:
            return False
        if _runtime_expression_signature(expr) == target_signature:
            return True
        expr_type = getattr(expr, "expr_type", None)
        if expr_type == ExpressionType.PHI:
            for cond, branch_value in getattr(expr, "value", None) or []:
                if cond is not None and self._expression_depends_on_signature(getattr(cond, "expression", None), target_signature):
                    return True
                if self._expression_depends_on_signature(branch_value, target_signature):
                    return True
            return False
        for operand in getattr(expr, "operands", None) or []:
            if self._expression_depends_on_signature(operand, target_signature):
                return True
        return False

    def _collect_summary_parameter_specs(
        self,
        *exprs: Optional[Expression],
    ) -> List[dict]:
        specs: Dict[str, dict] = {}

        def visit(expr: Optional[Expression]) -> None:
            if expr is None:
                return
            expr_type = getattr(expr, "expr_type", None)
            if expr_type == ExpressionType.PARAMETER:
                name = getattr(expr, "name", None)
                if not name:
                    return
                size = max(1, int(getattr(expr, "size", 0) or 4))
                index = int(getattr(expr, "value", -1) or -1)
                candidate = {
                    "name": name,
                    "index": index,
                    "size": size,
                    "data_type": getattr(expr, "data_type", None),
                }
                existing = specs.get(name)
                if existing is None or int(existing.get("size", 0) or 0) < size:
                    specs[name] = candidate
                return
            if expr_type == ExpressionType.PHI:
                for cond, branch_value in getattr(expr, "value", None) or []:
                    if cond is not None:
                        visit(getattr(cond, "expression", None))
                    visit(branch_value)
                return
            for operand in getattr(expr, "operands", None) or []:
                visit(operand)

        for expr in exprs:
            visit(expr)

        ordered = sorted(
            specs.values(),
            key=lambda item: (
                int(item.get("index", -1)) if int(item.get("index", -1)) >= 0 else 1_000_000,
                item.get("name") or "",
            ),
        )
        for fallback_index, spec in enumerate(ordered):
            if int(spec.get("index", -1)) < 0:
                spec["index"] = fallback_index
        return ordered

    def _collect_expression_symbol_specs(
        self,
        *exprs: Optional[Expression],
    ) -> List[dict]:
        specs: Dict[str, dict] = {}

        def add_symbol(name: Optional[str], size: int, index: int = -1, data_type=None) -> None:
            if not name:
                return
            candidate = {
                "name": name,
                "index": index,
                "size": max(1, int(size or 4)),
                "data_type": data_type,
            }
            existing = specs.get(name)
            if existing is None or int(existing.get("size", 0) or 0) < int(candidate["size"]):
                specs[name] = candidate

        def visit(expr: Optional[Expression]) -> None:
            if expr is None:
                return
            expr_type = getattr(expr, "expr_type", None)
            if expr_type == ExpressionType.PARAMETER:
                add_symbol(
                    getattr(expr, "name", None),
                    int(getattr(expr, "size", 0) or 4),
                    int(getattr(expr, "value", -1) or -1),
                    getattr(expr, "data_type", None),
                )
                return
            if expr_type == ExpressionType.VARIABLE:
                add_symbol(
                    getattr(expr, "name", None),
                    int(getattr(expr, "size", 0) or 4),
                    -1,
                    getattr(expr, "data_type", None),
                )
                return
            if expr_type == ExpressionType.PHI:
                for cond, branch_value in getattr(expr, "value", None) or []:
                    if cond is not None:
                        visit(getattr(cond, "expression", None))
                    visit(branch_value)
                return
            for operand in getattr(expr, "operands", None) or []:
                visit(operand)

        for expr in exprs:
            visit(expr)
        ordered = sorted(
            specs.values(),
            key=lambda item: (
                int(item.get("index", -1)) if int(item.get("index", -1)) >= 0 else 1_000_000,
                item.get("name") or "",
            ),
        )
        for fallback_index, spec in enumerate(ordered):
            if int(spec.get("index", -1)) < 0:
                spec["index"] = fallback_index
        return ordered

    def _prove_expression_equivalence_under_conditions(
        self,
        left: Expression,
        right: Expression,
        conditions: Sequence[Condition],
        parameters: Sequence[dict],
    ) -> bool:
        if left.equals(right):
            return True
        query = self._build_expression_equivalence_query(left, right, conditions, parameters)
        if not query:
            return False
        solver = Z3Solver(timeout=2, debug=self.debug)
        result = solver.check_equivalence_direct(query)
        return result.status == SolverStatus.UNSAT

    def _build_expression_equivalence_query(
        self,
        left: Expression,
        right: Expression,
        conditions: Sequence[Condition],
        parameters: Sequence[dict],
    ) -> Optional[str]:
        if left is None or right is None:
            return None
        declarations = ["(set-logic QF_BV)"]

        expression_symbols = self._collect_expression_symbol_specs(
            left,
            right,
            *(condition.expression for condition in conditions or [] if condition is not None),
        )
        symbol_specs: Dict[str, dict] = {str(item.get("name")): dict(item) for item in expression_symbols}
        for parameter in parameters or []:
            name = str(parameter.get("name") or "")
            if not name:
                continue
            existing = symbol_specs.get(name)
            if existing is None or int(existing.get("size", 0) or 0) < int(parameter.get("size", 0) or 0):
                symbol_specs[name] = dict(parameter)

        symbol_infos = self._build_auxiliary_parameter_infos(
            symbol_specs.values(),
        )
        for symbol in symbol_infos:
            declarations.append(f"(declare-const {symbol.smt_name} (_ BitVec {symbol.bit_width}))")
        render = build_symbol_replacer(symbol_infos, [])

        intrinsic_declarations: List[str] = []
        for expr in (left, right):
            for declaration in collect_intrinsic_smt_declarations(expr):
                if declaration not in intrinsic_declarations:
                    intrinsic_declarations.append(declaration)
        for condition in conditions or []:
            if condition is None:
                continue
            for declaration in collect_intrinsic_smt_declarations(condition.expression):
                if declaration not in intrinsic_declarations:
                    intrinsic_declarations.append(declaration)
        declarations.extend(intrinsic_declarations)

        assertions = []
        for condition in conditions or []:
            if condition is None:
                continue
            assertions.append(f"(assert {render(condition)})")
        target_bits = max(1, self._expression_equivalence_target_bits(left, right))
        left_smt = coerce_value_to_bitvec_width(
            left,
            render(left),
            target_bits,
            use_sign_extension=False,
        )
        right_smt = coerce_value_to_bitvec_width(
            right,
            render(right),
            target_bits,
            use_sign_extension=False,
        )
        assertions.append(f"(assert (not (= {left_smt} {right_smt})))")
        return "\n".join(declarations + assertions + ["(check-sat)"])

    def _expression_equivalence_target_bits(
        self,
        left: Expression,
        right: Expression,
    ) -> int:
        left_bits = int(getattr(left, "get_bit_width", lambda: 0)() or 0)
        right_bits = int(getattr(right, "get_bit_width", lambda: 0)() or 0)
        try:
            from ..model.render_smt import expression_smt_bit_width

            left_bits = max(left_bits, int(expression_smt_bit_width(left) or 0))
            right_bits = max(right_bits, int(expression_smt_bit_width(right) or 0))
        except Exception:
            pass
        return max(left_bits, right_bits, 32)

    def _build_auxiliary_parameter_infos(
        self,
        symbol_specs: Sequence[dict],
    ) -> List[ParameterInfo]:
        infos: List[ParameterInfo] = []
        seen: set[str] = set()
        for spec in sorted(
            symbol_specs or [],
            key=lambda item: (
                int(item.get("index", -1)) if int(item.get("index", -1)) >= 0 else 1_000_000,
                item.get("name") or "",
            ),
        ):
            name = str(spec.get("name") or "")
            if not name or name in seen:
                continue
            seen.add(name)
            width_bits = max(1, int(spec.get("size", 0) or 4)) * 8
            infos.append(
                ParameterInfo(
                    original_name=name,
                    smt_name=f"{name}_aux",
                    bit_width=width_bits,
                    index=int(spec.get("index", -1) or -1),
                    is_signed=bool(spec.get("is_signed", True)),
                )
            )
        return infos

    def _negate_simple_condition_set(
        self,
        conditions: Sequence[Condition],
    ) -> Optional[List[Condition]]:
        simplified = ConditionSimplifier.simplify_conditions_object_centric(list(conditions or []))
        if len(simplified) != 1:
            return None
        return ConditionSimplifier.simplify_conditions_object_centric([simplified[0].negate()])

    def _repair_two_way_partition_conditions(
        self,
        base_conditions: Sequence[Condition],
        continue_conditions: Sequence[Condition],
    ) -> Tuple[List[Condition], List[Condition]]:
        base_simplified = ConditionSimplifier.simplify_conditions_object_centric(list(base_conditions or []))
        continue_simplified = ConditionSimplifier.simplify_conditions_object_centric(list(continue_conditions or []))

        if not base_simplified and continue_simplified:
            negated_continue = self._negate_simple_condition_set(continue_simplified)
            if negated_continue is not None:
                base_simplified = negated_continue
        elif not continue_simplified and base_simplified:
            negated_base = self._negate_simple_condition_set(base_simplified)
            if negated_base is not None:
                continue_simplified = negated_base

        return base_simplified, continue_simplified

    def _derive_direct_counted_loop_conditions(
        self,
        high_function,
        induction: CountedLoopInduction,
        guard: CountedLoopGuard,
    ) -> Optional[Tuple[List[Condition], List[Condition]]]:
        if high_function is None or induction is None:
            return None

        header_block = getattr(induction.phi_op, "getParent", lambda: None)()
        if header_block is None:
            return None
        preheader = None
        in_size = int(getattr(header_block, "getInSize", lambda: 0)() or 0)
        entry_index = self._induction_init_index(induction)
        if entry_index < in_size:
            preheader = header_block.getIn(entry_index)
        if preheader is None:
            return None

        entry_blocks = [
            block
            for block in self._iter_basic_blocks(high_function)
            if int(getattr(block, "getInSize", lambda: 0)() or 0) == 0
        ]
        if not entry_blocks:
            return None

        path_sets: List[List[Condition]] = []
        for entry_block in entry_blocks:
            path_sets.extend(
                self._enumerate_paths_with_conditions(
                    start_block=entry_block,
                    target_block=preheader,
                    header_block=header_block,
                    placeholders={},
                    stop_block=guard.exit_block,
                    limit=16,
                )
            )
        if not path_sets:
            return None
        common = self._common_conditions_across_paths(path_sets)
        if not common:
            return None
        negated = self._negate_simple_condition_set(common)
        if negated is None:
            return None
        return negated, common

    def _common_conditions_across_paths(
        self,
        path_sets: Sequence[Sequence[Condition]],
    ) -> List[Condition]:
        if not path_sets:
            return []
        normalized_sets = [
            ConditionSimplifier.simplify_conditions_object_centric(list(conditions or []))
            for conditions in path_sets
        ]
        common = list(normalized_sets[0])
        for conditions in normalized_sets[1:]:
            condition_map = {
                _runtime_conditions_signature([condition]): condition
                for condition in conditions
            }
            common = [
                condition
                for condition in common
                if _runtime_conditions_signature([condition]) in condition_map
            ]
            if not common:
                break
        return ConditionSimplifier.simplify_conditions_object_centric(common)

    def _extract_counted_scalar_loop_model(
        self,
        high_function,
        analysis,
    ) -> Optional[Tuple[CountedLoopInduction, CountedLoopAccumulator, CountedLoopGuard, Tuple[ResidueLoopCase, ...]]]:
        blocks = list(self._iter_basic_blocks(high_function))
        if not blocks:
            return None
        best_model = None
        best_score = None

        for header in blocks:
            cbranch = self._find_cbranch_op(header)
            if cbranch is None:
                continue
            phi_ops = [
                op for op in self._iter_block_ops(header)
                if getattr(op, "getMnemonic", lambda: None)() == "MULTIEQUAL"
            ]
            if len(phi_ops) < 2:
                continue

            induction_candidates = [
                info for info in (
                    self._match_counted_loop_induction(phi_op)
                    for phi_op in phi_ops
                )
                if info is not None
            ]
            if not induction_candidates:
                continue

            for induction in induction_candidates:
                guards = self._candidate_counted_loop_guards(header, cbranch, induction)
                if not guards:
                    continue
                for guard in guards:
                    for accumulator in self._match_counted_loop_accumulators(
                        phi_ops,
                        induction,
                        guard.body_block,
                    ):
                        cases = self._extract_counted_loop_update_cases(
                            accumulator,
                            induction,
                            guard,
                        )
                        if not cases:
                            continue
                        residue_cases = self._extract_residue_loop_cases(
                            cases,
                            induction.placeholder.name or "__loop_iv",
                        )
                        if residue_cases is None:
                            continue
                        if not self._validate_counted_loop_update_cases(
                            cases=cases,
                            residue_cases=residue_cases,
                            induction=induction,
                            accumulator=accumulator,
                        ):
                            continue
                        score = self._counted_loop_model_priority(accumulator, residue_cases)
                        if best_score is None or score > best_score:
                            best_model = (induction, accumulator, guard, residue_cases)
                            best_score = score

        return best_model

    def _candidate_counted_loop_guards(
        self,
        header_block,
        cbranch_op,
        induction: CountedLoopInduction,
    ) -> List[CountedLoopGuard]:
        guards: List[CountedLoopGuard] = []
        seen = set()
        for candidate in (
            self._match_latch_counted_loop_guard(header_block, induction),
            self._match_counted_loop_guard(header_block, cbranch_op, induction),
        ):
            if candidate is None:
                continue
            key = (
                _runtime_expression_signature(candidate.condition_expr),
                _runtime_expression_signature(candidate.bound_expr),
                self._block_key(candidate.body_block),
                self._block_key(candidate.exit_block),
                self._block_key(candidate.latch_block),
            )
            if key in seen:
                continue
            seen.add(key)
            guards.append(candidate)
        return guards

    def _iter_basic_blocks(self, high_function) -> Iterable:
        try:
            for block in high_function.getBasicBlocks():
                yield block
        except Exception:
            return

    def _iter_block_ops(self, block) -> Iterable:
        iterator = getattr(block, "getIterator", lambda: None)()
        if iterator is None:
            return
        while iterator.hasNext():
            yield iterator.next()

    def _find_cbranch_op(self, block):
        for op in self._iter_block_ops(block):
            if getattr(op, "getMnemonic", lambda: None)() == "CBRANCH":
                return op
        return None

    def _make_pcode_op_ref(self, pcode_op) -> Optional[PcodeOpRef]:
        if pcode_op is None:
            return None
        address_offset = None
        seq_time = None
        seq_order = None
        try:
            seq = pcode_op.getSeqnum()
        except Exception:
            seq = None
        if seq is not None:
            try:
                target = seq.getTarget()
                address_offset = int(target.getOffset()) if target is not None else None
            except Exception:
                address_offset = None
            try:
                seq_time = int(seq.getTime())
            except Exception:
                seq_time = None
            try:
                seq_order = int(seq.getOrder())
            except Exception:
                seq_order = None
        parent = getattr(pcode_op, "getParent", lambda: None)()
        block_ref = self._make_pcode_block_ref(parent)
        return PcodeOpRef(
            address_offset=address_offset,
            seq_time=seq_time,
            seq_order=seq_order,
            block_index=block_ref.block_index if block_ref is not None else None,
            mnemonic=getattr(pcode_op, "getMnemonic", lambda: None)(),
        )

    def _make_pcode_block_ref(self, block) -> Optional[PcodeBlockRef]:
        if block is None:
            return None
        block_index = None
        start_address_offset = None
        try:
            block_index = int(block.getIndex())
        except Exception:
            block_index = None
        try:
            start = block.getStart()
            start_address_offset = int(start.getOffset()) if start is not None else None
        except Exception:
            start_address_offset = None
        if block_index is None and start_address_offset is None:
            return None
        return PcodeBlockRef(
            block_index=block_index,
            start_address_offset=start_address_offset,
        )

    def _collect_block_successors(self, block) -> List[object]:
        successors = []
        out_size = int(getattr(block, "getOutSize", lambda: 0)() or 0)
        for index in range(out_size):
            successor = getattr(block, "getOut", lambda _idx: None)(index)
            if successor is not None:
                successors.append(successor)
        return successors

    def _collect_block_predecessors(self, block) -> List[object]:
        predecessors = []
        in_size = int(getattr(block, "getInSize", lambda: 0)() or 0)
        for index in range(in_size):
            predecessor = getattr(block, "getIn", lambda _idx: None)(index)
            if predecessor is not None:
                predecessors.append(predecessor)
        return predecessors

    def _collect_loop_body_blocks(
        self,
        *,
        header_block,
        guard: CountedLoopGuard,
    ) -> Tuple[object, ...]:
        if guard is None or guard.body_block is None:
            return ()
        natural_loop_blocks = self._collect_natural_loop_blocks(
            header_block=header_block,
            guard=guard,
        )
        if natural_loop_blocks:
            return natural_loop_blocks
        self._debug("Falling back to reachability-based loop body collection")
        return self._collect_reachable_loop_body_blocks(
            header_block=header_block,
            guard=guard,
        )

    def _collect_natural_loop_blocks(
        self,
        *,
        header_block,
        guard: CountedLoopGuard,
    ) -> Tuple[object, ...]:
        if header_block is None or guard is None or guard.body_block is None or guard.latch_block is None:
            return ()
        header_key = self._block_key(header_block)
        latch_key = self._block_key(guard.latch_block)
        body_key = self._block_key(guard.body_block)
        exit_key = self._block_key(guard.exit_block)
        if header_key is None or latch_key is None or body_key is None:
            return ()
        if not any(self._block_key(successor) == header_key for successor in self._collect_block_successors(guard.latch_block)):
            return ()

        blocks_by_key: Dict[object, object] = {
            header_key: header_block,
            latch_key: guard.latch_block,
        }
        stack = [guard.latch_block]
        while stack:
            current = stack.pop()
            for predecessor in self._collect_block_predecessors(current):
                predecessor_key = self._block_key(predecessor)
                if predecessor_key is None or predecessor_key == exit_key:
                    continue
                if predecessor_key in blocks_by_key:
                    continue
                blocks_by_key[predecessor_key] = predecessor
                if predecessor_key != header_key:
                    stack.append(predecessor)

        if body_key not in blocks_by_key:
            return ()
        return tuple(blocks_by_key.values())

    def _collect_reachable_loop_body_blocks(
        self,
        *,
        header_block,
        guard: CountedLoopGuard,
    ) -> Tuple[object, ...]:
        if guard is None or guard.body_block is None:
            return ()
        header_key = self._block_key(header_block)
        exit_key = self._block_key(guard.exit_block)
        blocks_by_key: Dict[object, object] = {}

        def add_block(block) -> None:
            key = self._block_key(block)
            if key is not None and key != exit_key and key not in blocks_by_key:
                blocks_by_key[key] = block

        add_block(header_block)
        add_block(guard.body_block)
        add_block(guard.latch_block)
        stack = [guard.body_block]
        visited = set()
        while stack:
            current = stack.pop()
            current_key = self._block_key(current)
            if current_key in visited or current_key == exit_key:
                continue
            visited.add(current_key)
            add_block(current)
            for successor in self._collect_block_successors(current):
                successor_key = self._block_key(successor)
                if successor_key == exit_key:
                    continue
                if successor_key == header_key:
                    add_block(successor)
                    continue
                if successor_key not in visited:
                    stack.append(successor)
        return tuple(blocks_by_key.values())

    def _loop_block_guard_conditions(
        self,
        *,
        header_block,
        guard: CountedLoopGuard,
        loop_blocks: Sequence[object],
    ) -> Dict[object, Tuple[Condition, ...]]:
        return {
            block_key: tuple(info.get("common", ()))
            for block_key, info in self._loop_block_guard_effect_info(
                header_block=header_block,
                guard=guard,
                loop_blocks=loop_blocks,
            ).items()
        }

    def _loop_block_guard_effect_info(
        self,
        *,
        header_block,
        guard: CountedLoopGuard,
        loop_blocks: Sequence[object],
    ) -> Dict[object, Dict[str, Any]]:
        if guard is None or guard.body_block is None:
            return {}
        result: Dict[object, Dict[str, Any]] = {}
        header_key = self._block_key(header_block)
        body_key = self._block_key(guard.body_block)
        for block in loop_blocks or ():
            block_key = self._block_key(block)
            if block_key in {header_key, body_key}:
                result[block_key] = {
                    "common": (),
                    "paths": ((),),
                    "incomplete": False,
                }
                continue
            paths, incomplete = self._enumerate_paths_with_conditions_result(
                start_block=guard.body_block,
                target_block=block,
                header_block=header_block,
                placeholders={},
                stop_block=guard.exit_block,
                limit=16,
            )
            if not paths:
                result[block_key] = {
                    "common": (),
                    "paths": (),
                    "incomplete": incomplete,
                }
                continue
            result[block_key] = {
                "common": tuple(self._common_conditions_across_paths(paths)),
                "paths": tuple(tuple(path) for path in paths),
                "incomplete": incomplete,
            }
        return result

    def _block_key(self, block) -> object:
        if block is None:
            return None
        block_index = getattr(block, "getIndex", lambda: None)()
        if block_index is not None:
            return ("index", int(block_index))
        return ("id", id(block))

    def _can_reach_block(self, start_block, target_block) -> bool:
        if start_block is None or target_block is None:
            return False
        target_key = self._block_key(target_block)
        stack = [start_block]
        visited = set()
        while stack:
            current = stack.pop()
            current_key = self._block_key(current)
            if current_key in visited:
                continue
            visited.add(current_key)
            if current_key == target_key:
                return True
            for successor in self._collect_block_successors(current):
                stack.append(successor)
        return False

    def _pick_body_and_exit_blocks(self, header_block) -> Optional[Tuple[object, object, bool]]:
        successors = self._collect_block_successors(header_block)
        if len(successors) != 2:
            return None

        reaches = [
            successor for successor in successors
            if self._can_reach_block(successor, header_block)
        ]
        if len(reaches) != 1:
            return None

        body_block = reaches[0]
        exit_block = successors[0] if successors[1] is body_block else successors[1]
        true_out = getattr(header_block, "getTrueOut", lambda: None)()
        body_on_true = true_out is not None and self._block_key(true_out) == self._block_key(body_block)
        return body_block, exit_block, body_on_true

    def _induction_backedge_indices(
        self,
        induction: CountedLoopInduction,
    ) -> Tuple[int, ...]:
        indices = tuple(int(index) for index in getattr(induction, "backedge_indices", ()) or ())
        if indices:
            return indices
        return (int(getattr(induction, "backedge_index", 0)),)

    def _induction_init_index(
        self,
        induction: CountedLoopInduction,
    ) -> int:
        indices = self._induction_backedge_indices(induction)
        init_index = getattr(induction, "init_index", None)
        if isinstance(init_index, int):
            return init_index
        if len(indices) == 1:
            return 1 - indices[0]
        return 0

    def _accumulator_backedge_indices(
        self,
        accumulator: CountedLoopAccumulator,
    ) -> Tuple[int, ...]:
        indices = tuple(int(index) for index in getattr(accumulator, "backedge_indices", ()) or ())
        if indices:
            return indices
        return (int(getattr(accumulator, "backedge_index", 0)),)

    def _accumulator_init_index(
        self,
        accumulator: CountedLoopAccumulator,
        induction: CountedLoopInduction,
    ) -> int:
        init_index = getattr(accumulator, "init_index", None)
        if isinstance(init_index, int):
            return init_index
        return self._induction_init_index(induction)

    def _match_counted_loop_induction(
        self,
        phi_op,
    ) -> Optional[CountedLoopInduction]:
        input_count = int(getattr(phi_op, "getNumInputs", lambda: 0)() or 0)
        if input_count < 2:
            return None
        phi_output = getattr(phi_op, "getOutput", lambda: None)()
        if phi_output is None:
            return None

        placeholder = Expression.parameter("__loop_iv", index=-10_000, size=getattr(phi_output, "getSize", lambda: 4)() or 4)
        step_candidates = []
        for backedge_index in range(input_count):
            step = self._extract_index_step(phi_op.getInput(backedge_index), phi_output)
            if step in {None, 0}:
                continue
            step_candidates.append((backedge_index, int(step)))
        if not step_candidates:
            return None

        step_values = {step for _index, step in step_candidates}
        if len(step_values) != 1:
            return None
        init_indices = [index for index in range(input_count) if index not in {candidate for candidate, _step in step_candidates}]
        if len(init_indices) != 1:
            return None

        init_index = init_indices[0]
        step_value = step_candidates[0][1]
        init_expr = self._build_pcode_expression(
            phi_op.getInput(init_index),
            placeholders={phi_output: placeholder},
        )
        if init_expr is None or self._expression_is_unresolved(init_expr):
            return None
        return CountedLoopInduction(
            phi_op=phi_op,
            phi_output=phi_output,
            init_expr=init_expr,
            backedge_index=step_candidates[0][0],
            step=step_value,
            placeholder=placeholder,
            signed_guard=False,
            init_index=init_index,
            backedge_indices=tuple(index for index, _step in step_candidates),
        )
        return None

    def _match_counted_loop_guard(
        self,
        header_block,
        cbranch_op,
        induction: CountedLoopInduction,
    ) -> Optional[CountedLoopGuard]:
        block_info = self._pick_body_and_exit_blocks(header_block)
        if block_info is None:
            return None
        body_block, exit_block, body_on_true = block_info
        if int(getattr(cbranch_op, "getNumInputs", lambda: 0)() or 0) < 2:
            return None

        raw_expr = self._build_pcode_expression(
            cbranch_op.getInput(1),
            placeholders={induction.phi_output: induction.placeholder},
        )
        if raw_expr is None or self._expression_is_unresolved(raw_expr):
            return None

        normalized = self._normalize_loop_continue_guard(
            raw_expr,
            induction.placeholder,
            body_on_true,
            induction.step,
        )
        if normalized is not None:
            condition_expr, bound_expr, signed_comparison = normalized
            return CountedLoopGuard(
                condition_expr=condition_expr,
                bound_expr=bound_expr,
                continue_on_true=body_on_true,
                body_block=body_block,
                exit_block=exit_block,
                signed_comparison=signed_comparison,
                entry_condition_expr=condition_expr,
            )
        return None

    def _match_latch_counted_loop_guard(
        self,
        header_block,
        induction: CountedLoopInduction,
    ) -> Optional[CountedLoopGuard]:
        backedge_indices = self._induction_backedge_indices(induction)
        if not backedge_indices:
            return None
        backedge_varnode = induction.phi_op.getInput(backedge_indices[0])
        backedge_def = getattr(backedge_varnode, "getDef", lambda: None)()
        if backedge_def is None:
            return None
        latch_block = getattr(backedge_def, "getParent", lambda: None)()
        if latch_block is None:
            return None
        cbranch_op = self._find_cbranch_op(latch_block)
        if cbranch_op is None or int(getattr(cbranch_op, "getNumInputs", lambda: 0)() or 0) < 2:
            return None

        successors = self._collect_block_successors(latch_block)
        if len(successors) != 2:
            return None
        header_key = self._block_key(header_block)
        backedge_target = next(
            (successor for successor in successors if self._block_key(successor) == header_key),
            None,
        )
        if backedge_target is None:
            return None
        exit_block = successors[0] if successors[1] is backedge_target else successors[1]
        true_out = getattr(latch_block, "getTrueOut", lambda: None)()
        continue_on_true = true_out is not None and self._block_key(true_out) == header_key

        raw_expr = self._build_pcode_expression(
            cbranch_op.getInput(1),
            placeholders={induction.phi_output: induction.placeholder},
        )
        if raw_expr is None or self._expression_is_unresolved(raw_expr):
            return None
        normalized = self._normalize_latch_continue_guard(
            raw_expr,
            induction.placeholder,
            continue_on_true,
            induction.step,
        )
        if normalized is None:
            return None
        condition_expr, entry_condition_expr, bound_expr, signed_comparison = normalized
        return CountedLoopGuard(
            condition_expr=condition_expr,
            bound_expr=bound_expr,
            continue_on_true=continue_on_true,
            body_block=header_block,
            exit_block=exit_block,
            signed_comparison=signed_comparison,
            entry_condition_expr=entry_condition_expr,
            latch_block=latch_block,
        )

    def _match_counted_loop_accumulators(
        self,
        phi_ops: Sequence,
        induction: CountedLoopInduction,
        body_block,
    ) -> List[CountedLoopAccumulator]:
        induction_input_count = int(getattr(induction.phi_op, "getNumInputs", lambda: 0)() or 0)
        induction_init_index = self._induction_init_index(induction)
        induction_backedge_indices = self._induction_backedge_indices(induction)
        candidate_ops = [
            phi_op for phi_op in phi_ops
            if phi_op is not induction.phi_op
            and int(getattr(phi_op, "getNumInputs", lambda: 0)() or 0) == induction_input_count
            and getattr(phi_op, "getOutput", lambda: None)() is not None
        ]

        candidates: List[CountedLoopAccumulator] = []
        for phi_op in candidate_ops:
            phi_output = getattr(phi_op, "getOutput", lambda: None)()
            init_index = induction_init_index
            try:
                init_expr = self._trace_varnode_expression(phi_op.getInput(init_index))
                if init_expr is None or self._expression_is_unresolved(init_expr):
                    init_expr = self._build_pcode_expression(phi_op.getInput(init_index), placeholders={})
            except RecursionError:
                continue
            if init_expr is None or self._expression_is_unresolved(init_expr):
                continue
            placeholder = Expression.variable("__loop_acc", size=getattr(phi_output, "getSize", lambda: 4)() or 4)
            accumulator = CountedLoopAccumulator(
                phi_op=phi_op,
                phi_output=phi_output,
                init_expr=init_expr,
                backedge_index=induction.backedge_index,
                placeholder=placeholder,
                member_outputs=(phi_output,),
                member_placeholders=(placeholder,),
                init_index=init_index,
                backedge_indices=induction_backedge_indices,
            )
            all_backedges_resolved = True
            for backedge_index in self._accumulator_backedge_indices(accumulator):
                backedge_varnode = phi_op.getInput(backedge_index)
                backedge_def = getattr(backedge_varnode, "getDef", lambda: None)()
                parent_block = getattr(backedge_def, "getParent", lambda: None)() if backedge_def is not None else None
                if body_block is not None and parent_block is not None:
                    if not self._can_reach_block(body_block, parent_block):
                        all_backedges_resolved = False
                        break
                try:
                    resolved_backedge = self._build_pcode_expression(
                        backedge_varnode,
                        placeholders={
                            induction.phi_output: induction.placeholder,
                            accumulator.phi_output: accumulator.placeholder,
                        },
                    )
                except RecursionError:
                    all_backedges_resolved = False
                    break
                if resolved_backedge is None or self._expression_is_unresolved(resolved_backedge):
                    all_backedges_resolved = False
                    break
            if all_backedges_resolved:
                candidates.append(accumulator)
        candidates.sort(
            key=lambda candidate: self._counted_loop_accumulator_priority(candidate),
            reverse=True,
        )
        return candidates

    def _counted_loop_accumulator_priority(
        self,
        accumulator: CountedLoopAccumulator,
    ) -> Tuple[int, int, int]:
        phi_output = accumulator.phi_output
        output_size = int(getattr(phi_output, "getSize", lambda: 0)() or getattr(accumulator.placeholder, "size", 0) or 0)
        init_const = 1 if self._raw_constant_value(accumulator.init_expr) is not None else 0
        return (
            1 if self._varnode_reaches_return(phi_output) else 0,
            output_size,
            init_const,
        )

    def _counted_loop_model_priority(
        self,
        accumulator: CountedLoopAccumulator,
        residue_cases: Sequence[ResidueLoopCase],
    ) -> Tuple[int, int, int, int, int]:
        max_coeff = 0
        max_bias = 0
        for case in residue_cases or ():
            max_coeff = max(max_coeff, abs(int(case.affine[0])))
            max_bias = max(max_bias, abs(int(case.affine[1])))
        target_varnode = accumulator.phi_output or accumulator.update_varnode
        member_count = len(accumulator.member_outputs) or (1 if target_varnode is not None else 0)
        return (
            1 if self._varnode_reaches_return(target_varnode) else 0,
            1 if max_coeff != 0 else 0,
            max_coeff,
            member_count,
            max_bias,
        )

    def _extract_counted_loop_update_cases(
        self,
        accumulator: CountedLoopAccumulator,
        induction: CountedLoopInduction,
        guard: CountedLoopGuard,
    ) -> List[CountedLoopUpdateCase]:
        header_block = getattr(induction.phi_op, "getParent", lambda: None)()
        placeholders = {
            induction.phi_output: induction.placeholder,
        }
        for output, replacement in zip(accumulator.member_outputs, accumulator.member_placeholders):
            placeholders[output] = replacement
        if not accumulator.member_outputs and accumulator.phi_output is not None:
            placeholders[accumulator.phi_output] = accumulator.placeholder
        placeholders.update(
            self._collect_affine_loop_state_placeholders(
                header_block=header_block,
                induction=induction,
                accumulator=accumulator,
            )
        )

        raw_cases: List[Tuple[List[Condition], Expression]] = []
        if accumulator.update_varnode is not None:
            expr = self._build_pcode_expression(accumulator.update_varnode, placeholders=placeholders)
            if expr is None or self._expression_is_unresolved(expr):
                return []
            target_block = accumulator.update_block or guard.latch_block or guard.body_block
            for conditions in self._enumerate_paths_with_conditions(
                start_block=guard.body_block,
                target_block=target_block,
                header_block=header_block,
                placeholders=placeholders,
                stop_block=guard.exit_block,
                ):
                    raw_cases.append((conditions, expr))
        else:
            if accumulator.phi_op is None:
                return []
            parent_block = getattr(accumulator.phi_op, "getParent", lambda: None)()
            in_size = int(getattr(parent_block, "getInSize", lambda: 0)() or 0) if parent_block is not None else 0
            for backedge_index in self._accumulator_backedge_indices(accumulator):
                backedge_varnode = accumulator.phi_op.getInput(backedge_index)
                def_op = getattr(backedge_varnode, "getDef", lambda: None)()
                if def_op is not None and getattr(def_op, "getMnemonic", lambda: None)() == "MULTIEQUAL":
                    def_parent = getattr(def_op, "getParent", lambda: None)()
                    def_in_size = int(getattr(def_parent, "getInSize", lambda: 0)() or 0) if def_parent is not None else 0
                    input_count = int(getattr(def_op, "getNumInputs", lambda: 0)() or 0)
                    for index in range(input_count):
                        expr = self._build_pcode_expression(def_op.getInput(index), placeholders=placeholders)
                        if expr is None or self._expression_is_unresolved(expr):
                            continue
                        target_block = None
                        if def_parent is not None and index < def_in_size:
                            target_block = def_parent.getIn(index)
                        if target_block is None:
                            target_block = def_parent or guard.body_block
                        for conditions in self._enumerate_paths_with_conditions(
                            start_block=guard.body_block,
                            target_block=target_block,
                            header_block=header_block,
                            placeholders=placeholders,
                            stop_block=guard.exit_block,
                        ):
                            raw_cases.append((conditions, expr))
                    continue
                expr = self._build_pcode_expression(backedge_varnode, placeholders=placeholders)
                if expr is None or self._expression_is_unresolved(expr):
                    continue
                target_block = None
                if parent_block is not None and backedge_index < in_size:
                    target_block = parent_block.getIn(backedge_index)
                if target_block is None:
                    target_block = getattr(def_op, "getParent", lambda: None)() if def_op is not None else guard.body_block
                for conditions in self._enumerate_paths_with_conditions(
                    start_block=guard.body_block,
                    target_block=target_block,
                    header_block=header_block,
                    placeholders=placeholders,
                    stop_block=guard.exit_block,
                ):
                    raw_cases.append((conditions, expr))
            if not raw_cases:
                return []

        cases: List[CountedLoopUpdateCase] = []
        seen = set()
        for conditions, update_expr in raw_cases:
            simplified = ConditionSimplifier.simplify_conditions_object_centric(list(conditions or []))
            if ConditionSimplifier.object_centric_is_contradiction(simplified):
                continue
            reduced_update = _reduce_expression_under_conditions(update_expr, simplified) or update_expr
            delta_expr = self._extract_additive_delta(reduced_update, accumulator.placeholder, list(simplified))
            if delta_expr is None:
                continue
            key = (
                _runtime_conditions_signature(simplified),
                _runtime_expression_signature(delta_expr),
            )
            if key in seen:
                continue
            seen.add(key)
            cases.append(
                CountedLoopUpdateCase(
                    conditions=tuple(simplified),
                    update_expr=reduced_update,
                    delta_expr=delta_expr,
                )
            )
        return cases

    def _try_extract_counted_loop_update_cases_for_summary(
        self,
        accumulator: CountedLoopAccumulator,
        induction: CountedLoopInduction,
        guard: CountedLoopGuard,
    ) -> Tuple[CountedLoopUpdateCase, ...]:
        try:
            return tuple(self._extract_counted_loop_update_cases(accumulator, induction, guard))
        except (AttributeError, TypeError, IndexError, RecursionError):
            return ()

    def _build_counted_loop_case_refs(
        self,
        cases: Sequence[CountedLoopUpdateCase],
    ) -> Tuple[LoopCaseRef, ...]:
        refs: List[LoopCaseRef] = []
        for case in cases or ():
            body_effect = LoopBodyEffectRef(
                kind="accumulator_update",
                source="pcode_summary",
                scope="loop",
                guard_constraints=tuple(case.conditions or ()),
                value_expr=case.update_expr,
            )
            refs.append(
                LoopCaseRef(
                    path_conditions=tuple(case.conditions or ()),
                    body_effect=body_effect,
                    term_expr=case.delta_expr,
                    case_kind="accumulator_delta",
                    source="counted_loop_update_case",
                )
            )
        return tuple(refs)

    def _collect_affine_loop_state_placeholders(
        self,
        *,
        header_block,
        induction: CountedLoopInduction,
        accumulator: CountedLoopAccumulator,
    ) -> Dict[object, Expression]:
        placeholders: Dict[object, Expression] = {}
        if header_block is None:
            return placeholders
        member_output_keys = {
            self._varnode_cache_key(output)
            for output in accumulator.member_outputs
            if output is not None
        }
        for op in self._iter_block_ops(header_block):
            if getattr(op, "getMnemonic", lambda: None)() != "MULTIEQUAL":
                continue
            if op is induction.phi_op or op is accumulator.phi_op:
                continue
            output = getattr(op, "getOutput", lambda: None)()
            if output is not None and self._varnode_cache_key(output) in member_output_keys:
                continue
            expr = self._summarize_affine_loop_state_phi(op, induction)
            if expr is None:
                continue
            if output is None:
                continue
            placeholders[output] = expr
        return placeholders

    def _summarize_affine_loop_state_phi(
        self,
        phi_op,
        induction: CountedLoopInduction,
    ) -> Optional[Expression]:
        if phi_op is None or induction is None:
            return None
        if int(getattr(phi_op, "getNumInputs", lambda: 0)() or 0) != 2:
            return None
        phi_output = getattr(phi_op, "getOutput", lambda: None)()
        if phi_output is None:
            return None

        backedge_index = None
        delta = None
        for candidate_index in range(2):
            candidate_delta = self._extract_index_step(phi_op.getInput(candidate_index), phi_output)
            if candidate_delta is None:
                continue
            backedge_index = candidate_index
            delta = candidate_delta
            break
        if backedge_index is None or delta is None:
            return None

        init_expr = self._build_pcode_expression(
            phi_op.getInput(1 - backedge_index),
            placeholders={
                induction.phi_output: induction.placeholder,
                induction.phi_op.getInput(self._induction_init_index(induction)): induction.placeholder,
            },
        )
        if init_expr is None or self._expression_is_unresolved(init_expr):
            return None

        size = getattr(phi_output, "getSize", lambda: 0)() or induction.placeholder.size or init_expr.size or 4
        counter_name = induction.placeholder.name or "__loop_iv"
        init_affine = self._extract_affine_term(init_expr, counter_name)
        induction_step = int(induction.step or 0)
        if induction_step == 0 or delta % induction_step != 0:
            return None
        ratio = delta // induction_step
        if init_affine is not None and init_affine[0] == ratio:
            linear_term = self._scale_term(induction.placeholder, ratio, size)
            if linear_term is None:
                return None
            if init_affine[1] == 0:
                linear_term.size = size
                return linear_term
            bias_expr = Expression.constant(init_affine[1], size)
            expr = Expression.binary_op("INT_ADD", linear_term, bias_expr)
            expr.size = size
            return expr

        current_offset = Expression.binary_op("INT_SUB", induction.placeholder, induction.init_expr)
        current_offset.size = size
        if ratio == 0:
            expr = init_expr
        elif ratio == 1:
            expr = Expression.binary_op("INT_ADD", init_expr, current_offset)
            expr.size = size
        elif ratio == -1:
            expr = Expression.binary_op("INT_SUB", init_expr, current_offset)
            expr.size = size
        else:
            scale = Expression.constant(abs(ratio), size)
            scaled_offset = Expression.binary_op("INT_MULT", current_offset, scale)
            scaled_offset.size = size
            operator = "INT_ADD" if ratio > 0 else "INT_SUB"
            expr = Expression.binary_op(operator, init_expr, scaled_offset)
            expr.size = size
        expr.size = size
        return expr

    def _enumerate_paths_with_conditions(
        self,
        *,
        start_block,
        target_block,
        header_block,
        placeholders: Dict[object, Expression],
        stop_block=None,
        limit: int = 8,
    ) -> List[List[Condition]]:
        paths, _incomplete = self._enumerate_paths_with_conditions_result(
            start_block=start_block,
            target_block=target_block,
            header_block=header_block,
            placeholders=placeholders,
            stop_block=stop_block,
            limit=limit,
        )
        return paths

    def _enumerate_paths_with_conditions_result(
        self,
        *,
        start_block,
        target_block,
        header_block,
        placeholders: Dict[object, Expression],
        stop_block=None,
        limit: int = 8,
    ) -> Tuple[List[List[Condition]], bool]:
        if start_block is None or target_block is None:
            return [[]], False
        target_key = self._block_key(target_block)
        header_key = self._block_key(header_block)
        stop_key = self._block_key(stop_block)
        paths: List[List[Condition]] = []
        incomplete = False

        def dfs(current, active_conditions: List[Condition], visited: set) -> None:
            nonlocal incomplete
            if len(paths) >= limit:
                incomplete = True
                return
            current_key = self._block_key(current)
            if current_key == target_key:
                paths.append(list(active_conditions))
                return
            if current_key == stop_key:
                return
            visited = set(visited)
            visited.add(current_key)
            for successor in self._collect_block_successors(current):
                successor_key = self._block_key(successor)
                if successor_key in visited or successor_key == header_key:
                    continue
                branch_condition = self._build_block_edge_condition(
                    current,
                    successor,
                    placeholders=placeholders,
                )
                next_conditions = list(active_conditions)
                if branch_condition is not None:
                    next_conditions.append(branch_condition)
                dfs(successor, next_conditions, visited)

        dfs(start_block, [], set())
        return paths, incomplete

    def _build_block_edge_condition(
        self,
        block,
        successor,
        *,
        placeholders: Dict[object, Expression],
    ) -> Optional[Condition]:
        cbranch = self._find_cbranch_op(block)
        if cbranch is None or int(getattr(cbranch, "getNumInputs", lambda: 0)() or 0) < 2:
            return None
        expr = self._build_pcode_expression(cbranch.getInput(1), placeholders=placeholders)
        if expr is None or self._expression_is_unresolved(expr):
            return None

        true_out = getattr(block, "getTrueOut", lambda: None)()
        false_out = getattr(block, "getFalseOut", lambda: None)()
        successor_key = self._block_key(successor)
        if true_out is not None and self._block_key(true_out) == successor_key:
            return Condition(expr, False)
        if false_out is not None and self._block_key(false_out) == successor_key:
            return Condition(expr, True)
        return None

    def _build_pcode_expression(
        self,
        varnode,
        *,
        placeholders: Dict[object, Expression],
        _seen=None,
        _memo=None,
    ) -> Optional[Expression]:
        if varnode is None:
            return None
        if _memo is None:
            _memo = {}

        placeholder_keys = tuple(sorted(id(candidate) for candidate in placeholders))
        memo_key = (self._varnode_cache_key(varnode), placeholder_keys)
        cached = _memo.get(memo_key)
        if cached is not None:
            if cached is False:
                return None
            return cached
        _memo[memo_key] = False

        for candidate, replacement in placeholders.items():
            if self._same_placeholder_varnode(varnode, candidate):
                _memo[memo_key] = replacement
                return replacement

        current = self._follow_passthrough_varnode(varnode)
        current_memo_key = memo_key
        if current is not varnode:
            current_memo_key = (self._varnode_cache_key(current), placeholder_keys)
            cached = _memo.get(current_memo_key)
            if cached is not None:
                if cached is False:
                    return None
                _memo[memo_key] = cached
                return cached
            _memo[current_memo_key] = False
        for candidate, replacement in placeholders.items():
            if self._same_placeholder_varnode(current, candidate):
                _memo[memo_key] = replacement
                _memo[current_memo_key] = replacement
                return replacement

        if _seen is None:
            _seen = set()
        current_id = id(current)
        if current_id in _seen:
            return None
        _seen = set(_seen)
        _seen.add(current_id)

        def_op = getattr(current, "getDef", lambda: None)()
        if def_op is None:
            traced = self._trace_varnode_expression(current)
            if traced is None or self._expression_is_unresolved(traced):
                return None
            _memo[memo_key] = traced
            _memo[current_memo_key] = traced
            return traced

        mnemonic = getattr(def_op, "getMnemonic", lambda: None)()
        output = getattr(def_op, "getOutput", lambda: None)()
        output_size = max(1, int(getattr(output, "getSize", lambda: 0)() or getattr(current, "getSize", lambda: 0)() or 1))

        if mnemonic == "MULTIEQUAL":
            parent_block = getattr(def_op, "getParent", lambda: None)()
            input_count = int(getattr(def_op, "getNumInputs", lambda: 0)() or 0)
            branches = []
            for index in range(input_count):
                value = self._build_pcode_expression(
                    def_op.getInput(index),
                    placeholders=placeholders,
                    _seen=_seen,
                    _memo=_memo,
                )
                if value is None:
                    continue
                condition = None
                if parent_block is not None and index < int(getattr(parent_block, "getInSize", lambda: 0)() or 0):
                    predecessor = parent_block.getIn(index)
                    condition = self._build_block_edge_condition(
                        predecessor,
                        parent_block,
                        placeholders=placeholders,
                    )
                branches.append((condition, value))
            if not branches:
                return None
            if len(branches) == 1 and branches[0][0] is None:
                result = branches[0][1]
                _memo[memo_key] = result
                _memo[current_memo_key] = result
                return result
            phi = Expression.phi(branches)
            phi.size = output_size
            _memo[memo_key] = phi
            _memo[current_memo_key] = phi
            return phi

        if mnemonic in {"COPY", "CAST", "INT_ZEXT", "INT_SEXT", "SUBPIECE"}:
            expr = self._build_pcode_expression(
                def_op.getInput(0),
                placeholders=placeholders,
                _seen=_seen,
                _memo=_memo,
            )
            if expr is None:
                return None
            if mnemonic in {"COPY", "CAST"}:
                expr.size = output_size
                _memo[memo_key] = expr
                _memo[current_memo_key] = expr
                return expr
            if mnemonic in {"INT_ZEXT", "INT_SEXT"}:
                widened = Expression.unary_op(mnemonic, expr)
                widened.size = output_size
                _memo[memo_key] = widened
                _memo[current_memo_key] = widened
                return widened
            if mnemonic == "SUBPIECE":
                if int(getattr(def_op, "getNumInputs", lambda: 0)() or 0) < 2:
                    return None
                offset_expr = self._build_pcode_expression(
                    def_op.getInput(1),
                    placeholders=placeholders,
                    _seen=_seen,
                    _memo=_memo,
                )
                if offset_expr is None:
                    return None
                subpiece = Expression.binary_op("SUBPIECE", expr, offset_expr)
                subpiece.size = output_size
                _memo[memo_key] = subpiece
                _memo[current_memo_key] = subpiece
                return subpiece

        if mnemonic in {"INT_NEGATE", "INT_2COMP", "BOOL_NEGATE"}:
            if int(getattr(def_op, "getNumInputs", lambda: 0)() or 0) != 1:
                return None
            operand = self._build_pcode_expression(
                def_op.getInput(0),
                placeholders=placeholders,
                _seen=_seen,
                _memo=_memo,
            )
            if operand is None:
                return None
            unary = Expression.unary_op(mnemonic, operand)
            unary.size = output_size
            _memo[memo_key] = unary
            _memo[current_memo_key] = unary
            return unary

        if mnemonic in {
            "INT_ADD",
            "INT_SUB",
            "INT_MULT",
            "INT_AND",
            "INT_OR",
            "INT_XOR",
            "PIECE",
            "INT_LEFT",
            "INT_RIGHT",
            "INT_SRIGHT",
            "INT_EQUAL",
            "INT_NOTEQUAL",
            "INT_LESS",
            "INT_LESSEQUAL",
            "INT_SLESS",
            "INT_SLESSEQUAL",
            "BOOL_AND",
            "BOOL_OR",
            "BOOL_XOR",
        }:
            if int(getattr(def_op, "getNumInputs", lambda: 0)() or 0) != 2:
                return None
            left = self._build_pcode_expression(
                def_op.getInput(0),
                placeholders=placeholders,
                _seen=_seen,
                _memo=_memo,
            )
            right = self._build_pcode_expression(
                def_op.getInput(1),
                placeholders=placeholders,
                _seen=_seen,
                _memo=_memo,
            )
            if left is None or right is None:
                return None
            expr = Expression.binary_op(mnemonic, left, right)
            expr.size = output_size
            _memo[memo_key] = expr
            _memo[current_memo_key] = expr
            return expr

        return None

    def _normalize_loop_continue_guard(
        self,
        raw_expr: Expression,
        counter_placeholder: Expression,
        body_on_true: bool,
        step: int,
    ) -> Optional[Tuple[Expression, Expression, bool]]:
        counter_name = counter_placeholder.name or "__loop_iv"
        parsed = self._parse_counter_comparison(raw_expr, counter_name)
        if parsed is None:
            return None
        relation, other_expr, signed = parsed
        if not self._is_counted_loop_bound_expr(other_expr):
            return None
        if not body_on_true:
            relation = {
                "<": ">=",
                "<=": ">",
                ">": "<=",
                ">=": "<",
            }.get(relation)
        if step > 0:
            if relation == "<=":
                other_expr = self._adjust_loop_bound_for_strict_relation(other_expr, +1)
                relation = "<"
            if relation != "<":
                return None
            operator = "INT_SLESS" if signed else "INT_LESS"
            condition_expr = Expression.binary_op(operator, counter_placeholder, other_expr)
            condition_expr.size = 1
            return condition_expr, other_expr, signed

        if relation == ">=":
            other_expr = self._adjust_loop_bound_for_strict_relation(other_expr, -1)
            relation = ">"
        if relation != ">":
            return None
        operator = "INT_SLESS" if signed else "INT_LESS"
        condition_expr = Expression.binary_op(operator, other_expr, counter_placeholder)
        condition_expr.size = 1
        return condition_expr, other_expr, signed

    def _normalize_latch_continue_guard(
        self,
        raw_expr: Expression,
        counter_placeholder: Expression,
        continue_on_true: bool,
        step: int,
    ) -> Optional[Tuple[Expression, Expression, Expression, bool]]:
        counter_name = counter_placeholder.name or "__loop_iv"
        if raw_expr.expr_type != ExpressionType.BINARY_OP or len(raw_expr.operands) != 2:
            return None
        operator = raw_expr.operator
        left, right = raw_expr.operands

        counter_side = None
        bound_expr = None
        signed = operator.startswith("INT_S")
        affine_left = self._extract_affine_term(left, counter_name)
        affine_right = self._extract_affine_term(right, counter_name)
        if affine_left is not None and affine_left[0] == 1 and affine_right is None:
            counter_side = "left"
            bound_expr = right
            bias = affine_left[1]
        elif affine_right is not None and affine_right[0] == 1 and affine_left is None:
            counter_side = "right"
            bound_expr = left
            bias = affine_right[1]
        else:
            return None

        if bias != abs(step):
            return None
        if not self._is_counted_loop_bound_expr(bound_expr):
            return None

        continue_when_equal = operator == "INT_EQUAL"
        if raw_expr.operator not in {"INT_EQUAL", "INT_NOTEQUAL"}:
            return None
        keep_looping = continue_when_equal if continue_on_true else not continue_when_equal
        if keep_looping:
            return None

        compare_op = "INT_SLESS" if signed else "INT_LESS"
        if step > 0:
            condition_expr = Expression.binary_op(compare_op, counter_placeholder, bound_expr)
        else:
            condition_expr = Expression.binary_op(compare_op, bound_expr, counter_placeholder)
        condition_expr.size = 1
        entry_op = "INT_NOTEQUAL" if counter_side == "left" else "INT_NOTEQUAL"
        entry_condition_expr = Expression.binary_op(entry_op, counter_placeholder, bound_expr)
        entry_condition_expr.size = 1
        return condition_expr, entry_condition_expr, bound_expr, signed

    def _is_counted_loop_bound_expr(self, expr: Optional[Expression]) -> bool:
        if expr is None or self._expression_is_unresolved(expr):
            return False
        expr_size = int(getattr(expr, "size", 0) or 0)
        if expr_size == 1:
            return False
        if getattr(expr, "expr_type", None) == ExpressionType.BINARY_OP:
            if expr.operator in {
                "BOOL_AND",
                "BOOL_OR",
                "BOOL_XOR",
                "INT_EQUAL",
                "INT_NOTEQUAL",
                "INT_LESS",
                "INT_LESSEQUAL",
                "INT_SLESS",
                "INT_SLESSEQUAL",
            }:
                return False
        return True

    def _adjust_loop_bound_for_strict_relation(
        self,
        bound_expr: Expression,
        delta: int,
    ) -> Expression:
        if delta == 0:
            return bound_expr
        adjusted = Expression.binary_op(
            "INT_ADD" if delta > 0 else "INT_SUB",
            bound_expr,
            Expression.constant(abs(delta), size=bound_expr.size or 4),
        )
        adjusted.size = bound_expr.size
        return adjusted

    def _parse_counter_comparison(
        self,
        expr: Optional[Expression],
        counter_name: str,
    ) -> Optional[Tuple[str, Expression, bool]]:
        if expr is None or expr.expr_type != ExpressionType.BINARY_OP or len(expr.operands) != 2:
            return None
        operator = expr.operator
        if operator not in {"INT_SLESS", "INT_SLESSEQUAL", "INT_LESS", "INT_LESSEQUAL"}:
            return None
        signed = operator.startswith("INT_S")
        left, right = expr.operands
        left_is_counter = self._expr_matches_counter_placeholder(left, counter_name)
        right_is_counter = self._expr_matches_counter_placeholder(right, counter_name)
        if left_is_counter == right_is_counter:
            return None
        if left_is_counter:
            relation = "<" if operator in {"INT_SLESS", "INT_LESS"} else "<="
            return relation, right, signed
        relation = ">" if operator in {"INT_SLESS", "INT_LESS"} else ">="
        return relation, left, signed

    def _expr_matches_counter_placeholder(
        self,
        expr: Optional[Expression],
        counter_name: str,
    ) -> bool:
        normalized = self._normalize_counter_view(expr, counter_name)
        return bool(normalized is not None and getattr(normalized[0], "name", None) == counter_name)

    def _extract_residue_loop_cases(
        self,
        cases: Sequence[CountedLoopUpdateCase],
        counter_name: str,
    ) -> Optional[Tuple[ResidueLoopCase, ...]]:
        if not cases:
            return None
        if len(cases) == 1 and not cases[0].conditions:
            affine = self._extract_affine_term(cases[0].delta_expr, counter_name)
            if affine is None:
                return None
            return (ResidueLoopCase(modulus=1, residue=0, affine=affine),)

        residue_cases: List[ResidueLoopCase] = []
        modulus = None
        seen_residues = set()
        for case in cases:
            affine = self._extract_affine_term(case.delta_expr, counter_name)
            if affine is None:
                return None
            residue_info = self._extract_exact_residue_case(case.conditions, counter_name)
            if residue_info is None:
                return None
            case_modulus, residue = residue_info
            if modulus is None:
                modulus = case_modulus
            if modulus != case_modulus:
                return None
            if residue in seen_residues:
                return None
            seen_residues.add(residue)
            residue_cases.append(
                ResidueLoopCase(
                    modulus=case_modulus,
                    residue=residue,
                    affine=affine,
                )
            )
        if modulus is None or seen_residues != set(range(modulus)):
            return None
        return tuple(sorted(residue_cases, key=lambda item: item.residue))

    def _validate_counted_loop_update_cases(
        self,
        *,
        cases: Sequence[CountedLoopUpdateCase],
        residue_cases: Sequence[ResidueLoopCase],
        induction: CountedLoopInduction,
        accumulator: CountedLoopAccumulator,
    ) -> bool:
        """Require the affine recurrence to match the actual loop update.

        Residue extraction is intentionally syntactic: it classifies already
        extracted deltas.  Before accepting a closed form, prove with SMT that
        each source CFG update case is exactly the accumulator state plus the
        affine delta assigned to that residue.  This keeps direct summaries from
        becoming a shortcut around the real P-code update semantics.
        """
        if not cases or not residue_cases:
            return False

        counter_name = induction.placeholder.name or "__loop_iv"
        by_residue = {
            (int(case.modulus), int(case.residue)): case
            for case in residue_cases
        }
        if len(by_residue) != len(residue_cases):
            return False

        for case in cases:
            residue_info = self._extract_exact_residue_case(case.conditions, counter_name)
            if residue_info is None:
                if len(residue_cases) != 1:
                    return False
                only = residue_cases[0]
                if int(only.modulus) != 1 or int(only.residue) != 0:
                    return False
                residue_info = (1, 0)

            residue_case = by_residue.get((int(residue_info[0]), int(residue_info[1])))
            if residue_case is None:
                return False

            affine_delta = self._build_affine_delta_expression(
                induction.placeholder,
                residue_case.affine,
                max(
                    int(getattr(case.delta_expr, "size", 0) or 0),
                    int(getattr(case.update_expr, "size", 0) or 0),
                    int(getattr(accumulator.placeholder, "size", 0) or 0),
                    int(getattr(induction.placeholder, "size", 0) or 0),
                    4,
                ),
            )
            if affine_delta is None:
                return False

            parameters = self._collect_summary_parameter_specs(
                case.update_expr,
                case.delta_expr,
                affine_delta,
                accumulator.placeholder,
                induction.placeholder,
                *(condition.expression for condition in case.conditions or [] if condition is not None),
            )
            if not self._prove_expression_equivalence_under_conditions(
                case.delta_expr,
                affine_delta,
                case.conditions,
                parameters,
            ):
                self._debug("Declined counted scalar loop summary: extracted delta does not match residue affine case")
                return False

            expected_update = self._sum_expression_terms([accumulator.placeholder, affine_delta])
            if expected_update is None:
                return False
            expected_update.size = max(
                int(getattr(expected_update, "size", 0) or 0),
                int(getattr(case.update_expr, "size", 0) or 0),
                int(getattr(accumulator.placeholder, "size", 0) or 0),
            )
            if not self._prove_expression_equivalence_under_conditions(
                case.update_expr,
                expected_update,
                case.conditions,
                parameters,
            ):
                self._debug("Declined counted scalar loop summary: update expression is not accumulator plus affine delta")
                return False

        return True

    def _build_affine_delta_expression(
        self,
        counter_expr: Expression,
        affine: Tuple[int, int],
        size: int,
    ) -> Optional[Expression]:
        coeff, bias = int(affine[0]), int(affine[1])
        terms: List[Expression] = []
        counter = self._copy_symbol_expression(counter_expr, max(1, size))
        coeff_term = self._scale_expression(counter, coeff)
        if coeff_term is not None:
            coeff_term.size = max(1, size)
            terms.append(coeff_term)
        if bias != 0:
            terms.append(Expression.constant(bias, max(1, size)))
        if not terms:
            return Expression.constant(0, max(1, size))
        result = self._sum_expression_terms(terms)
        if result is not None:
            result.size = max(1, size)
        return result

    def _copy_symbol_expression(self, expr: Expression, size: int) -> Expression:
        if getattr(expr, "expr_type", None) == ExpressionType.PARAMETER:
            return Expression.parameter(
                getattr(expr, "name", None) or "param",
                index=int(getattr(expr, "value", -1) or -1),
                data_type=getattr(expr, "data_type", None),
                data_type_obj=getattr(expr, "data_type_obj", None),
                size=max(1, int(size or getattr(expr, "size", 0) or 4)),
                storage_info=getattr(expr, "storage_info", None),
                runtime_ref=getattr(expr, "runtime_ref", None),
            )
        if getattr(expr, "expr_type", None) == ExpressionType.VARIABLE:
            return Expression.variable(
                getattr(expr, "name", None) or "var",
                data_type=getattr(expr, "data_type", None),
                data_type_obj=getattr(expr, "data_type_obj", None),
                size=max(1, int(size or getattr(expr, "size", 0) or 4)),
                storage_info=getattr(expr, "storage_info", None),
                runtime_ref=getattr(expr, "runtime_ref", None),
            )
        return expr

    def _extract_exact_residue_case(
        self,
        conditions: Sequence[Condition],
        counter_name: str,
    ) -> Optional[Tuple[int, int]]:
        residue_cases = []
        for condition in conditions or []:
            residue = self._condition_to_exact_residue(condition, counter_name)
            if residue is not None:
                residue_cases.append(residue)
                continue
            if self._condition_mentions_counter(condition, counter_name):
                return None
        if not residue_cases:
            return None
        first = residue_cases[0]
        if any(item != first for item in residue_cases[1:]):
            return None
        return first

    def _condition_to_exact_residue(
        self,
        condition: Condition,
        counter_name: str,
    ) -> Optional[Tuple[int, int]]:
        expr = getattr(condition, "expression", None)
        if expr is None or expr.expr_type != ExpressionType.BINARY_OP or len(expr.operands) != 2:
            return None
        if expr.operator not in {"INT_EQUAL", "INT_NOTEQUAL"}:
            return None

        is_equal = expr.operator == "INT_EQUAL"
        if condition.negated:
            is_equal = not is_equal

        bitand = None
        residue_value = None
        if self._raw_constant_value(expr.operands[0]) is not None:
            bitand = expr.operands[1]
            residue_value = self._raw_constant_value(expr.operands[0])
        elif self._raw_constant_value(expr.operands[1]) is not None:
            bitand = expr.operands[0]
            residue_value = self._raw_constant_value(expr.operands[1])
        if bitand is None or residue_value is None:
            return None
        if bitand.expr_type != ExpressionType.BINARY_OP or bitand.operator != "INT_AND" or len(bitand.operands) != 2:
            return None

        counter_expr = None
        mask_value = None
        if self._raw_constant_value(bitand.operands[0]) is not None and self._expr_matches_counter_placeholder(bitand.operands[1], counter_name):
            mask_value = self._raw_constant_value(bitand.operands[0])
            counter_expr = bitand.operands[1]
        elif self._raw_constant_value(bitand.operands[1]) is not None and self._expr_matches_counter_placeholder(bitand.operands[0], counter_name):
            mask_value = self._raw_constant_value(bitand.operands[1])
            counter_expr = bitand.operands[0]
        if counter_expr is None or mask_value is None:
            return None
        if mask_value <= 0 or (mask_value & (mask_value + 1)) != 0:
            return None

        modulus = int(mask_value) + 1
        residue = int(residue_value) & int(mask_value)
        if is_equal:
            return modulus, residue
        if modulus == 2:
            return modulus, residue ^ 1
        return None

    def _condition_mentions_counter(
        self,
        condition: Condition,
        counter_name: str,
    ) -> bool:
        expr = getattr(condition, "expression", None)
        if expr is None:
            return False
        return any(
            self._expr_matches_counter_placeholder(node, counter_name)
            for node in self._iter_expression_nodes(expr)
        )

    def _expression_is_unresolved(self, expr: Optional[Expression]) -> bool:
        if expr is None:
            return True
        if expr.expr_type in {ExpressionType.UNKNOWN, ExpressionType.CALL}:
            return True
        if expr.expr_type == ExpressionType.PHI and expr.value:
            for cond, value in expr.value:
                if cond is not None and self._expression_is_unresolved(cond.expression):
                    return True
                if self._expression_is_unresolved(value):
                    return True
            return False
        return any(self._expression_is_unresolved(operand) for operand in getattr(expr, "operands", []) or [])

    def _safe_expr_text(self, expr: Optional[Expression]) -> str:
        signature = _runtime_expression_signature(expr)
        return repr(signature)

    def _substitute_exact_expression(
        self,
        expr: Optional[Expression],
        needle: Expression,
        replacement: Expression,
    ) -> Optional[Expression]:
        if expr is None:
            return None
        if expr.structural_key() == needle.structural_key():
            return replacement

        if expr.expr_type == ExpressionType.BINARY_OP and len(expr.operands) == 2:
            left = self._substitute_exact_expression(expr.operands[0], needle, replacement)
            right = self._substitute_exact_expression(expr.operands[1], needle, replacement)
            if left is expr.operands[0] and right is expr.operands[1]:
                return expr
            rebuilt = Expression.binary_op(expr.operator, left, right)
            rebuilt.size = expr.size
            return rebuilt

        if expr.expr_type == ExpressionType.UNARY_OP and len(expr.operands) == 1:
            operand = self._substitute_exact_expression(expr.operands[0], needle, replacement)
            if operand is expr.operands[0]:
                return expr
            rebuilt = Expression.unary_op(expr.operator, operand)
            rebuilt.size = expr.size
            return rebuilt

        if expr.expr_type == ExpressionType.PHI and expr.value:
            branches = []
            changed = False
            for condition, value in expr.value:
                new_condition = condition
                if condition is not None:
                    condition_expr = self._substitute_exact_expression(
                        condition.expression,
                        needle,
                        replacement,
                    )
                    if condition_expr is not condition.expression:
                        new_condition = Condition(condition_expr, condition.negated)
                        changed = True
                new_value = self._substitute_exact_expression(value, needle, replacement)
                if new_value is not value:
                    changed = True
                branches.append((new_condition, new_value))
            if not changed:
                return expr
            rebuilt = Expression.phi(branches)
            rebuilt.size = expr.size
            return rebuilt

        if expr.expr_type in {ExpressionType.CALL, ExpressionType.INTRINSIC, ExpressionType.MEMORY} and expr.operands:
            new_operands = [
                self._substitute_exact_expression(operand, needle, replacement)
                for operand in expr.operands
            ]
            if all(new is old for new, old in zip(new_operands, expr.operands)):
                return expr
            if expr.expr_type == ExpressionType.CALL:
                rebuilt = Expression.call(expr.name or "call", new_operands)
            elif expr.expr_type == ExpressionType.INTRINSIC:
                rebuilt = Expression.intrinsic(
                    expr.name or "intrinsic",
                    new_operands,
                    size=expr.size,
                    runtime_ref=expr.runtime_ref,
                    opcode=expr.opcode,
                )
            else:
                rebuilt = Expression.memory(
                    new_operands[0],
                    size=expr.size,
                    read_order_key=expr.read_order_key,
                    runtime_ref=expr.runtime_ref,
                )
            rebuilt.size = expr.size
            return rebuilt

        return expr

    def _has_branch_accumulator_candidate(
        self,
        analysis,
    ) -> bool:
        if analysis is None or not analysis.returns or len(analysis.parameters or []) < 3:
            return False
        effect_summary = getattr(analysis, "effect_summary", None)
        if effect_summary is None or not getattr(effect_summary, "effects", None):
            return False
        if self._infer_loop_parameter_pair(analysis) is None:
            return False
        if not self._infer_pointer_parameter_name(analysis):
            return False
        return True

    def _debug(self, message: str) -> None:
        if self.debug:
            print(f"[RecurrenceSummary] {message}")

    def _try_summarize_linear_self_recursion(self, function, high_function, analysis) -> Optional[Tuple[List[ReturnInfo], str]]:
        function_name = function.getName()
        recursive_returns = [
            ret for ret in (analysis.returns or [])
            if self._expression_contains_recursive_unknown(ret.value, function_name)
        ]
        if len(recursive_returns) != 1:
            self._debug(
                f"Declined '{function_name}': expected exactly one recursive return, found {len(recursive_returns)}"
            )
            return None

        base_returns = [
            ret for ret in (analysis.returns or [])
            if ret not in recursive_returns and self._is_constant_expression(ret.value)
        ]
        if len(base_returns) != 1:
            self._debug(
                f"Declined '{function_name}': expected exactly one constant base return, found {len(base_returns)}"
            )
            return None

        param_info = dict(analysis.parameters[0])
        if not self._parameter_can_be_counter(param_info):
            self._debug(f"Declined '{function_name}': parameter is not a scalar counter candidate")
            return None

        param_expr = self._parameter_expression(param_info)
        param_name = param_expr.name
        if not param_name:
            self._debug(f"Declined '{function_name}': parameter name is unavailable")
            return None
        recursive_ret = recursive_returns[0]
        base_ret = base_returns[0]

        lower_bound = self._infer_lower_bound_from_conditions(recursive_ret.conditions, param_name)
        if lower_bound is None:
            lower_bound = self._infer_lower_bound_from_base_conditions(base_ret.conditions, param_name)
        if lower_bound is None:
            self._debug(f"Declined '{function_name}': could not infer recursion/base split bound")
            return None

        self_call_ops = [
            op for op in self._iter_pcode_ops(high_function)
            if op.getMnemonic() == "CALL"
            and op.getNumInputs() >= 2
            and self._is_direct_self_call(op, function_name)
        ]
        if len(self_call_ops) != 1:
            self._debug(
                f"Declined '{function_name}': expected exactly one direct self-call, found {len(self_call_ops)}"
            )
            return None

        call_arg_expr = self.tracer.trace_varnode(self_call_ops[0].getInput(1), use_cache=False)
        step = self._extract_unit_step_from_call_argument(call_arg_expr, param_name)
        if step != -1:
            self._debug(
                f"Declined '{function_name}': recursive call argument is not a unit decrement "
                f"({call_arg_expr.to_string()})"
            )
            return None

        addend_expr = self._extract_addend_expression(recursive_ret.value, function_name)
        if addend_expr is None:
            self._debug(
                f"Declined '{function_name}': could not isolate non-recursive addend from "
                f"{recursive_ret.value.to_string()}"
            )
            return None

        affine = self._extract_affine_term(addend_expr, param_name)
        if affine is None:
            self._debug(
                f"Declined '{function_name}': addend is not affine in the counter "
                f"({addend_expr.to_string()})"
            )
            return None
        coeff, bias = affine

        base_value = self._constant_value(base_ret.value)
        if base_value is None:
            self._debug(f"Declined '{function_name}': base value is not a concrete constant")
            return None

        recursive_value = self._build_closed_form(
            param_expr=param_expr,
            lower_bound=lower_bound,
            coeff=coeff,
            bias=bias,
            base_value=base_value,
        )
        if recursive_value is None:
            self._debug(f"Declined '{function_name}': failed to construct closed-form summary")
            return None

        recursive_conditions = self._build_recursive_conditions(param_expr, lower_bound)
        base_conditions = self._build_base_conditions(param_expr, lower_bound)
        if recursive_conditions is None or base_conditions is None:
            self._debug(f"Declined '{function_name}': failed to build guard conditions for summary")
            return None

        summarized_returns = [
            ReturnInfo(
                address=base_ret.address,
                value=Expression.constant(base_value, recursive_value.size or param_expr.size or 4),
                conditions=base_conditions,
                branch_index=base_ret.branch_index,
                pcode_identity=base_ret.pcode_identity,
                pcode_order=base_ret.pcode_order,
                pcode_time=base_ret.pcode_time,
            ),
            ReturnInfo(
                address=recursive_ret.address,
                value=recursive_value,
                conditions=recursive_conditions,
                branch_index=recursive_ret.branch_index,
                pcode_identity=recursive_ret.pcode_identity,
                pcode_order=recursive_ret.pcode_order,
                pcode_time=recursive_ret.pcode_time,
            ),
        ]

        self._debug(
            f"Recovered linear self-recursive summary for '{function_name}' "
            f"(lower_bound={lower_bound}, coeff={coeff}, bias={bias}, base={base_value})"
        )
        return summarized_returns, "linear_self_recursion_summary"

    def _try_summarize_readonly_pointer_reduction(
        self,
        function,
        high_function,
        analysis,
    ) -> Optional[Tuple[List[ReturnInfo], str]]:
        if analysis is None or not analysis.returns:
            return None
        if getattr(getattr(analysis, "effect_summary", None), "effects", None):
            self._debug("Declined readonly reduction summary: function mutates memory")
            return None

        pointer_param, count_param = self._infer_readonly_pointer_reduction_parameters(
            analysis,
            high_function,
        )
        if pointer_param is None or count_param is None:
            self._debug("Declined readonly reduction summary: pointer/count parameters not identified")
            return None

        broad_positive_conditions = self._readonly_reduction_positive_conditions(analysis, pointer_param, count_param)
        if ConditionSimplifier.object_centric_is_contradiction(broad_positive_conditions):
            self._debug("Declined readonly reduction summary: positive region is contradictory")
            return None

        accumulator_proof = self._detect_readonly_sum_accumulator_proof(
            high_function,
            analysis,
            pointer_param,
            count_param,
            positive_conditions=broad_positive_conditions,
        )
        positive_conditions = self._readonly_reduction_positive_conditions(
            analysis,
            pointer_param,
            count_param,
            loop_start_index=int(accumulator_proof.start_index) if accumulator_proof is not None else 0,
        )
        if ConditionSimplifier.object_centric_is_contradiction(positive_conditions):
            self._debug("Declined readonly reduction summary: positive loop region is contradictory")
            return None
        if accumulator_proof is None:
            self._debug(
                f"Declined readonly reduction summary for '{function.getName()}': "
                "no supported accumulator/load loop shape found"
            )
            return None

        overlapping_positive_returns = [
            ret for ret in (analysis.returns or [])
            if self._return_overlaps_conditions(ret, positive_conditions)
        ]
        if not overlapping_positive_returns:
            self._debug("Declined readonly reduction summary: no positive-region returns to replace")
            return None
        exact_return_candidates = [
            ret for ret in (analysis.returns or [])
            if self._return_overlaps_conditions(ret, broad_positive_conditions)
        ]

        preserved_returns = [
            ret for ret in (analysis.returns or [])
            if ret not in overlapping_positive_returns
        ]
        if not preserved_returns and not overlapping_positive_returns:
            return None
        for ret in preserved_returns:
            if ret not in exact_return_candidates:
                exact_return_candidates.append(ret)

        summary_pointer_expr = self._parameter_expression(pointer_param)
        summary_count_expr = self._parameter_expression(count_param)
        result_size = max(1, int(getattr(overlapping_positive_returns[0].value, "size", 0) or 0) or 4)
        semantic_witnesses = self._build_readonly_reduction_semantic_witnesses(
            analysis,
            pointer_param,
            count_param,
            overlapping_positive_returns,
            accumulator_proof,
            result_size=result_size,
        )
        exact_return_witnesses = self._extract_readonly_reduction_exact_witnesses(
            analysis,
            pointer_param,
            count_param,
            exact_return_candidates,
            accumulator_proof,
        )
        accumulator_proof = accumulator_proof.with_runtime_evidence(
            limit_expr=summary_count_expr,
            result_size=result_size,
            loop_body_witnesses=semantic_witnesses,
            exact_return_witnesses=exact_return_witnesses,
            guard_constraints=positive_conditions,
            signed_counter=bool(count_param.get("is_signed", True)),
        )
        reduction_ref = accumulator_proof.to_readonly_reduction_ref()
        if reduction_ref is None:
            self._debug("Declined readonly reduction summary: accumulator proof cannot lower to READONLY_SUM")
            return None
        summary_expr = Expression.intrinsic(
            "READONLY_SUM",
            [summary_pointer_expr, summary_count_expr],
            size=result_size,
            runtime_ref=reduction_ref,
            opcode=READONLY_SUM_OPCODE,
        )
        positive_anchor = overlapping_positive_returns[0]
        summarized_returns = list(preserved_returns)
        summarized_returns.append(
            ReturnInfo(
                address=positive_anchor.address,
                value=summary_expr,
                conditions=list(positive_conditions),
                branch_index=10_200,
                pcode_identity=positive_anchor.pcode_identity,
                pcode_order=positive_anchor.pcode_order,
                pcode_time=positive_anchor.pcode_time,
            )
        )
        self._debug(
            f"Recovered readonly pointer-reduction summary for '{function.getName()}' "
            f"(pointer={pointer_param.get('name')}, count={count_param.get('name')}, "
            f"stride={accumulator_proof.stride}, element_size={accumulator_proof.element_size})"
        )
        return summarized_returns, "readonly_pointer_reduction_summary"

    def _build_readonly_loop_summary_ref(
        self,
        *,
        summary_count_expr: Expression,
        pointer_base_ref: LocationBaseRef,
        accumulator_proof: ReductionAccumulatorProof,
        result_size: int,
        semantic_witnesses: Sequence[ReadonlyReductionWitness],
        seed_terms: Sequence[ReadonlyReductionTermRef] = (),
        guard_constraints: Sequence[Condition] = (),
    ) -> Optional[LoopSummaryRef]:
        proof = ReductionAccumulatorProof(
            reduction_kind=accumulator_proof.reduction_kind,
            pointer_base_ref=pointer_base_ref,
            count_parameter_name=accumulator_proof.count_parameter_name,
            count_parameter_index=accumulator_proof.count_parameter_index,
            limit_expr=summary_count_expr,
            result_size=max(1, int(result_size or 0)),
            stride=accumulator_proof.stride,
            element_size=accumulator_proof.element_size,
            start_offset=accumulator_proof.start_offset,
            start_index=accumulator_proof.start_index,
            index_step=accumulator_proof.index_step,
            index_scale=accumulator_proof.index_scale,
            signed_counter=accumulator_proof.signed_counter,
            seed_terms=tuple(seed_terms or accumulator_proof.seed_terms or ()),
            lane_terms=accumulator_proof.lane_terms,
            loop_body_witnesses=tuple(semantic_witnesses or ()),
            exact_return_witnesses=accumulator_proof.exact_return_witnesses,
            guard_constraints=tuple(guard_constraints or ()),
            side_effect_profile=accumulator_proof.side_effect_profile,
            constant_bias=accumulator_proof.constant_bias,
            induction_phi_ref=accumulator_proof.induction_phi_ref,
            accumulator_phi_ref=accumulator_proof.accumulator_phi_ref,
            update_op_ref=accumulator_proof.update_op_ref,
            load_op_refs=accumulator_proof.load_op_refs,
            entry_block_ref=accumulator_proof.entry_block_ref,
            backedge_block_ref=accumulator_proof.backedge_block_ref,
            source=accumulator_proof.source,
        )
        return proof.to_loop_summary_ref()

    def _infer_readonly_pointer_reduction_parameters(
        self,
        analysis,
        high_function,
    ) -> Tuple[Optional[dict], Optional[dict]]:
        parameters = list(analysis.parameters or [])
        if not parameters:
            return None, None

        pointer_ranked: List[Tuple[int, int, dict]] = []
        for param in parameters:
            score = self._readonly_pointer_candidate_score(
                analysis,
                high_function,
                param,
            )
            if score <= 0:
                continue
            pointer_ranked.append((score, -int(param.get("index", 0) or 0), param))
        pointer_ranked.sort(reverse=True)
        pointer_param = pointer_ranked[0][2] if pointer_ranked else None

        counter_ranked: List[Tuple[int, int, dict]] = []
        for param in parameters:
            if pointer_param is not None and int(param.get("index", -1)) == int(pointer_param.get("index", -2)):
                continue
            score = self._readonly_counter_candidate_score(analysis, param)
            if score <= 0:
                continue
            counter_ranked.append((score, -int(param.get("index", 0) or 0), param))
        counter_ranked.sort(reverse=True)
        counter_param = counter_ranked[0][2] if counter_ranked else None

        if pointer_param is None and counter_param is not None and len(parameters) == 2:
            pointer_param = next(
                (param for param in parameters if int(param.get("index", -1)) != int(counter_param.get("index", -1))),
                None,
            )
        if counter_param is None and pointer_param is not None and len(parameters) == 2:
            counter_param = next(
                (param for param in parameters if int(param.get("index", -1)) != int(pointer_param.get("index", -1))),
                None,
            )
        return pointer_param, counter_param

    def _readonly_pointer_candidate_score(
        self,
        analysis,
        high_function,
        param: dict,
    ) -> int:
        score = 0
        if is_pointer_data_type(
            param.get("data_type_obj"),
            param.get("data_type"),
            program=getattr(self.tracer, "program", None),
        ):
            score += 8
        if self._parameter_has_pointer_progression(high_function, param):
            score += 6
        if self._parameter_bases_memory_reads(analysis, param):
            score += 4
        if self._parameter_has_pointer_guards(analysis, param):
            score += 1
        return score

    def _readonly_counter_candidate_score(
        self,
        analysis,
        param: dict,
    ) -> int:
        score = 0
        if self._parameter_can_be_counter(param):
            score += 4
        if self._analysis_mentions_parameter_in_conditions(analysis, str(param.get("name", "") or "")):
            score += 3
        return score

    def _parameter_has_pointer_progression(
        self,
        high_function,
        param: dict,
    ) -> bool:
        if high_function is None:
            return False
        for op in self._iter_pcode_ops(high_function):
            if getattr(op, "getMnemonic", lambda: None)() != "MULTIEQUAL":
                continue
            if self._match_pointer_progression_phi(op, param) is not None:
                return True
        return False

    def _parameter_bases_memory_reads(
        self,
        analysis,
        param: dict,
    ) -> bool:
        for ret in analysis.returns or []:
            for node in self._iter_expression_nodes(ret.value):
                if node.expr_type == ExpressionType.MEMORY and node.operands:
                    location = canonicalize_location(
                        node.operands[0],
                        analysis.parameters or [],
                        size=max(1, int(getattr(node, "size", 0) or 0) or 1),
                    )
                    if location is not None and location.base_ref.matches_parameter(param):
                        return True
                if node.expr_type == ExpressionType.INTRINSIC and getattr(node, "name", None) == "PTRADD":
                    base_name = self._parameter_name_from_expr(node.operands[0] if node.operands else None)
                    if base_name and base_name == param.get("name"):
                        return True
        return False

    def _parameter_has_pointer_guards(
        self,
        analysis,
        param: dict,
    ) -> bool:
        pointer_name = str(param.get("name", "") or "")
        if not pointer_name:
            return False
        for ret in analysis.returns or []:
            for condition in ret.conditions or []:
                if (
                    self._condition_is_pointer_null(condition, pointer_name)
                    or self._condition_is_pointer_nonnull(condition, pointer_name)
                ):
                    return True
        return False

    def _iter_expression_nodes(self, expr: Optional[Expression]):
        if expr is None:
            return
        stack = [expr]
        seen = set()
        while stack:
            current = stack.pop()
            if current is None:
                continue
            current_id = id(current)
            if current_id in seen:
                continue
            seen.add(current_id)
            yield current
            if current.expr_type == ExpressionType.PHI and current.value:
                for cond, value in current.value:
                    if cond is not None and getattr(cond, "expression", None) is not None:
                        stack.append(cond.expression)
                    if value is not None:
                        stack.append(value)
                continue
            for operand in reversed(list(getattr(current, "operands", None) or [])):
                stack.append(operand)

    def _readonly_reduction_positive_conditions(
        self,
        analysis,
        pointer_param: dict,
        count_param: dict,
        *,
        loop_start_index: int = 0,
    ) -> List[Condition]:
        pointer_expr = self._parameter_expression(pointer_param)
        count_expr = self._parameter_expression(count_param)
        lower_bound = max(0, int(loop_start_index or 0))
        return [
            Condition(
                Expression.binary_op(
                    "INT_NOTEQUAL",
                    pointer_expr,
                    Expression.constant(0, pointer_expr.size or 8),
                ),
                False,
            ),
            Condition(
                Expression.binary_op(
                    "INT_SLESS",
                    Expression.constant(lower_bound, count_expr.size or 4),
                    count_expr,
                ),
                False,
            ),
        ]

    def _return_overlaps_conditions(
        self,
        ret: ReturnInfo,
        conditions: Sequence[Condition],
    ) -> bool:
        return not ConditionSimplifier.object_centric_is_contradiction(
            list(ret.conditions or []) + list(conditions or [])
        )

    def _detect_readonly_sum_accumulator_proof(
        self,
        high_function,
        analysis,
        pointer_param: dict,
        count_param: dict,
        *,
        positive_conditions: Sequence[Condition] = (),
    ) -> Optional[ReductionAccumulatorProof]:
        if not self._analysis_mentions_parameter_in_conditions(
            analysis,
            count_param.get("name", ""),
        ):
            self._debug("Declined readonly reduction summary: counter not observed in guards")
            return None

        pointer_phis: List[Dict[str, object]] = []
        index_phis: List[Dict[str, object]] = []
        pointer_base_ref = LocationBaseRef.parameter(
            pointer_param.get("name", "ptr"),
            index=pointer_param.get("index"),
            owner_program_id=pointer_param.get("owner_program_id"),
            owner_entry_offset=pointer_param.get("owner_entry_offset"),
        )
        count_expr = self._parameter_expression(count_param)
        result_size = self._readonly_reduction_result_size(
            analysis,
            positive_conditions=positive_conditions,
        )
        all_ops = list(self._iter_pcode_ops(high_function))
        for op in all_ops:
            if getattr(op, "getMnemonic", lambda: None)() != "MULTIEQUAL":
                continue
            pointer_match = self._match_pointer_progression_phi(op, pointer_param)
            if pointer_match is not None:
                pointer_phis.append(pointer_match)
            index_match = self._match_index_progression_phi(op)
            if index_match is not None:
                index_phis.append(index_match)

        for op in all_ops:
            if getattr(op, "getMnemonic", lambda: None)() != "MULTIEQUAL":
                continue
            accumulator_match = self._match_accumulator_phi(
                op,
                pointer_param,
                count_param,
                pointer_base_ref,
                count_expr,
                pointer_phis,
                index_phis,
                result_size=result_size,
                positive_conditions=positive_conditions,
            )
            if accumulator_match is not None:
                return accumulator_match

        vectorized_match = self._detect_vectorized_readonly_prefix_sum_accumulator_proof(
            all_ops,
            pointer_param,
            count_param,
            pointer_base_ref,
            count_expr,
            analysis,
            positive_conditions=positive_conditions,
        )
        if vectorized_match is not None:
            return vectorized_match
        if not pointer_phis and not index_phis:
            self._debug("Declined readonly reduction summary: no pointer/index progression PHI found")
        return None

    def _detect_vectorized_readonly_prefix_sum_accumulator_proof(
        self,
        all_ops: Sequence[object],
        pointer_param: dict,
        count_param: dict,
        pointer_base_ref: LocationBaseRef,
        count_expr: Expression,
        analysis,
        *,
        positive_conditions: Sequence[Condition] = (),
    ) -> Optional[ReductionAccumulatorProof]:
        """Recognize a vector-body plus scalar-tail readonly prefix sum.

        Optimizing compilers often lower ``sum(base[0:count])`` into two
        loops: a vector/unrolled body over ``count & -K`` elements and a
        scalar tail from that rounded count to ``count``.  The normal
        recurrence detector intentionally expects a single canonical induction
        PHI, so this recognizer proves the object-level coverage of the two
        loops before collapsing them back to the scalar prefix-sum summary.
        """

        result_size = self._readonly_reduction_result_size(
            analysis,
            positive_conditions=positive_conditions,
        )
        if result_size <= 0:
            return None

        rounded_candidates = self._readonly_round_down_candidates(all_ops, count_param)
        if not rounded_candidates:
            self._debug("Declined vectorized readonly prefix-sum shape: no rounded-count candidate")
            return None

        for rounded_vn, lane_count in rounded_candidates:
            if lane_count <= 1:
                continue
            vector_stride = lane_count * result_size
            vector_pointer = self._match_vector_prefix_pointer(
                all_ops,
                pointer_param,
                vector_stride=vector_stride,
                element_size=result_size,
            )
            if vector_pointer is None:
                self._debug(
                    "Declined vectorized readonly prefix-sum candidate: "
                    f"no vector pointer progression for lanes={lane_count}"
                )
                continue
            pointer_phi, vector_base_offset = vector_pointer
            if not self._vector_prefix_lanes_cover_block(
                all_ops,
                pointer_phi,
                base_offset=vector_base_offset,
                vector_stride=vector_stride,
                element_size=result_size,
            ):
                self._debug(
                    "Declined vectorized readonly prefix-sum candidate: "
                    f"vector lanes do not cover one contiguous block (lanes={lane_count})"
                )
                continue
            vector_region_conditions = list(positive_conditions or [])
            count_expr = self._parameter_expression(count_param)
            vector_region_conditions.append(
                Condition(
                    Expression.binary_op(
                        "INT_SLESSEQUAL",
                        Expression.constant(lane_count, count_expr.size or 4),
                        count_expr,
                    ),
                    False,
                )
            )
            return_term_proof = self._vector_prefix_lanes_have_unit_terms_in_positive_return(
                analysis,
                pointer_param,
                vector_region_conditions,
                vector_stride=vector_stride,
                element_size=result_size,
            )
            def_use_term_proof = self._vector_prefix_lanes_contribute_additively_to_return(
                all_ops,
                pointer_phi,
                base_offset=vector_base_offset,
                vector_stride=vector_stride,
                element_size=result_size,
            )
            if return_term_proof is not True:
                self._debug(
                    "Declined vectorized readonly prefix-sum candidate: "
                    f"positive return is not an exact readonly sum witness (lanes={lane_count})"
                )
                continue
            if not def_use_term_proof:
                self._debug(
                    "Declined vectorized readonly prefix-sum candidate: "
                    f"vector lanes do not flow additively to the return (lanes={lane_count})"
                )
                continue
            if not (
                self._has_vector_countdown_loop(
                    all_ops,
                    rounded_vn,
                    lane_count=lane_count,
                )
                or self._has_vector_loop_bound_to_rounded_count(
                    all_ops,
                    pointer_phi,
                    pointer_param,
                    rounded_vn,
                    element_size=result_size,
                    base_offset=vector_base_offset,
                    vector_stride=vector_stride,
                )
            ):
                self._debug(
                    "Declined vectorized readonly prefix-sum candidate: "
                    f"no object-centric bound tying vector cursor to rounded count (lanes={lane_count})"
                )
                continue
            if not self._has_scalar_tail_from_rounded_count(
                all_ops,
                pointer_param,
                count_param,
                rounded_vn,
                element_size=result_size,
            ):
                self._debug(
                    "Declined vectorized readonly prefix-sum candidate: "
                    f"no scalar tail from rounded count to full count (lanes={lane_count})"
                )
                continue
            self._debug(
                "Recovered vectorized readonly prefix-sum accumulator proof "
                f"(lanes={lane_count}, element_size={result_size})"
            )
            return ReductionAccumulatorProof(
                reduction_kind="memory_sum",
                pointer_base_ref=pointer_base_ref,
                count_parameter_name=count_param.get("name", "count"),
                count_parameter_index=count_param.get("index"),
                limit_expr=count_expr,
                result_size=max(1, int(result_size)),
                stride=int(result_size),
                element_size=int(result_size),
                start_offset=0,
                start_index=0,
                index_step=1,
                index_scale=int(result_size),
                signed_counter=bool(count_param.get("is_signed", True)),
                seed_terms=(),
                lane_terms=(),
                guard_constraints=tuple(positive_conditions or ()),
                entry_block_ref=self._make_pcode_block_ref(getattr(pointer_phi, "getParent", lambda: None)()),
                source="recurrence_summary",
            )
        return None

    def _readonly_reduction_result_size(
        self,
        analysis,
        *,
        positive_conditions: Sequence[Condition] = (),
    ) -> int:
        returns = list(getattr(analysis, "returns", None) or [])
        if positive_conditions:
            overlapping = [
                ret for ret in returns
                if self._return_overlaps_conditions(ret, positive_conditions)
            ]
            if overlapping:
                returns = overlapping
        for ret in returns:
            value = getattr(ret, "value", None)
            size = int(getattr(value, "size", 0) or 0)
            if size > 0:
                return size
        return 4

    def _readonly_round_down_candidates(
        self,
        all_ops: Sequence[object],
        count_param: dict,
    ) -> List[Tuple[object, int]]:
        candidates: List[Tuple[object, int]] = []
        for op in all_ops:
            if getattr(op, "getMnemonic", lambda: None)() != "INT_AND":
                continue
            if int(getattr(op, "getNumInputs", lambda: 0)() or 0) < 2:
                continue
            left = self._follow_passthrough_varnode(op.getInput(0))
            right = self._follow_passthrough_varnode(op.getInput(1))
            mask = self._varnode_unsigned_constant_value(left)
            value = right
            if mask is None:
                mask = self._varnode_unsigned_constant_value(right)
                value = left
            if mask is None or not self._varnode_matches_parameter(value, count_param.get("name", "")):
                continue
            count_width_bits = self._infer_counter_bit_width(
                self._trace_varnode_expression(value),
                str(count_param.get("name", "") or ""),
            )
            if count_width_bits is None:
                count_width_bits = self._varnode_bit_width(value)
            if count_width_bits is None:
                count_width_bits = max(1, int(count_param.get("size", 0) or 0)) * 8
            lane_count = self._power_of_two_rounding_from_mask(mask, count_width_bits=count_width_bits)
            if lane_count is None:
                continue
            output = getattr(op, "getOutput", lambda: None)()
            if output is not None:
                candidates.append((output, lane_count))
        return candidates

    def _power_of_two_rounding_from_mask(self, mask: int, *, count_width_bits: int) -> Optional[int]:
        width_bits = int(count_width_bits or 0)
        if width_bits <= 0:
            return None
        full_mask = (1 << width_bits) - 1
        current = int(mask) & full_mask
        low_clear = 0
        while low_clear < width_bits and (current & (1 << low_clear)) == 0:
            low_clear += 1
        if low_clear <= 0:
            return None
        lane_count = 1 << low_clear
        expected = full_mask ^ (lane_count - 1)
        if current != expected:
            return None
        return lane_count

    def _varnode_bit_width(self, varnode) -> Optional[int]:
        try:
            size = int(getattr(varnode, "getSize", lambda: 0)() or 0)
        except Exception:
            size = 0
        if size > 0:
            return size * 8
        expr = self._trace_varnode_expression(varnode)
        size = int(getattr(expr, "size", 0) or 0)
        if size > 0:
            return size * 8
        return None

    def _match_vector_prefix_pointer(
        self,
        all_ops: Sequence[object],
        pointer_param: dict,
        *,
        vector_stride: int,
        element_size: int,
    ) -> Optional[Tuple[object, int]]:
        for op in all_ops:
            if getattr(op, "getMnemonic", lambda: None)() != "MULTIEQUAL":
                continue
            phi_output = getattr(op, "getOutput", lambda: None)()
            if phi_output is None:
                continue
            if not self._phi_has_pointer_step(
                all_ops,
                phi_output,
                step_bytes=vector_stride,
            ):
                continue
            lane_offsets = self._load_byte_offsets_from_pointer(all_ops, phi_output, element_size=element_size)
            if not lane_offsets:
                continue
            min_offset = min(lane_offsets)
            base_offset = -int(min_offset)
            if base_offset < 0:
                continue
            if not self._has_pointer_base_plus_constant(
                all_ops,
                pointer_param,
                base_offset,
            ):
                continue
            return phi_output, base_offset
        return None

    def _phi_has_pointer_step(
        self,
        all_ops: Sequence[object],
        phi_output,
        *,
        step_bytes: int,
    ) -> bool:
        for op in all_ops:
            if getattr(op, "getMnemonic", lambda: None)() != "PTRADD":
                continue
            if int(getattr(op, "getNumInputs", lambda: 0)() or 0) < 3:
                continue
            base = self._follow_passthrough_varnode(op.getInput(0))
            if not self._same_varnode_value(base, phi_output):
                continue
            index = self._signed_varnode_constant_value(self._follow_passthrough_varnode(op.getInput(1)))
            elem = self._varnode_unsigned_constant_value(self._follow_passthrough_varnode(op.getInput(2)))
            if index is not None and elem is not None and int(index) * int(elem) == int(step_bytes):
                return True
        return False

    def _has_pointer_base_plus_constant(
        self,
        all_ops: Sequence[object],
        pointer_param: dict,
        byte_offset: int,
    ) -> bool:
        if int(byte_offset) == 0:
            return True
        for op in all_ops:
            mnemonic = getattr(op, "getMnemonic", lambda: None)()
            if mnemonic in {"INT_ADD", "PTRSUB"} and int(getattr(op, "getNumInputs", lambda: 0)() or 0) >= 2:
                left = self._follow_passthrough_varnode(op.getInput(0))
                right = self._follow_passthrough_varnode(op.getInput(1))
                if (
                    self._varnode_matches_parameter(left, pointer_param.get("name", ""))
                    and self._signed_varnode_constant_value(right) == int(byte_offset)
                ):
                    return True
                if (
                    mnemonic == "INT_ADD"
                    and self._varnode_matches_parameter(right, pointer_param.get("name", ""))
                    and self._signed_varnode_constant_value(left) == int(byte_offset)
                ):
                    return True
            if mnemonic == "PTRADD" and int(getattr(op, "getNumInputs", lambda: 0)() or 0) >= 3:
                base = self._follow_passthrough_varnode(op.getInput(0))
                index = self._signed_varnode_constant_value(self._follow_passthrough_varnode(op.getInput(1)))
                elem = self._varnode_unsigned_constant_value(self._follow_passthrough_varnode(op.getInput(2)))
                if (
                    self._varnode_matches_parameter(base, pointer_param.get("name", ""))
                    and index is not None
                    and elem is not None
                    and int(index) * int(elem) == int(byte_offset)
                ):
                    return True
        return False

    def _load_byte_offsets_from_pointer(
        self,
        all_ops: Sequence[object],
        pointer_phi,
        *,
        element_size: int,
    ) -> List[int]:
        offsets: List[int] = []
        for op in all_ops:
            if getattr(op, "getMnemonic", lambda: None)() != "LOAD":
                continue
            if int(getattr(op, "getNumInputs", lambda: 0)() or 0) < 2:
                continue
            output = getattr(op, "getOutput", lambda: None)()
            load_size = max(1, int(getattr(output, "getSize", lambda: element_size)() or element_size))
            address = self._follow_passthrough_varnode(op.getInput(1))
            byte_offset = self._byte_offset_from_pointer(address, pointer_phi)
            if byte_offset is None:
                continue
            for lane_delta in range(0, load_size, element_size):
                offsets.append(int(byte_offset) + int(lane_delta))
        return offsets

    def _byte_offset_from_pointer(self, address_varnode, pointer_phi) -> Optional[int]:
        if self._same_varnode_value(address_varnode, pointer_phi):
            return 0
        def_op = getattr(address_varnode, "getDef", lambda: None)()
        if def_op is None or getattr(def_op, "getMnemonic", lambda: None)() != "PTRADD":
            return None
        if int(getattr(def_op, "getNumInputs", lambda: 0)() or 0) < 3:
            return None
        base = self._follow_passthrough_varnode(def_op.getInput(0))
        if not self._same_varnode_value(base, pointer_phi):
            return None
        index = self._signed_varnode_constant_value(self._follow_passthrough_varnode(def_op.getInput(1)))
        elem = self._varnode_unsigned_constant_value(self._follow_passthrough_varnode(def_op.getInput(2)))
        if index is None or elem is None:
            return None
        return int(index) * int(elem)

    def _vector_prefix_lanes_cover_block(
        self,
        all_ops: Sequence[object],
        pointer_phi,
        *,
        base_offset: int,
        vector_stride: int,
        element_size: int,
    ) -> bool:
        raw_offsets = self._load_byte_offsets_from_pointer(all_ops, pointer_phi, element_size=element_size)
        normalized = sorted({int(offset) + int(base_offset) for offset in raw_offsets})
        expected = list(range(0, int(vector_stride), int(element_size)))
        return normalized == expected

    def _vector_prefix_lanes_have_unit_terms_in_positive_return(
        self,
        analysis,
        pointer_param: dict,
        vector_region_conditions: Sequence[Condition],
        *,
        vector_stride: int,
        element_size: int,
    ) -> Optional[bool]:
        expected = {
            (int(byte_offset), int(element_size))
            for byte_offset in range(0, int(vector_stride), int(element_size))
        }
        expected_counts = Counter({term_key: 1 for term_key in expected})
        saw_overlapping_return = False
        for ret in getattr(analysis, "returns", None) or ():
            if not self._return_overlaps_conditions(ret, vector_region_conditions):
                continue
            saw_overlapping_return = True
            value = _reduce_expression_under_conditions(ret.value, ret.conditions or ())
            terms = self._extract_readonly_reduction_terms(
                value,
                getattr(analysis, "parameters", None) or (),
                pointer_param,
            )
            if terms is None and value is not ret.value:
                terms = self._extract_readonly_reduction_terms(
                    ret.value,
                    getattr(analysis, "parameters", None) or (),
                    pointer_param,
                )
            if terms is None:
                return False
            counts = Counter((int(term.byte_offset), int(term.access_size)) for term in terms)
            if counts != expected_counts:
                return False
        return True if saw_overlapping_return else None

    def _vector_prefix_lanes_contribute_additively_to_return(
        self,
        all_ops: Sequence[object],
        pointer_phi,
        *,
        base_offset: int,
        vector_stride: int,
        element_size: int,
    ) -> bool:
        expected_offsets = set(range(0, int(vector_stride), int(element_size)))
        expected_counts = Counter({offset: 1 for offset in expected_offsets})
        contributing_counts: Counter[int] = Counter()
        for op in all_ops:
            if getattr(op, "getMnemonic", lambda: None)() != "LOAD":
                continue
            if int(getattr(op, "getNumInputs", lambda: 0)() or 0) < 2:
                continue
            output = getattr(op, "getOutput", lambda: None)()
            if output is None:
                continue
            load_size = max(1, int(getattr(output, "getSize", lambda: element_size)() or element_size))
            address = self._follow_passthrough_varnode(op.getInput(1))
            byte_offset = self._byte_offset_from_pointer(address, pointer_phi)
            if byte_offset is None:
                continue
            normalized_offsets = [
                int(byte_offset) + int(base_offset) + lane_delta
                for lane_delta in range(0, load_size, element_size)
            ]
            if any(offset not in expected_offsets for offset in normalized_offsets):
                if self._load_lanes_flow_additively_to_return(
                    output,
                    load_size=load_size,
                    element_size=element_size,
                    pointer_phi=pointer_phi,
                    expected_offsets=expected_offsets,
                    base_offset=base_offset,
                ):
                    self._debug(
                        "Declined vectorized readonly prefix-sum load contribution: "
                        f"unexpected_offsets={tuple(normalized_offsets)}"
                    )
                    return False
                continue
            if self._load_lanes_flow_additively_to_return(
                output,
                load_size=load_size,
                element_size=element_size,
                pointer_phi=pointer_phi,
                expected_offsets=expected_offsets,
                base_offset=base_offset,
            ):
                contributing_counts.update(normalized_offsets)
        return contributing_counts == expected_counts

    def _load_lanes_flow_additively_to_return(
        self,
        load_output,
        *,
        load_size: int,
        element_size: int,
        pointer_phi=None,
        expected_offsets: Sequence[int] = (),
        base_offset: int = 0,
    ) -> bool:
        required_lanes = max(1, int(load_size) // max(1, int(element_size)))
        if required_lanes <= 1:
            count = self._varnode_additive_return_contribution_count(load_output)
            if count != 1:
                self._debug(
                    "Declined vectorized readonly prefix-sum load contribution: "
                    f"load={self._varnode_cache_key(load_output)} contribution_count={count}"
                )
            return count == 1
        lane_roots = self._collect_scalar_lane_roots(load_output, element_size=element_size)
        if len(lane_roots) != required_lanes:
            self._debug(
                "Declined vectorized readonly prefix-sum load contribution: "
                f"load={self._varnode_cache_key(load_output)} "
                f"lane_roots={len(lane_roots)} required_lanes={required_lanes}"
            )
            return False
        counts = tuple(
            self._varnode_additive_return_contribution_count(lane)
            for lane in lane_roots
        )
        if any(count != 1 for count in counts):
            self._debug(
                "Declined vectorized readonly prefix-sum load contribution: "
                f"load={self._varnode_cache_key(load_output)} lane_counts={counts}"
            )
            return False
        return True

    def _collect_scalar_lane_roots(
        self,
        start_varnode,
        *,
        element_size: int,
        budget: int = 64,
    ) -> Tuple[object, ...]:
        lanes: List[object] = []
        stack = [start_varnode]
        seen = set()
        while stack and len(seen) < budget:
            current = stack.pop()
            key = self._varnode_cache_key(current)
            if key in seen:
                continue
            seen.add(key)
            for op in self._iter_varnode_descendant_ops(current):
                mnemonic = getattr(op, "getMnemonic", lambda: None)()
                output = getattr(op, "getOutput", lambda: None)()
                if output is None:
                    continue
                output_size = max(1, int(getattr(output, "getSize", lambda: element_size)() or element_size))
                if mnemonic == "SUBPIECE" and output_size == int(element_size):
                    lanes.append(output)
                    continue
                if mnemonic in {"INT_RIGHT", "COPY", "CAST", "INT_ZEXT", "INT_SEXT"}:
                    stack.append(output)
        unique: Dict[Tuple[Any, ...], object] = {}
        for lane in lanes:
            key = self._varnode_cache_key(lane)
            if key is not None:
                unique[key] = lane
        return tuple(unique.values())

    def _varnode_additive_return_contribution_count(
        self,
        start_varnode,
        *,
        budget: int = 128,
    ) -> int:
        allowed = {
            "INT_ADD",
            "COPY",
            "CAST",
            "INT_ZEXT",
            "INT_SEXT",
            "SUBPIECE",
            "MULTIEQUAL",
        }
        stack = [(start_varnode, 1)]
        seen_coefficients: Dict[Tuple[Any, ...], int] = {}
        return_count = 0
        steps = 0
        while stack and steps < budget:
            current, coefficient = stack.pop()
            steps += 1
            if coefficient <= 0:
                continue
            key = self._varnode_cache_key(current)
            previous = seen_coefficients.get(key)
            if previous is not None and previous >= coefficient:
                continue
            seen_coefficients[key] = coefficient
            for op in self._iter_varnode_descendant_ops(current):
                mnemonic = getattr(op, "getMnemonic", lambda: None)()
                input_multiplicity = self._varnode_input_multiplicity(op, current)
                if input_multiplicity <= 0:
                    continue
                if mnemonic == "RETURN":
                    return_count += coefficient * input_multiplicity
                    if return_count > 1:
                        return 2
                    continue
                if mnemonic not in allowed:
                    continue
                if mnemonic == "MULTIEQUAL":
                    accepted_phi_input = self._multiequal_input_is_accumulator_update(
                        op,
                        current,
                    )
                    if not accepted_phi_input:
                        self._debug(
                            "Declined vectorized readonly prefix-sum accumulator PHI contribution: "
                            f"phi={self._varnode_cache_key(getattr(op, 'getOutput', lambda: None)())} "
                            f"input={self._varnode_cache_key(current)} "
                            f"reason={self._multiequal_accumulator_update_rejection_reason(op)}"
                        )
                        continue
                output = getattr(op, "getOutput", lambda: None)()
                if output is not None:
                    next_coefficient = coefficient
                    if mnemonic == "INT_ADD":
                        next_coefficient *= input_multiplicity
                    if next_coefficient > 1:
                        return 2
                    stack.append((output, next_coefficient))
        return min(return_count, 2)

    def _multiequal_input_is_accumulator_update(self, phi_op, input_varnode) -> bool:
        return self._same_varnode_identity(
            input_varnode,
            self._unique_multiequal_accumulator_update_input(phi_op),
        )

    def _unique_multiequal_accumulator_update_input(self, phi_op):
        phi_output = getattr(phi_op, "getOutput", lambda: None)()
        if phi_output is None:
            return None
        update_inputs = []
        seed_inputs = []
        input_count = int(getattr(phi_op, "getNumInputs", lambda: 0)() or 0)
        for index in range(input_count):
            try:
                candidate = phi_op.getInput(index)
            except Exception:
                continue
            if self._varnode_is_accumulator_update_for_phi(candidate, phi_output):
                update_inputs.append((index, candidate))
            else:
                seed_inputs.append((index, candidate))
        if len(update_inputs) != 1:
            return None
        if not seed_inputs:
            return None
        update_indices = tuple(index for index, _candidate in update_inputs)
        for seed_index, seed_input in seed_inputs:
            if self._varnode_depends_on_varnode(seed_input, phi_output):
                return None
            if self._varnode_aliases_accumulator_object(seed_input, phi_output) and not (
                self._phi_input_is_cfg_entry_seed(phi_op, seed_index, update_indices)
            ):
                return None
        return update_inputs[0][1]

    def _multiequal_accumulator_update_rejection_reason(self, phi_op) -> str:
        phi_output = getattr(phi_op, "getOutput", lambda: None)()
        if phi_output is None:
            return "no_phi_output"
        update_inputs = []
        seed_inputs = []
        input_count = int(getattr(phi_op, "getNumInputs", lambda: 0)() or 0)
        for index in range(input_count):
            try:
                candidate = phi_op.getInput(index)
            except Exception:
                continue
            if self._varnode_is_accumulator_update_for_phi(candidate, phi_output):
                update_inputs.append((index, candidate))
            else:
                seed_inputs.append((index, candidate))
        seed_depends = [
            self._varnode_depends_on_varnode(seed_input, phi_output)
            for _seed_index, seed_input in seed_inputs
        ]
        seed_aliases = [
            self._varnode_aliases_accumulator_object(seed_input, phi_output)
            for _seed_index, seed_input in seed_inputs
        ]
        update_indices = tuple(index for index, _candidate in update_inputs)
        seed_entry = [
            self._phi_input_is_cfg_entry_seed(phi_op, seed_index, update_indices)
            for seed_index, _seed_input in seed_inputs
        ]
        return (
            f"updates={len(update_inputs)}, seeds={len(seed_inputs)}, "
            f"seed_depends={tuple(seed_depends)}, seed_aliases={tuple(seed_aliases)}, "
            f"seed_entry={tuple(seed_entry)}"
        )

    def _varnode_is_accumulator_update_for_phi(self, candidate, phi_output) -> bool:
        def_op = getattr(candidate, "getDef", lambda: None)()
        if def_op is None or getattr(def_op, "getMnemonic", lambda: None)() != "INT_ADD":
            return False
        if int(getattr(def_op, "getNumInputs", lambda: 0)() or 0) < 2:
            return False
        for index in range(int(getattr(def_op, "getNumInputs", lambda: 0)() or 0)):
            try:
                candidate = self._follow_passthrough_varnode(def_op.getInput(index))
            except Exception:
                continue
            if self._same_varnode_value(candidate, phi_output):
                return True
        return False

    def _varnode_depends_on_varnode(self, start_varnode, target_varnode, *, budget: int = 64) -> bool:
        stack = [start_varnode]
        seen = set()
        steps = 0
        while stack and steps < budget:
            current = stack.pop()
            steps += 1
            key = self._varnode_cache_key(current)
            if key in seen:
                continue
            seen.add(key)
            if self._same_varnode_identity(current, target_varnode):
                return True
            def_op = getattr(current, "getDef", lambda: None)()
            if def_op is None:
                continue
            input_count = int(getattr(def_op, "getNumInputs", lambda: 0)() or 0)
            for index in range(input_count):
                try:
                    stack.append(def_op.getInput(index))
                except Exception:
                    continue
        return False

    def _varnode_aliases_accumulator_object(self, candidate, phi_output) -> bool:
        """Return True when a non-update PHI input is the accumulator object itself.

        This deliberately avoids storage-address equality: optimized Ghidra SSA can
        place a real entry seed and a loop-carried value in the same register slot.
        HighVariable and representative identity, however, mean the input is not an
        independent seed object but an alias of the accumulator's SSA object.
        """
        if candidate is None or phi_output is None:
            return False
        try:
            candidate_high = candidate.getHigh()
            phi_high = phi_output.getHigh()
        except Exception:
            return False
        if candidate_high is None or phi_high is None:
            return False
        if candidate_high is phi_high:
            return True
        try:
            if candidate_high == phi_high:
                return True
        except Exception:
            pass
        try:
            candidate_rep = candidate_high.getRepresentative()
            phi_rep = phi_high.getRepresentative()
        except Exception:
            candidate_rep = None
            phi_rep = None
        if candidate_rep is not None and phi_rep is not None:
            if candidate_rep is phi_rep:
                return True
            if self._same_varnode_identity(candidate_rep, phi_rep):
                return True
        return False

    def _phi_input_is_cfg_entry_seed(
        self,
        phi_op,
        input_index: int,
        update_indices: Sequence[int],
    ) -> bool:
        parent_block = getattr(phi_op, "getParent", lambda: None)()
        if parent_block is None:
            return False
        in_size = int(getattr(parent_block, "getInSize", lambda: 0)() or 0)
        if input_index < 0 or input_index >= in_size:
            return False
        try:
            seed_predecessor = parent_block.getIn(input_index)
        except Exception:
            return False
        if seed_predecessor is None:
            return False
        for update_index in update_indices:
            if update_index < 0 or update_index >= in_size:
                return False
            try:
                update_predecessor = parent_block.getIn(update_index)
            except Exception:
                return False
            if seed_predecessor is update_predecessor:
                return False
        return not self._cfg_block_reachable_without_reentering_header(
            parent_block,
            seed_predecessor,
            budget=128,
        )

    def _cfg_block_reachable_without_reentering_header(
        self,
        header_block,
        target_block,
        *,
        budget: int = 128,
    ) -> bool:
        if header_block is None or target_block is None:
            return False
        stack = [header_block]
        seen = set()
        steps = 0
        while stack and steps < budget:
            current = stack.pop()
            steps += 1
            current_key = self._block_identity_key(current)
            if current_key in seen:
                continue
            seen.add(current_key)
            out_size = int(getattr(current, "getOutSize", lambda: 0)() or 0)
            for index in range(out_size):
                try:
                    successor = current.getOut(index)
                except Exception:
                    continue
                if successor is target_block:
                    return True
                if successor is None or successor is header_block:
                    continue
                stack.append(successor)
        return False

    def _block_identity_key(self, block) -> object:
        if block is None:
            return None
        try:
            return ("block_index", int(block.getIndex()))
        except Exception:
            return ("block_id", id(block))

    def _same_varnode_identity(self, left, right) -> bool:
        if left is None or right is None:
            return False
        if left is right:
            return True
        left_key = self._varnode_cache_key(left)
        right_key = self._varnode_cache_key(right)
        return left_key is not None and right_key is not None and left_key == right_key

    def _varnode_input_multiplicity(self, op, varnode) -> int:
        count = 0
        input_count = int(getattr(op, "getNumInputs", lambda: 0)() or 0)
        for index in range(input_count):
            try:
                candidate = op.getInput(index)
            except Exception:
                continue
            if self._same_varnode_value(candidate, varnode):
                count += 1
        return count

    def _iter_varnode_descendant_ops(self, varnode):
        descendants = getattr(varnode, "getDescendants", lambda: None)()
        if descendants is None:
            return ()
        try:
            return tuple(iter(descendants))
        except TypeError:
            pass
        ops = []
        try:
            while descendants.hasNext():
                ops.append(descendants.next())
        except Exception:
            return ()
        return tuple(ops)

    def _has_vector_countdown_loop(
        self,
        all_ops: Sequence[object],
        rounded_vn,
        *,
        lane_count: int,
    ) -> bool:
        for op in all_ops:
            if getattr(op, "getMnemonic", lambda: None)() != "MULTIEQUAL":
                continue
            phi_output = getattr(op, "getOutput", lambda: None)()
            if phi_output is None:
                continue
            has_init = False
            input_count = int(getattr(op, "getNumInputs", lambda: 0)() or 0)
            for index in range(input_count):
                if self._same_varnode_value(self._follow_passthrough_varnode(op.getInput(index)), rounded_vn):
                    has_init = True
                    break
            if not has_init:
                continue
            if self._index_phi_has_step(all_ops, phi_output, -int(lane_count)):
                return True
        return False

    def _index_phi_has_step(
        self,
        all_ops: Sequence[object],
        phi_output,
        step: int,
    ) -> bool:
        for op in all_ops:
            mnemonic = getattr(op, "getMnemonic", lambda: None)()
            if mnemonic not in {"INT_ADD", "INT_SUB"}:
                continue
            if int(getattr(op, "getNumInputs", lambda: 0)() or 0) < 2:
                continue
            left = self._follow_passthrough_varnode(op.getInput(0))
            right = self._follow_passthrough_varnode(op.getInput(1))
            constant = self._signed_varnode_constant_value(right)
            if self._same_varnode_value(left, phi_output) and constant is not None:
                actual = int(constant) if mnemonic == "INT_ADD" else -int(constant)
                if actual == int(step):
                    return True
            constant = self._signed_varnode_constant_value(left)
            if mnemonic == "INT_ADD" and self._same_varnode_value(right, phi_output) and constant is not None:
                if int(constant) == int(step):
                    return True
        return False

    def _has_vector_loop_bound_to_rounded_count(
        self,
        all_ops: Sequence[object],
        pointer_phi,
        pointer_param: dict,
        rounded_vn,
        *,
        element_size: int,
        base_offset: int,
        vector_stride: int,
    ) -> bool:
        """Prove a vector cursor stops at ``base + rounded_count * elem``.

        Clang/LLVM often emits a pointer-induction vector loop instead of a
        separate countdown induction.  This keeps the recognition object-centric:
        the proof is over Ghidra varnodes and P-code def-use links, not textual
        decompiler output.
        """

        compare_ops = {
            "INT_EQUAL",
            "INT_NOTEQUAL",
            "INT_LESS",
            "INT_LESSEQUAL",
            "INT_SLESS",
            "INT_SLESSEQUAL",
        }
        for op in all_ops:
            if getattr(op, "getMnemonic", lambda: None)() not in compare_ops:
                continue
            if int(getattr(op, "getNumInputs", lambda: 0)() or 0) < 2:
                continue
            left = self._follow_passthrough_varnode(op.getInput(0))
            right = self._follow_passthrough_varnode(op.getInput(1))
            if self._vector_cursor_matches_end_bound(
                left,
                right,
                pointer_phi,
                pointer_param,
                rounded_vn,
                element_size=element_size,
                base_offset=base_offset,
                vector_stride=vector_stride,
            ):
                return True
            if self._vector_cursor_matches_end_bound(
                right,
                left,
                pointer_phi,
                pointer_param,
                rounded_vn,
                element_size=element_size,
                base_offset=base_offset,
                vector_stride=vector_stride,
            ):
                return True
        return False

    def _vector_cursor_matches_end_bound(
        self,
        cursor_vn,
        end_vn,
        pointer_phi,
        pointer_param: dict,
        rounded_vn,
        *,
        element_size: int,
        base_offset: int,
        vector_stride: int,
    ) -> bool:
        cursor_offset = self._byte_offset_from_pointer_like(cursor_vn, pointer_phi)
        if cursor_offset is None:
            return False
        if int(cursor_offset) not in {0, int(vector_stride)}:
            return False
        return self._varnode_is_base_plus_scaled_counter(
            end_vn,
            pointer_param,
            rounded_vn,
            element_size=element_size,
            byte_offset=int(base_offset) + int(cursor_offset),
        )

    def _has_scalar_tail_from_rounded_count(
        self,
        all_ops: Sequence[object],
        pointer_param: dict,
        count_param: dict,
        rounded_vn,
        *,
        element_size: int,
    ) -> bool:
        tail_starts = self._tail_start_varnodes_from_rounded_count(
            all_ops,
            pointer_param,
            rounded_vn,
            element_size=element_size,
        )
        if not tail_starts:
            return False

        for op in all_ops:
            if getattr(op, "getMnemonic", lambda: None)() != "MULTIEQUAL":
                continue
            phi_output = getattr(op, "getOutput", lambda: None)()
            if phi_output is None:
                continue
            input_count = int(getattr(op, "getNumInputs", lambda: 0)() or 0)
            if not any(
                any(
                    self._same_varnode_value(self._follow_passthrough_varnode(op.getInput(index)), tail_start)
                    for tail_start in tail_starts
                )
                for index in range(input_count)
            ):
                continue
            if not self._phi_has_pointer_step(all_ops, phi_output, step_bytes=int(element_size)):
                continue
            if not self._tail_load_contributes_additively_to_return(
                all_ops,
                phi_output,
                element_size=element_size,
            ):
                continue
            if not (
                self._has_scalar_tail_bound_to_count(
                    all_ops,
                    phi_output,
                    pointer_param,
                    count_param,
                    element_size=element_size,
                )
                or self._has_scalar_tail_countdown_from_count_minus_rounded(
                    all_ops,
                    rounded_vn,
                    count_param,
                )
            ):
                continue
            return True
        return False

    def _tail_load_contributes_additively_to_return(
        self,
        all_ops: Sequence[object],
        tail_phi,
        *,
        element_size: int,
    ) -> bool:
        for load_op in all_ops:
            if getattr(load_op, "getMnemonic", lambda: None)() != "LOAD":
                continue
            if int(getattr(load_op, "getNumInputs", lambda: 0)() or 0) < 2:
                continue
            address = self._follow_passthrough_varnode(load_op.getInput(1))
            if not self._same_varnode_value(address, tail_phi):
                continue
            output = getattr(load_op, "getOutput", lambda: None)()
            if output is None:
                continue
            load_size = max(1, int(getattr(output, "getSize", lambda: element_size)() or element_size))
            if load_size != int(element_size):
                continue
            if self._load_lanes_flow_additively_to_return(
                output,
                load_size=load_size,
                element_size=element_size,
            ):
                return True
        return False

    def _tail_start_varnodes_from_rounded_count(
        self,
        all_ops: Sequence[object],
        pointer_param: dict,
        rounded_vn,
        *,
        element_size: int,
    ) -> Tuple[object, ...]:
        starts: List[object] = []
        for op in all_ops:
            output = getattr(op, "getOutput", lambda: None)()
            if output is None:
                continue
            if self._varnode_is_base_plus_scaled_counter(
                output,
                pointer_param,
                rounded_vn,
                element_size=element_size,
                byte_offset=0,
            ):
                starts.append(output)
        return tuple(starts)

    def _has_scalar_tail_bound_to_count(
        self,
        all_ops: Sequence[object],
        tail_phi,
        pointer_param: dict,
        count_param: dict,
        *,
        element_size: int,
    ) -> bool:
        compare_ops = {
            "INT_EQUAL",
            "INT_NOTEQUAL",
            "INT_LESS",
            "INT_LESSEQUAL",
            "INT_SLESS",
            "INT_SLESSEQUAL",
        }
        for op in all_ops:
            if getattr(op, "getMnemonic", lambda: None)() not in compare_ops:
                continue
            if int(getattr(op, "getNumInputs", lambda: 0)() or 0) < 2:
                continue
            left = self._follow_passthrough_varnode(op.getInput(0))
            right = self._follow_passthrough_varnode(op.getInput(1))
            if self._scalar_tail_cursor_matches_count_bound(
                left,
                right,
                tail_phi,
                pointer_param,
                count_param,
                element_size=element_size,
            ):
                return True
            if self._scalar_tail_cursor_matches_count_bound(
                right,
                left,
                tail_phi,
                pointer_param,
                count_param,
                element_size=element_size,
            ):
                return True
        return False

    def _has_scalar_tail_countdown_from_count_minus_rounded(
        self,
        all_ops: Sequence[object],
        rounded_vn,
        count_param: dict,
    ) -> bool:
        """Recognize tail loops controlled by ``remaining = count - rounded``."""

        for op in all_ops:
            if getattr(op, "getMnemonic", lambda: None)() != "MULTIEQUAL":
                continue
            phi_output = getattr(op, "getOutput", lambda: None)()
            if phi_output is None:
                continue
            input_count = int(getattr(op, "getNumInputs", lambda: 0)() or 0)
            has_count_minus_rounded_init = any(
                self._varnode_is_count_minus_rounded(
                    self._follow_passthrough_varnode(op.getInput(index)),
                    count_param,
                    rounded_vn,
                )
                for index in range(input_count)
            )
            if not has_count_minus_rounded_init:
                continue
            if self._index_phi_has_step(all_ops, phi_output, -1):
                return True
        return False

    def _varnode_is_count_minus_rounded(
        self,
        candidate_vn,
        count_param: dict,
        rounded_vn,
    ) -> bool:
        candidate_vn = self._follow_passthrough_varnode(candidate_vn)
        def_op = getattr(candidate_vn, "getDef", lambda: None)()
        if def_op is None or getattr(def_op, "getMnemonic", lambda: None)() != "INT_SUB":
            return False
        if int(getattr(def_op, "getNumInputs", lambda: 0)() or 0) < 2:
            return False
        left = self._follow_passthrough_varnode(def_op.getInput(0))
        right = self._follow_passthrough_varnode(def_op.getInput(1))
        return (
            self._varnode_matches_parameter(left, count_param.get("name", ""))
            and self._same_varnode_value(right, rounded_vn)
        )

    def _scalar_tail_cursor_matches_count_bound(
        self,
        cursor_vn,
        end_vn,
        tail_phi,
        pointer_param: dict,
        count_param: dict,
        *,
        element_size: int,
    ) -> bool:
        cursor_offset = self._byte_offset_from_pointer_like(cursor_vn, tail_phi)
        if cursor_offset is None:
            return False
        if int(cursor_offset) not in {0, int(element_size)}:
            return False
        return self._varnode_is_base_plus_scaled_parameter(
            end_vn,
            pointer_param,
            count_param,
            element_size=element_size,
            byte_offset=int(cursor_offset),
        )

    def _byte_offset_from_pointer_like(self, candidate_vn, base_vn) -> Optional[int]:
        candidate_vn = self._follow_passthrough_varnode(candidate_vn)
        if self._same_varnode_value(candidate_vn, base_vn):
            return 0
        offset = self._byte_offset_from_pointer(candidate_vn, base_vn)
        if offset is not None:
            return int(offset)
        def_op = getattr(candidate_vn, "getDef", lambda: None)()
        if def_op is None:
            return None
        mnemonic = getattr(def_op, "getMnemonic", lambda: None)()
        if mnemonic not in {"INT_ADD", "PTRSUB"} or int(getattr(def_op, "getNumInputs", lambda: 0)() or 0) < 2:
            return None
        left = self._follow_passthrough_varnode(def_op.getInput(0))
        right = self._follow_passthrough_varnode(def_op.getInput(1))
        if self._same_varnode_value(left, base_vn):
            return self._signed_varnode_constant_value(right)
        if mnemonic == "INT_ADD" and self._same_varnode_value(right, base_vn):
            return self._signed_varnode_constant_value(left)
        return None

    def _varnode_is_base_plus_scaled_parameter(
        self,
        candidate_vn,
        pointer_param: dict,
        count_param: dict,
        *,
        element_size: int,
        byte_offset: int,
    ) -> bool:
        candidate_vn = self._follow_passthrough_varnode(candidate_vn)
        def_op = getattr(candidate_vn, "getDef", lambda: None)()
        if def_op is None:
            return False
        mnemonic = getattr(def_op, "getMnemonic", lambda: None)()
        if mnemonic == "PTRADD" and int(getattr(def_op, "getNumInputs", lambda: 0)() or 0) >= 3:
            base = self._follow_passthrough_varnode(def_op.getInput(0))
            index = self._follow_passthrough_varnode(def_op.getInput(1))
            elem = self._varnode_unsigned_constant_value(self._follow_passthrough_varnode(def_op.getInput(2)))
            if (
                elem == int(element_size)
                and self._varnode_matches_parameter(base, pointer_param.get("name", ""))
                and self._varnode_matches_parameter(index, count_param.get("name", ""))
                and int(byte_offset) == 0
            ):
                return True
        scaled_count = self._scaled_parameter_varnode(candidate_vn, count_param, element_size=element_size)
        if scaled_count is not None and self._varnode_matches_parameter(scaled_count, pointer_param.get("name", "")):
            return int(byte_offset) == 0
        if mnemonic in {"INT_ADD", "PTRSUB"} and int(getattr(def_op, "getNumInputs", lambda: 0)() or 0) >= 2:
            left = self._follow_passthrough_varnode(def_op.getInput(0))
            right = self._follow_passthrough_varnode(def_op.getInput(1))
            left_const = self._signed_varnode_constant_value(left)
            right_const = self._signed_varnode_constant_value(right)
            if right_const == int(byte_offset):
                return self._varnode_is_base_plus_scaled_parameter(
                    left,
                    pointer_param,
                    count_param,
                    element_size=element_size,
                    byte_offset=0,
                )
            if mnemonic == "INT_ADD" and left_const == int(byte_offset):
                return self._varnode_is_base_plus_scaled_parameter(
                    right,
                    pointer_param,
                    count_param,
                    element_size=element_size,
                    byte_offset=0,
                )
            if self._varnode_matches_parameter(left, pointer_param.get("name", "")):
                return self._varnode_is_scaled_parameter_plus_constant(
                    right,
                    count_param,
                    element_size=element_size,
                    byte_offset=byte_offset,
                )
            if mnemonic == "INT_ADD" and self._varnode_matches_parameter(right, pointer_param.get("name", "")):
                return self._varnode_is_scaled_parameter_plus_constant(
                    left,
                    count_param,
                    element_size=element_size,
                    byte_offset=byte_offset,
                )
        return False

    def _varnode_is_base_plus_scaled_counter(
        self,
        candidate_vn,
        pointer_param: dict,
        counter_vn,
        *,
        element_size: int,
        byte_offset: int,
    ) -> bool:
        candidate_vn = self._follow_passthrough_varnode(candidate_vn)
        def_op = getattr(candidate_vn, "getDef", lambda: None)()
        if def_op is None:
            return False
        mnemonic = getattr(def_op, "getMnemonic", lambda: None)()
        if mnemonic == "PTRADD" and int(getattr(def_op, "getNumInputs", lambda: 0)() or 0) >= 3:
            base = self._follow_passthrough_varnode(def_op.getInput(0))
            index = self._follow_passthrough_varnode(def_op.getInput(1))
            elem = self._varnode_unsigned_constant_value(self._follow_passthrough_varnode(def_op.getInput(2)))
            if (
                elem == int(element_size)
                and self._varnode_matches_parameter(base, pointer_param.get("name", ""))
                and self._same_varnode_value(index, counter_vn)
                and int(byte_offset) == 0
            ):
                return True
        if mnemonic in {"INT_ADD", "PTRSUB"} and int(getattr(def_op, "getNumInputs", lambda: 0)() or 0) >= 2:
            left = self._follow_passthrough_varnode(def_op.getInput(0))
            right = self._follow_passthrough_varnode(def_op.getInput(1))
            left_const = self._signed_varnode_constant_value(left)
            right_const = self._signed_varnode_constant_value(right)
            if right_const == int(byte_offset):
                return self._varnode_is_base_plus_scaled_counter(
                    left,
                    pointer_param,
                    counter_vn,
                    element_size=element_size,
                    byte_offset=0,
                )
            if mnemonic == "INT_ADD" and left_const == int(byte_offset):
                return self._varnode_is_base_plus_scaled_counter(
                    right,
                    pointer_param,
                    counter_vn,
                    element_size=element_size,
                    byte_offset=0,
                )
            if self._varnode_matches_parameter(left, pointer_param.get("name", "")):
                return self._varnode_is_scaled_counter_plus_constant(
                    right,
                    counter_vn,
                    element_size=element_size,
                    byte_offset=byte_offset,
                )
            if mnemonic == "INT_ADD" and self._varnode_matches_parameter(right, pointer_param.get("name", "")):
                return self._varnode_is_scaled_counter_plus_constant(
                    left,
                    counter_vn,
                    element_size=element_size,
                    byte_offset=byte_offset,
                )
        return False

    def _varnode_is_scaled_parameter_plus_constant(
        self,
        candidate_vn,
        count_param: dict,
        *,
        element_size: int,
        byte_offset: int,
    ) -> bool:
        candidate_vn = self._follow_passthrough_varnode(candidate_vn)
        if int(byte_offset) == 0 and self._scaled_parameter_varnode(candidate_vn, count_param, element_size=element_size) is not None:
            return True
        def_op = getattr(candidate_vn, "getDef", lambda: None)()
        if def_op is None or getattr(def_op, "getMnemonic", lambda: None)() != "INT_ADD":
            return False
        if int(getattr(def_op, "getNumInputs", lambda: 0)() or 0) < 2:
            return False
        left = self._follow_passthrough_varnode(def_op.getInput(0))
        right = self._follow_passthrough_varnode(def_op.getInput(1))
        left_const = self._signed_varnode_constant_value(left)
        right_const = self._signed_varnode_constant_value(right)
        if left_const == int(byte_offset):
            return self._scaled_parameter_varnode(right, count_param, element_size=element_size) is not None
        if right_const == int(byte_offset):
            return self._scaled_parameter_varnode(left, count_param, element_size=element_size) is not None
        return False

    def _varnode_is_scaled_counter_plus_constant(
        self,
        candidate_vn,
        counter_vn,
        *,
        element_size: int,
        byte_offset: int,
    ) -> bool:
        candidate_vn = self._follow_passthrough_varnode(candidate_vn)
        if int(byte_offset) == 0 and self._varnode_is_scaled_counter(candidate_vn, counter_vn, element_size=element_size):
            return True
        def_op = getattr(candidate_vn, "getDef", lambda: None)()
        if def_op is None or getattr(def_op, "getMnemonic", lambda: None)() != "INT_ADD":
            return False
        if int(getattr(def_op, "getNumInputs", lambda: 0)() or 0) < 2:
            return False
        left = self._follow_passthrough_varnode(def_op.getInput(0))
        right = self._follow_passthrough_varnode(def_op.getInput(1))
        left_const = self._signed_varnode_constant_value(left)
        right_const = self._signed_varnode_constant_value(right)
        if left_const == int(byte_offset):
            return self._varnode_is_scaled_counter(right, counter_vn, element_size=element_size)
        if right_const == int(byte_offset):
            return self._varnode_is_scaled_counter(left, counter_vn, element_size=element_size)
        return False

    def _scaled_parameter_varnode(
        self,
        candidate_vn,
        count_param: dict,
        *,
        element_size: int,
    ):
        candidate_vn = self._follow_passthrough_varnode(candidate_vn)
        def_op = getattr(candidate_vn, "getDef", lambda: None)()
        if def_op is None:
            return None
        mnemonic = getattr(def_op, "getMnemonic", lambda: None)()
        if mnemonic == "INT_MULT" and int(getattr(def_op, "getNumInputs", lambda: 0)() or 0) >= 2:
            left = self._follow_passthrough_varnode(def_op.getInput(0))
            right = self._follow_passthrough_varnode(def_op.getInput(1))
            if self._varnode_matches_parameter(left, count_param.get("name", "")) and self._varnode_unsigned_constant_value(right) == int(element_size):
                return left
            if self._varnode_matches_parameter(right, count_param.get("name", "")) and self._varnode_unsigned_constant_value(left) == int(element_size):
                return right
        if mnemonic == "INT_LEFT" and int(getattr(def_op, "getNumInputs", lambda: 0)() or 0) >= 2:
            shifted = self._follow_passthrough_varnode(def_op.getInput(0))
            shift_bits = self._varnode_unsigned_constant_value(self._follow_passthrough_varnode(def_op.getInput(1)))
            if (
                shift_bits is not None
                and (1 << int(shift_bits)) == int(element_size)
                and self._varnode_matches_parameter(shifted, count_param.get("name", ""))
            ):
                return shifted
        return None

    def _varnode_is_scaled_counter(
        self,
        candidate_vn,
        counter_vn,
        *,
        element_size: int,
    ) -> bool:
        candidate_vn = self._follow_passthrough_varnode(candidate_vn)
        def_op = getattr(candidate_vn, "getDef", lambda: None)()
        if def_op is None:
            return False
        mnemonic = getattr(def_op, "getMnemonic", lambda: None)()
        if mnemonic == "INT_MULT" and int(getattr(def_op, "getNumInputs", lambda: 0)() or 0) >= 2:
            left = self._follow_passthrough_varnode(def_op.getInput(0))
            right = self._follow_passthrough_varnode(def_op.getInput(1))
            return (
                self._same_varnode_value(left, counter_vn)
                and self._varnode_unsigned_constant_value(right) == int(element_size)
            ) or (
                self._same_varnode_value(right, counter_vn)
                and self._varnode_unsigned_constant_value(left) == int(element_size)
            )
        if mnemonic == "INT_LEFT" and int(getattr(def_op, "getNumInputs", lambda: 0)() or 0) >= 2:
            shifted = self._follow_passthrough_varnode(def_op.getInput(0))
            shift_bits = self._varnode_unsigned_constant_value(self._follow_passthrough_varnode(def_op.getInput(1)))
            return (
                shift_bits is not None
                and (1 << int(shift_bits)) == int(element_size)
                and self._same_varnode_value(shifted, counter_vn)
            )
        return False

    def _analysis_mentions_parameter_in_conditions(
        self,
        analysis,
        param_name: str,
    ) -> bool:
        if not param_name:
            return False
        for ret in analysis.returns or []:
            for condition in ret.conditions or []:
                relation = self._condition_relation(condition, param_name)
                if relation is not None:
                    return True
                relation = self._parameter_comparison_relation(condition)
                if relation is not None and param_name in relation[:3:2]:
                    return True
        return False

    def _build_readonly_reduction_semantic_witnesses(
        self,
        analysis,
        pointer_param: dict,
        count_param: dict,
        positive_returns: Sequence[ReturnInfo],
        accumulator_proof: ReductionAccumulatorProof,
        *,
        result_size: int,
    ) -> Tuple[ReadonlyReductionWitness, ...]:
        exact_witnesses = self._extract_readonly_reduction_exact_witnesses(
            analysis,
            pointer_param,
            count_param,
            positive_returns,
            accumulator_proof,
        )
        witness_proof = accumulator_proof.with_runtime_evidence(
            limit_expr=accumulator_proof.limit_expr,
            result_size=result_size,
            loop_body_witnesses=tuple(exact_witnesses),
            exact_return_witnesses=tuple(exact_witnesses),
            guard_constraints=tuple(accumulator_proof.guard_constraints or ()),
            signed_counter=bool(accumulator_proof.signed_counter),
        )
        loop_body_exact_witnesses = []
        for witness in exact_witnesses:
            expected_terms = witness_proof.loop_body_terms_for_count_value(int(witness.exact_count))
            if expected_terms is None:
                continue
            if tuple(term.stable_key() for term in witness.terms) == tuple(
                term.stable_key() for term in expected_terms
            ):
                loop_body_exact_witnesses.append(witness)
        synthesized_witnesses = self._synthesize_linear_readonly_reduction_witnesses(
            pointer_param,
            witness_proof,
            result_size=result_size,
        )
        if not loop_body_exact_witnesses:
            return synthesized_witnesses
        if not synthesized_witnesses:
            return tuple(loop_body_exact_witnesses)

        exact_by_count = {
            int(witness.exact_count): witness
            for witness in loop_body_exact_witnesses
        }
        synthesized_by_count = {
            int(witness.exact_count): witness
            for witness in synthesized_witnesses
        }
        overlap = set(exact_by_count) & set(synthesized_by_count)
        for exact_count in sorted(overlap):
            if exact_by_count[exact_count].stable_key() != synthesized_by_count[exact_count].stable_key():
                return exact_witnesses

        merged = dict(synthesized_by_count)
        merged.update(exact_by_count)
        return tuple(merged[count] for count in sorted(merged))

    def _extract_readonly_reduction_exact_witnesses(
        self,
        analysis,
        pointer_param: dict,
        count_param: dict,
        positive_returns: Sequence[ReturnInfo],
        accumulator_proof: Optional[ReductionAccumulatorProof] = None,
    ) -> Tuple[ReadonlyReductionWitness, ...]:
        count_name = str(count_param.get("name") or "")
        witness_by_count: Dict[int, ReadonlyReductionWitness] = {}
        for ret in positive_returns or []:
            exact_count = self._exact_counter_value_from_conditions(ret.conditions or [], count_name)
            reduced_value = _reduce_expression_under_conditions(ret.value, ret.conditions or [])
            terms = self._extract_readonly_reduction_terms(
                reduced_value,
                analysis.parameters or [],
                pointer_param,
            )
            if terms is None and reduced_value is not ret.value:
                terms = self._extract_readonly_reduction_terms(
                    ret.value,
                    analysis.parameters or [],
                    pointer_param,
                )
            if terms is not None and (exact_count is None or exact_count <= 0):
                exact_count = self._infer_exact_count_from_readonly_terms(
                    ret.conditions or [],
                    terms,
                    count_param,
                    accumulator_proof,
                )
            if exact_count is None or exact_count <= 0:
                self._debug("Skipped readonly exact-return witness: no exact positive counter value")
                continue
            expected_terms = (
                accumulator_proof.full_terms_for_count_value(int(exact_count))
                if accumulator_proof is not None
                else None
            )
            if expected_terms is None:
                expected_trip_count = self._readonly_loop_trip_count_for_count_value(accumulator_proof, int(exact_count))
                if expected_trip_count is None:
                    self._debug(
                        "Skipped readonly exact-return witness: "
                        f"no expected term model for count={exact_count}"
                    )
                    continue
            else:
                expected_trip_count = len(expected_terms)
            if expected_trip_count is None:
                continue
            if terms is None or len(terms) != int(expected_trip_count):
                self._debug(
                    "Skipped readonly exact-return witness: "
                    f"term extraction/count mismatch for count={exact_count}"
                )
                continue
            if expected_terms is not None and tuple(term.stable_key() for term in terms) != tuple(
                term.stable_key() for term in expected_terms
            ):
                self._debug(
                    "Skipped readonly exact-return witness: "
                    f"terms do not match accumulator proof for count={exact_count}"
                )
                continue
            witness = ReadonlyReductionWitness(
                exact_count=int(exact_count),
                terms=tuple(terms),
            )
            existing = witness_by_count.get(int(exact_count))
            if existing is None or existing.stable_key() == witness.stable_key():
                witness_by_count[int(exact_count)] = witness
        if not witness_by_count:
            return ()
        return tuple(witness_by_count[count] for count in sorted(witness_by_count))

    def _infer_exact_count_from_readonly_terms(
        self,
        conditions: Sequence[Condition],
        terms: Sequence[ReadonlyReductionTermRef],
        count_param: dict,
        accumulator_proof: Optional[ReductionAccumulatorProof],
    ) -> Optional[int]:
        if accumulator_proof is None or not terms:
            return None
        term_key = tuple(term.stable_key() for term in terms)
        max_count = max(
            int(accumulator_proof.start_index),
            len(tuple(accumulator_proof.seed_terms or ())),
            1,
        )
        for count_value in range(1, max_count + 1):
            expected_terms = accumulator_proof.full_terms_for_count_value(count_value)
            if expected_terms is None:
                continue
            if term_key != tuple(term.stable_key() for term in expected_terms):
                continue
            if self._conditions_imply_counter_value(conditions, count_param, count_value):
                return count_value
        return None

    def _conditions_imply_counter_value(
        self,
        conditions: Sequence[Condition],
        count_param: dict,
        count_value: int,
    ) -> bool:
        count_expr = self._parameter_expression(count_param)
        equality = Condition(
            Expression.binary_op(
                "INT_EQUAL",
                count_expr,
                Expression.constant(int(count_value), count_expr.size or 4),
            ),
            False,
        )
        return ConditionSimplifier.object_centric_is_contradiction(
            list(conditions or []) + [equality.negate()]
        )

    def _readonly_loop_trip_count_for_count_value(
        self,
        accumulator_proof: Optional[ReductionAccumulatorProof],
        count_value: int,
    ) -> Optional[int]:
        if count_value <= 0:
            return None
        if accumulator_proof is None:
            return int(count_value)
        return accumulator_proof.trip_count_for_count_value(count_value)

    def _synthesize_linear_readonly_reduction_witnesses(
        self,
        pointer_param: dict,
        accumulator_proof: Optional[ReductionAccumulatorProof],
        *,
        result_size: int,
    ) -> Tuple[ReadonlyReductionWitness, ...]:
        if accumulator_proof is None:
            return ()
        stride = int(accumulator_proof.stride)
        element_size = int(accumulator_proof.element_size)
        start_index = int(accumulator_proof.start_index)
        index_step = int(accumulator_proof.index_step)
        access_size = max(1, int(result_size or 0))
        if stride <= 0 or element_size <= 0 or element_size != access_size or index_step <= 0:
            return ()
        witnesses: List[ReadonlyReductionWitness] = []
        max_count = max(4, start_index + min(index_step * 2, 32) + 1)
        for exact_count in range(1, max_count + 1):
            terms = accumulator_proof.loop_body_terms_for_count_value(exact_count)
            if terms is None:
                continue
            witnesses.append(
                ReadonlyReductionWitness(
                    exact_count=exact_count,
                    terms=terms,
                )
            )
        return tuple(witnesses)

    def _extract_readonly_reduction_terms(
        self,
        expr: Optional[Expression],
        parameters: Sequence[dict],
        pointer_param: dict,
    ) -> Optional[List[ReadonlyReductionTermRef]]:
        if expr is None:
            return None
        big_endian = self._program_is_big_endian()
        extracted: List[ReadonlyReductionTermRef] = []
        for sign, term in self._flatten_add_terms(expr):
            if term.expr_type == ExpressionType.CONSTANT:
                value = self._raw_constant_value(term)
                if value is None or int(value) != 0:
                    return None
                continue
            if sign != 1:
                return None
            descriptor = self._extract_readonly_reduction_term_descriptor(
                term,
                parameters,
                pointer_param,
                big_endian=big_endian,
            )
            if descriptor is None:
                return None
            extracted.append(descriptor)
        if not extracted:
            return None
        extracted.sort(key=lambda item: (int(item.byte_offset), int(item.access_size)))
        return extracted

    def _extract_readonly_reduction_term_descriptor(
        self,
        expr: Optional[Expression],
        parameters: Sequence[dict],
        pointer_param: dict,
        *,
        big_endian: bool,
        lsb_byte_offset: int = 0,
        narrowed_size: Optional[int] = None,
    ) -> Optional[ReadonlyReductionTermRef]:
        if expr is None:
            return None

        if expr.expr_type == ExpressionType.UNARY_OP and expr.operands:
            if expr.operator == "INT_SEXT":
                return None
            if expr.operator in {"INT_ZEXT", "CAST", "COPY"}:
                return self._extract_readonly_reduction_term_descriptor(
                    expr.operands[0],
                    parameters,
                    pointer_param,
                    big_endian=big_endian,
                    lsb_byte_offset=lsb_byte_offset,
                    narrowed_size=narrowed_size,
                )

        if expr.expr_type == ExpressionType.BINARY_OP and len(expr.operands) == 2:
            if expr.operator == "SUBPIECE":
                byte_offset = self._raw_constant_value(expr.operands[1])
                if byte_offset is None or byte_offset < 0:
                    return None
                return self._extract_readonly_reduction_term_descriptor(
                    expr.operands[0],
                    parameters,
                    pointer_param,
                    big_endian=big_endian,
                    lsb_byte_offset=lsb_byte_offset + int(byte_offset),
                    narrowed_size=max(1, int(expr.size or 0)),
                )
            if expr.operator == "INT_RIGHT":
                shift_bits = self._raw_constant_value(expr.operands[1])
                if shift_bits is None or shift_bits < 0 or (int(shift_bits) % 8) != 0:
                    return None
                return self._extract_readonly_reduction_term_descriptor(
                    expr.operands[0],
                    parameters,
                    pointer_param,
                    big_endian=big_endian,
                    lsb_byte_offset=lsb_byte_offset + (int(shift_bits) // 8),
                    narrowed_size=narrowed_size or max(1, int(expr.size or 0)),
                )
            if expr.operator == "INT_AND":
                mask_width = self._low_mask_width_bytes(expr.operands[0], expr.operands[1])
                if mask_width is None:
                    mask_width = self._low_mask_width_bytes(expr.operands[1], expr.operands[0])
                if mask_width is not None:
                    return self._extract_readonly_reduction_term_descriptor(
                        expr.operands[0] if expr.operands[0].expr_type != ExpressionType.CONSTANT else expr.operands[1],
                        parameters,
                        pointer_param,
                        big_endian=big_endian,
                        lsb_byte_offset=lsb_byte_offset,
                        narrowed_size=narrowed_size or mask_width,
                    )

        if expr.expr_type != ExpressionType.MEMORY or not expr.operands:
            return None

        load_size = max(1, int(expr.size or 0))
        access_size = max(1, int(narrowed_size or load_size))
        if lsb_byte_offset < 0 or access_size > load_size or lsb_byte_offset + access_size > load_size:
            return None
        location = canonicalize_location(expr.operands[0], parameters, size=load_size)
        if location is None or not location.base_ref.matches_parameter(pointer_param):
            return None
        if big_endian:
            byte_offset = int(location.offset) + (load_size - access_size - int(lsb_byte_offset))
        else:
            byte_offset = int(location.offset) + int(lsb_byte_offset)
        return ReadonlyReductionTermRef(
            byte_offset=byte_offset,
            access_size=access_size,
        )

    def _low_mask_width_bytes(
        self,
        value_expr: Optional[Expression],
        mask_expr: Optional[Expression],
    ) -> Optional[int]:
        if value_expr is None or mask_expr is None:
            return None
        mask_value = self._raw_constant_value(mask_expr)
        value_size = max(1, int(getattr(value_expr, "size", 0) or 0))
        if mask_value is None or mask_value < 0:
            return None
        full_mask = (1 << (value_size * 8)) - 1
        mask_value = int(mask_value) & full_mask
        for width in range(1, value_size + 1):
            if mask_value == ((1 << (width * 8)) - 1):
                return width
        return None

    def _program_is_big_endian(self) -> bool:
        program = getattr(self.tracer, "program", None)
        if program is None:
            return False
        language_getter = getattr(program, "getLanguage", None)
        if not callable(language_getter):
            return False
        language = language_getter()
        is_big_endian = getattr(language, "isBigEndian", None)
        if not callable(is_big_endian):
            return False
        try:
            return bool(is_big_endian())
        except Exception:
            return False

    def _match_pointer_progression_phi(
        self,
        phi_op,
        pointer_param: dict,
    ) -> Optional[Dict[str, object]]:
        output = getattr(phi_op, "getOutput", lambda: None)()
        if output is None:
            return None

        input_count = int(getattr(phi_op, "getNumInputs", lambda: 0)() or 0)
        for init_index in range(input_count):
            init_varnode = self._follow_passthrough_varnode(phi_op.getInput(init_index))
            if not self._varnode_matches_parameter(init_varnode, pointer_param.get("name", "")):
                continue
            for back_index in range(input_count):
                if back_index == init_index:
                    continue
                back_varnode = self._follow_passthrough_varnode(phi_op.getInput(back_index))
                step = self._extract_pointer_step(back_varnode, output)
                if step is None or step <= 0:
                    continue
                return {
                    "phi_op": phi_op,
                    "phi_output": output,
                    "stride": int(step),
                    "start_offset": 0,
                    "start_index": 0,
                    "index_step": 1,
                    "index_scale": int(step),
                }
        return None

    def _match_index_progression_phi(
        self,
        phi_op,
    ) -> Optional[Dict[str, object]]:
        output = getattr(phi_op, "getOutput", lambda: None)()
        if output is None:
            return None

        input_count = int(getattr(phi_op, "getNumInputs", lambda: 0)() or 0)
        for init_index in range(input_count):
            init_varnode = self._follow_passthrough_varnode(phi_op.getInput(init_index))
            init_value = self._varnode_constant_value(init_varnode)
            if init_value is None:
                continue
            for back_index in range(input_count):
                if back_index == init_index:
                    continue
                back_varnode = self._follow_passthrough_varnode(phi_op.getInput(back_index))
                step = self._extract_index_step(back_varnode, output)
                if step is not None and step > 0:
                    return {
                        "phi_op": phi_op,
                        "phi_output": output,
                        "start": int(init_value),
                        "step": int(step),
                    }
        return None

    def _match_accumulator_phi(
        self,
        phi_op,
        pointer_param: dict,
        count_param: dict,
        pointer_base_ref: LocationBaseRef,
        count_expr: Expression,
        pointer_phis: Sequence[Dict[str, object]],
        index_phis: Sequence[Dict[str, object]],
        *,
        result_size: int,
        positive_conditions: Sequence[Condition] = (),
    ) -> Optional[ReductionAccumulatorProof]:
        output = getattr(phi_op, "getOutput", lambda: None)()
        if output is None:
            return None

        input_count = int(getattr(phi_op, "getNumInputs", lambda: 0)() or 0)
        for init_index in range(input_count):
            init_varnode = self._follow_passthrough_varnode(phi_op.getInput(init_index))
            for back_index in range(input_count):
                if back_index == init_index:
                    continue
                back_varnode = self._follow_passthrough_varnode(phi_op.getInput(back_index))
                back_def = getattr(back_varnode, "getDef", lambda: None)()
                if back_def is None or getattr(back_def, "getMnemonic", lambda: None)() != "INT_ADD":
                    continue
                input0 = self._follow_passthrough_varnode(back_def.getInput(0))
                input1 = self._follow_passthrough_varnode(back_def.getInput(1))
                if self._same_varnode_value(input0, output):
                    addend_varnode = input1
                elif self._same_varnode_value(input1, output):
                    addend_varnode = input0
                else:
                    continue
                load_progressions = self._collect_load_progressions_from_varnode(
                    addend_varnode,
                    pointer_param,
                    pointer_phis,
                    index_phis,
                )
                if load_progressions is None or not load_progressions:
                    continue
                first = load_progressions[0]
                if any(
                    signature["stride"] != first["stride"]
                    or signature["element_size"] != first["element_size"]
                    or signature.get("start_index", 0) != first.get("start_index", 0)
                    or signature.get("index_step", 1) != first.get("index_step", 1)
                    or signature.get("index_scale", signature["stride"]) != first.get("index_scale", first["stride"])
                    for signature in load_progressions[1:]
                ):
                    continue
                expanded_terms = self._readonly_load_progression_term_counter(
                    load_progressions,
                    result_size=max(1, int(result_size or first["element_size"])),
                )
                if expanded_terms is None or any(count != 1 for count in expanded_terms.values()):
                    continue
                proof_start_offset = int(first.get("start_offset", 0) or 0)
                lane_terms = set()
                if len(expanded_terms) > 1:
                    proof_start_offset = min(int(offset) for offset, _size in expanded_terms.keys())
                    lane_terms = {
                        (int(offset) - proof_start_offset, max(1, int(size or 0)))
                        for offset, size in expanded_terms.keys()
                    }
                seed_terms = self._extract_readonly_accumulator_seed_terms(
                    init_varnode,
                    pointer_param,
                    first,
                )
                if seed_terms is None:
                    continue
                load_op_refs = tuple(
                    ref for ref in (signature.get("load_op_ref") for signature in load_progressions)
                    if isinstance(ref, PcodeOpRef)
                )
                induction_phi_ref = next(
                    (
                        ref for ref in (signature.get("induction_phi_ref") for signature in load_progressions)
                        if isinstance(ref, PcodeOpRef)
                    ),
                    None,
                )
                return ReductionAccumulatorProof(
                    reduction_kind="memory_sum",
                    pointer_base_ref=pointer_base_ref,
                    count_parameter_name=count_param.get("name", "count"),
                    count_parameter_index=count_param.get("index"),
                    limit_expr=count_expr,
                    result_size=max(1, int(result_size or first["element_size"])),
                    stride=int(first["stride"]),
                    element_size=int(first["element_size"]),
                    start_offset=proof_start_offset,
                    start_index=int(first.get("start_index", 0) or 0),
                    index_step=int(first.get("index_step", 1) or 1),
                    index_scale=int(first.get("index_scale", first["stride"]) or first["stride"]),
                    signed_counter=bool(count_param.get("is_signed", True)),
                    seed_terms=tuple(seed_terms),
                    lane_terms=tuple(sorted(lane_terms)),
                    guard_constraints=tuple(positive_conditions or ()),
                    induction_phi_ref=induction_phi_ref,
                    accumulator_phi_ref=self._make_pcode_op_ref(phi_op),
                    update_op_ref=self._make_pcode_op_ref(back_def),
                    load_op_refs=load_op_refs,
                    entry_block_ref=self._make_pcode_block_ref(getattr(phi_op, "getParent", lambda: None)()),
                    backedge_block_ref=self._make_pcode_block_ref(getattr(back_def, "getParent", lambda: None)()),
                    source="recurrence_summary",
                )
        return None

    def _extract_readonly_accumulator_seed_terms(
        self,
        init_varnode,
        pointer_param: dict,
        load_signature: Dict[str, int],
    ) -> Optional[Tuple[ReadonlyReductionTermRef, ...]]:
        if self._varnode_constant_value(init_varnode) == 0:
            return ()

        expected = self._expected_readonly_prefix_seed_terms(load_signature)
        if not expected:
            return None

        init_expr = self._build_pcode_expression(init_varnode, placeholders={})
        if init_expr is None:
            init_expr = self._trace_varnode_expression(init_varnode)
        terms = self._extract_readonly_reduction_terms(
            init_expr,
            [pointer_param],
            pointer_param,
        )
        if terms is None:
            return None
        seed_terms = tuple(terms)
        if tuple(term.stable_key() for term in seed_terms) != tuple(term.stable_key() for term in expected):
            return None
        return seed_terms

    def _expected_readonly_prefix_seed_terms(
        self,
        load_signature: Dict[str, int],
    ) -> Tuple[ReadonlyReductionTermRef, ...]:
        start_index = int(load_signature.get("start_index", 0) or 0)
        index_step = int(load_signature.get("index_step", 1) or 1)
        index_scale = int(load_signature.get("index_scale", load_signature.get("stride", 0)) or 0)
        element_size = int(load_signature.get("element_size", 0) or 0)
        if start_index <= 0 or index_step <= 0 or index_scale <= 0 or element_size <= 0:
            return ()
        first_index = start_index % index_step
        if first_index == start_index:
            return ()
        return tuple(
            ReadonlyReductionTermRef(
                byte_offset=int(index * index_scale),
                access_size=element_size,
            )
            for index in range(first_index, start_index, index_step)
        )

    def _collect_load_progressions_from_varnode(
        self,
        varnode,
        pointer_param: dict,
        pointer_phis: Sequence[Dict[str, object]],
        index_phis: Sequence[Dict[str, object]],
        depth: int = 0,
        *,
        lsb_byte_offset: int = 0,
        narrowed_size: Optional[int] = None,
    ) -> Optional[List[Dict[str, object]]]:
        if varnode is None or depth > 8:
            return None
        varnode = self._follow_readonly_load_addend_passthrough(varnode)
        if self._varnode_constant_value(varnode) == 0:
            return []
        if self._varnode_constant_value(varnode) is not None:
            return None

        def_op = getattr(varnode, "getDef", lambda: None)()
        if def_op is None:
            return None
        mnemonic = getattr(def_op, "getMnemonic", lambda: None)()
        if mnemonic == "LOAD":
            signature = self._match_load_progression(
                def_op,
                pointer_param,
                pointer_phis,
                index_phis,
            )
            if signature is None:
                return None
            adjusted = self._adjust_readonly_load_signature_access(
                signature,
                lsb_byte_offset=int(lsb_byte_offset),
                narrowed_size=narrowed_size,
            )
            return [adjusted] if adjusted is not None else None
        if mnemonic == "INT_ADD":
            left = self._collect_load_progressions_from_varnode(
                def_op.getInput(0),
                pointer_param,
                pointer_phis,
                index_phis,
                depth + 1,
                lsb_byte_offset=lsb_byte_offset,
                narrowed_size=narrowed_size,
            )
            right = self._collect_load_progressions_from_varnode(
                def_op.getInput(1),
                pointer_param,
                pointer_phis,
                index_phis,
                depth + 1,
                lsb_byte_offset=lsb_byte_offset,
                narrowed_size=narrowed_size,
            )
            if left is None or right is None:
                return None
            return left + right
        if mnemonic == "INT_SEXT":
            return None
        if mnemonic in {"SUBPIECE", "INT_RIGHT", "INT_ZEXT", "CAST", "COPY"}:
            next_lsb_byte_offset = int(lsb_byte_offset)
            next_narrowed_size = narrowed_size
            if mnemonic == "SUBPIECE":
                byte_offset = self._varnode_constant_value(
                    self._follow_readonly_load_addend_passthrough(def_op.getInput(1))
                )
                if byte_offset is None or int(byte_offset) < 0:
                    return None
                output = getattr(def_op, "getOutput", lambda: None)()
                next_lsb_byte_offset += int(byte_offset)
                output_size = max(1, int(getattr(output, "getSize", lambda: 0)() or 0))
                next_narrowed_size = (
                    output_size
                    if next_narrowed_size is None
                    else min(int(next_narrowed_size), output_size)
                )
            elif mnemonic == "INT_RIGHT":
                shift_bits = self._varnode_constant_value(
                    self._follow_readonly_load_addend_passthrough(def_op.getInput(1))
                )
                if shift_bits is None or int(shift_bits) < 0 or (int(shift_bits) % 8) != 0:
                    return None
                next_lsb_byte_offset += int(shift_bits) // 8
            elif mnemonic != "SUBPIECE" and int(getattr(def_op, "getNumInputs", lambda: 0)() or 0) < 1:
                return None
            return self._collect_load_progressions_from_varnode(
                def_op.getInput(0),
                pointer_param,
                pointer_phis,
                index_phis,
                depth + 1,
                lsb_byte_offset=next_lsb_byte_offset,
                narrowed_size=next_narrowed_size,
            )
        if mnemonic == "INT_AND" and int(getattr(def_op, "getNumInputs", lambda: 0)() or 0) >= 2:
            left = self._follow_readonly_load_addend_passthrough(def_op.getInput(0))
            right = self._follow_readonly_load_addend_passthrough(def_op.getInput(1))
            left_const = self._varnode_constant_value(left)
            right_const = self._varnode_constant_value(right)
            if left_const is not None:
                mask_width = self._low_mask_width_bytes_from_value(int(left_const))
                if mask_width is None:
                    return None
                return self._collect_load_progressions_from_varnode(
                    right,
                    pointer_param,
                    pointer_phis,
                    index_phis,
                    depth + 1,
                    lsb_byte_offset=lsb_byte_offset,
                    narrowed_size=narrowed_size or mask_width,
                )
            if right_const is not None:
                mask_width = self._low_mask_width_bytes_from_value(int(right_const))
                if mask_width is None:
                    return None
                return self._collect_load_progressions_from_varnode(
                    left,
                    pointer_param,
                    pointer_phis,
                    index_phis,
                    depth + 1,
                    lsb_byte_offset=lsb_byte_offset,
                    narrowed_size=narrowed_size or mask_width,
                )
        return None

    def _follow_readonly_load_addend_passthrough(self, varnode):
        current = varnode
        seen = set()
        passthrough = {"COPY", "CAST", "INT_ZEXT"}
        while current is not None:
            current_key = self._varnode_cache_key(current)
            if current_key in seen:
                break
            seen.add(current_key)
            def_op = getattr(current, "getDef", lambda: None)()
            if def_op is None:
                break
            if getattr(def_op, "getMnemonic", lambda: None)() not in passthrough:
                break
            input_count = int(getattr(def_op, "getNumInputs", lambda: 0)() or 0)
            if input_count <= 0:
                break
            current = def_op.getInput(0)
        return current

    def _readonly_load_progression_term_counter(
        self,
        load_progressions: Sequence[Dict[str, object]],
        *,
        result_size: int,
    ) -> Optional[Counter[Tuple[int, int]]]:
        counter: Counter[Tuple[int, int]] = Counter()
        for signature in load_progressions or ():
            lane_offset = int(signature.get("start_offset", 0) or 0)
            lane_size = max(1, int(signature.get("element_size", 0) or 0))
            access_size = min(max(1, int(result_size or lane_size)), lane_size)
            if access_size <= 0 or lane_size % access_size != 0:
                return None
            for byte_delta in range(0, lane_size, access_size):
                counter[(lane_offset + byte_delta, access_size)] += 1
        return counter if counter else None

    def _adjust_readonly_load_signature_access(
        self,
        signature: Dict[str, object],
        *,
        lsb_byte_offset: int,
        narrowed_size: Optional[int],
    ) -> Optional[Dict[str, object]]:
        load_size = max(1, int(signature.get("element_size", 0) or 0))
        access_size = max(1, int(narrowed_size or load_size))
        lsb_byte_offset = int(lsb_byte_offset)
        if lsb_byte_offset < 0 or access_size > load_size or lsb_byte_offset + access_size > load_size:
            return None
        adjusted = dict(signature)
        if self._program_is_big_endian():
            byte_delta = load_size - access_size - lsb_byte_offset
        else:
            byte_delta = lsb_byte_offset
        adjusted["start_offset"] = int(adjusted.get("start_offset", 0) or 0) + int(byte_delta)
        adjusted["element_size"] = access_size
        return adjusted

    def _low_mask_width_bytes_from_value(self, mask: int) -> Optional[int]:
        if mask < 0:
            return None
        width = 0
        current = int(mask)
        while current & 0xFF == 0xFF:
            width += 1
            current >>= 8
        if current != 0 or width <= 0:
            return None
        return width

    def _match_load_progression(
        self,
        load_op,
        pointer_param: dict,
        pointer_phis: Sequence[Dict[str, object]],
        index_phis: Sequence[Dict[str, object]],
    ) -> Optional[Dict[str, int]]:
        output = getattr(load_op, "getOutput", lambda: None)()
        load_size = max(1, int(getattr(output, "getSize", lambda: 4)() or 4))
        address_varnode = self._follow_passthrough_varnode(load_op.getInput(1))

        for pointer_info in pointer_phis:
            if self._same_varnode_value(address_varnode, pointer_info["phi_output"]):
                return {
                    "load_op_ref": self._make_pcode_op_ref(load_op),
                    "induction_phi_ref": self._make_pcode_op_ref(pointer_info.get("phi_op")),
                    "stride": int(pointer_info["stride"]),
                    "element_size": load_size,
                    "start_offset": int(pointer_info.get("start_offset", 0) or 0),
                    "start_index": int(pointer_info.get("start_index", 0) or 0),
                    "index_step": int(pointer_info.get("index_step", 1) or 1),
                    "index_scale": int(pointer_info.get("index_scale", pointer_info["stride"]) or pointer_info["stride"]),
                }

        address_def = getattr(address_varnode, "getDef", lambda: None)()
        if address_def is None:
            return None
        mnemonic = getattr(address_def, "getMnemonic", lambda: None)()
        if mnemonic == "PTRADD" and int(getattr(address_def, "getNumInputs", lambda: 0)() or 0) >= 3:
            base_input = self._follow_passthrough_varnode(address_def.getInput(0))
            index_input = self._follow_passthrough_varnode(address_def.getInput(1))
            elem_size = self._varnode_constant_value(self._follow_passthrough_varnode(address_def.getInput(2)))
            constant_index = self._varnode_constant_value(index_input)
            if elem_size is not None and elem_size > 0 and constant_index is not None:
                for pointer_info in pointer_phis:
                    if self._same_varnode_value(base_input, pointer_info["phi_output"]):
                        return {
                            "load_op_ref": self._make_pcode_op_ref(load_op),
                            "induction_phi_ref": self._make_pcode_op_ref(pointer_info.get("phi_op")),
                            "stride": int(pointer_info["stride"]),
                            "element_size": load_size,
                            "start_offset": int(pointer_info.get("start_offset", 0) or 0)
                            + int(elem_size) * int(constant_index),
                            "start_index": int(pointer_info.get("start_index", 0) or 0),
                            "index_step": int(pointer_info.get("index_step", 1) or 1),
                            "index_scale": int(pointer_info.get("index_scale", pointer_info["stride"]) or pointer_info["stride"]),
                        }
            index_info = self._matched_index_progression(index_input, index_phis)
            if (
                elem_size is not None
                and elem_size > 0
                and self._varnode_matches_parameter(base_input, pointer_param.get("name", ""))
                and index_info is not None
            ):
                return {
                    "load_op_ref": self._make_pcode_op_ref(load_op),
                    "induction_phi_ref": self._make_pcode_op_ref(index_info.get("phi_op")),
                    "stride": int(elem_size) * int(index_info.get("step", 1) or 1),
                    "element_size": load_size,
                    "start_offset": int(elem_size) * int(index_info.get("start", 0) or 0),
                    "start_index": int(index_info.get("start", 0) or 0),
                    "index_step": int(index_info.get("step", 1) or 1),
                    "index_scale": int(elem_size),
                }
        if mnemonic == "INT_ADD" and int(getattr(address_def, "getNumInputs", lambda: 0)() or 0) >= 2:
            left = self._follow_passthrough_varnode(address_def.getInput(0))
            right = self._follow_passthrough_varnode(address_def.getInput(1))
            for pointer_info in pointer_phis:
                if self._same_varnode_value(left, pointer_info["phi_output"]) and self._varnode_constant_value(right) == 0:
                    return {
                        "load_op_ref": self._make_pcode_op_ref(load_op),
                        "induction_phi_ref": self._make_pcode_op_ref(pointer_info.get("phi_op")),
                        "stride": int(pointer_info["stride"]),
                        "element_size": load_size,
                        "start_offset": int(pointer_info.get("start_offset", 0) or 0),
                        "start_index": int(pointer_info.get("start_index", 0) or 0),
                        "index_step": int(pointer_info.get("index_step", 1) or 1),
                        "index_scale": int(pointer_info.get("index_scale", pointer_info["stride"]) or pointer_info["stride"]),
                    }
                if self._same_varnode_value(right, pointer_info["phi_output"]) and self._varnode_constant_value(left) == 0:
                    return {
                        "load_op_ref": self._make_pcode_op_ref(load_op),
                        "induction_phi_ref": self._make_pcode_op_ref(pointer_info.get("phi_op")),
                        "stride": int(pointer_info["stride"]),
                        "element_size": load_size,
                        "start_offset": int(pointer_info.get("start_offset", 0) or 0),
                        "start_index": int(pointer_info.get("start_index", 0) or 0),
                        "index_step": int(pointer_info.get("index_step", 1) or 1),
                        "index_scale": int(pointer_info.get("index_scale", pointer_info["stride"]) or pointer_info["stride"]),
                    }
            if self._varnode_matches_parameter(left, pointer_param.get("name", "")):
                scaled = self._scaled_index_stride_and_start(right, index_phis)
                if scaled is not None and scaled[0] > 0:
                    return {
                        "stride": int(scaled[0]),
                        "element_size": load_size,
                        "start_offset": int(scaled[1]),
                        "start_index": int(scaled[2]),
                        "index_step": int(scaled[3]),
                        "index_scale": int(scaled[4]),
                    }
            if self._varnode_matches_parameter(right, pointer_param.get("name", "")):
                scaled = self._scaled_index_stride_and_start(left, index_phis)
                if scaled is not None and scaled[0] > 0:
                    return {
                        "stride": int(scaled[0]),
                        "element_size": load_size,
                        "start_offset": int(scaled[1]),
                        "start_index": int(scaled[2]),
                        "index_step": int(scaled[3]),
                        "index_scale": int(scaled[4]),
                    }
        return None

    def _matched_index_progression(
        self,
        varnode,
        index_phis: Sequence[Dict[str, object]],
    ) -> Optional[Dict[str, object]]:
        varnode = self._follow_passthrough_varnode(varnode)
        for info in index_phis:
            if self._same_varnode_value(varnode, info["phi_output"]):
                return info
        return None

    def _matches_index_progression(
        self,
        varnode,
        index_phis: Sequence[Dict[str, object]],
    ) -> bool:
        return self._matched_index_progression(varnode, index_phis) is not None

    def _scaled_index_stride(
        self,
        varnode,
        index_phis: Sequence[Dict[str, object]],
    ) -> Optional[int]:
        scaled = self._scaled_index_stride_and_start(varnode, index_phis)
        if scaled is None:
            return None
        return int(scaled[0])

    def _scaled_index_stride_and_start(
        self,
        varnode,
        index_phis: Sequence[Dict[str, object]],
    ) -> Optional[Tuple[int, int, int, int, int]]:
        varnode = self._follow_passthrough_varnode(varnode)
        index_info = self._matched_index_progression(varnode, index_phis)
        if index_info is not None:
            start = int(index_info.get("start", 0) or 0)
            step = int(index_info.get("step", 1) or 1)
            return step, start, start, step, 1
        def_op = getattr(varnode, "getDef", lambda: None)()
        if def_op is None:
            return None
        mnemonic = getattr(def_op, "getMnemonic", lambda: None)()
        if mnemonic == "INT_MULT" and int(getattr(def_op, "getNumInputs", lambda: 0)() or 0) >= 2:
            left = self._follow_passthrough_varnode(def_op.getInput(0))
            right = self._follow_passthrough_varnode(def_op.getInput(1))
            left_info = self._matched_index_progression(left, index_phis)
            if left_info is not None:
                scale = self._varnode_constant_value(right)
                if scale is None:
                    return None
                return (
                    int(scale) * int(left_info.get("step", 1) or 1),
                    int(scale) * int(left_info.get("start", 0) or 0),
                    int(left_info.get("start", 0) or 0),
                    int(left_info.get("step", 1) or 1),
                    int(scale),
                )
            right_info = self._matched_index_progression(right, index_phis)
            if right_info is not None:
                scale = self._varnode_constant_value(left)
                if scale is None:
                    return None
                return (
                    int(scale) * int(right_info.get("step", 1) or 1),
                    int(scale) * int(right_info.get("start", 0) or 0),
                    int(right_info.get("start", 0) or 0),
                    int(right_info.get("step", 1) or 1),
                    int(scale),
                )
        if mnemonic == "INT_LEFT" and int(getattr(def_op, "getNumInputs", lambda: 0)() or 0) >= 2:
            shifted = self._follow_passthrough_varnode(def_op.getInput(0))
            shift_bits = self._varnode_constant_value(self._follow_passthrough_varnode(def_op.getInput(1)))
            shifted_info = self._matched_index_progression(shifted, index_phis)
            if shifted_info is not None and shift_bits is not None and shift_bits >= 0:
                scale = 1 << int(shift_bits)
                return (
                    scale * int(shifted_info.get("step", 1) or 1),
                    scale * int(shifted_info.get("start", 0) or 0),
                    int(shifted_info.get("start", 0) or 0),
                    int(shifted_info.get("step", 1) or 1),
                    int(scale),
                )
        return None

    def _extract_pointer_step(
        self,
        varnode,
        phi_output,
    ) -> Optional[int]:
        varnode = self._follow_passthrough_varnode(varnode)
        def_op = getattr(varnode, "getDef", lambda: None)()
        if def_op is None:
            return None
        mnemonic = getattr(def_op, "getMnemonic", lambda: None)()
        if mnemonic == "PTRADD" and int(getattr(def_op, "getNumInputs", lambda: 0)() or 0) >= 3:
            base = self._follow_passthrough_varnode(def_op.getInput(0))
            index = self._follow_passthrough_varnode(def_op.getInput(1))
            element_size = self._varnode_constant_value(self._follow_passthrough_varnode(def_op.getInput(2)))
            index_value = self._varnode_constant_value(index)
            if (
                self._same_varnode_value(base, phi_output)
                and element_size is not None
                and index_value is not None
            ):
                return int(element_size) * int(index_value)
        if mnemonic in {"INT_ADD", "PTRSUB"} and int(getattr(def_op, "getNumInputs", lambda: 0)() or 0) >= 2:
            left = self._follow_passthrough_varnode(def_op.getInput(0))
            right = self._follow_passthrough_varnode(def_op.getInput(1))
            if self._same_varnode_value(left, phi_output):
                return self._varnode_constant_value(right)
            if self._same_varnode_value(right, phi_output):
                return self._varnode_constant_value(left)
        return None

    def _extract_index_step(
        self,
        varnode,
        phi_output,
    ) -> Optional[int]:
        step_expr = self._extract_index_step_expression(varnode, phi_output)
        if step_expr is None:
            return None
        bit_width = int(getattr(step_expr, "size", 0) or getattr(varnode, "getSize", lambda: 0)() or 4) * 8
        return self._signed_constant_value(step_expr, bit_width_hint=bit_width)

    def _extract_index_step_expression(
        self,
        varnode,
        phi_output,
    ) -> Optional[Expression]:
        varnode = self._follow_passthrough_varnode(varnode)
        def_op = getattr(varnode, "getDef", lambda: None)()
        if def_op is None:
            return None
        mnemonic = getattr(def_op, "getMnemonic", lambda: None)()
        if mnemonic in {"INT_ADD", "INT_SUB"} and int(getattr(def_op, "getNumInputs", lambda: 0)() or 0) >= 2:
            left = self._follow_passthrough_varnode(def_op.getInput(0))
            right = self._follow_passthrough_varnode(def_op.getInput(1))
            if self._same_varnode_value(left, phi_output):
                step_expr = self._build_pcode_expression(right, placeholders={})
                if step_expr is None or self._expression_is_unresolved(step_expr):
                    return None
                if mnemonic == "INT_ADD":
                    return step_expr
                negated = Expression.unary_op("INT_2COMP", step_expr)
                negated.size = int(getattr(step_expr, "size", 0) or getattr(varnode, "getSize", lambda: 0)() or 4)
                return negated
            if self._same_varnode_value(right, phi_output):
                if mnemonic != "INT_ADD":
                    return None
                step_expr = self._build_pcode_expression(left, placeholders={})
                if step_expr is None or self._expression_is_unresolved(step_expr):
                    return None
                return step_expr
        return None

    def _follow_passthrough_varnode(self, varnode):
        current = varnode
        seen = set()
        passthrough = {"COPY", "CAST", "INT_ZEXT", "INT_SEXT", "SUBPIECE"}
        while current is not None:
            current_key = self._varnode_cache_key(current)
            if current_key in seen:
                break
            seen.add(current_key)
            def_op = getattr(current, "getDef", lambda: None)()
            if def_op is None:
                break
            if getattr(def_op, "getMnemonic", lambda: None)() not in passthrough:
                break
            input_count = int(getattr(def_op, "getNumInputs", lambda: 0)() or 0)
            if input_count <= 0:
                break
            current = def_op.getInput(0)
        return current

    def _varnode_cache_key(self, varnode):
        if varnode is None:
            return None
        address_key = None
        try:
            address = varnode.getAddress()
            if address is not None:
                address_key = (
                    address.getAddressSpace().getName(),
                    int(varnode.getOffset()),
                    int(varnode.getSize()),
                )
        except Exception:
            address_key = None

        def_key = None
        def_op = getattr(varnode, "getDef", lambda: None)()
        if def_op is not None:
            seq = getattr(def_op, "getSeqnum", lambda: None)()
            if seq is not None:
                try:
                    target = seq.getTarget()
                    target_key = str(target) if target is not None else None
                except Exception:
                    target_key = None
                try:
                    order_key = int(seq.getOrder())
                except Exception:
                    order_key = None
                try:
                    time_key = int(seq.getTime())
                except Exception:
                    time_key = None
                def_key = (target_key, order_key, time_key, getattr(def_op, "getMnemonic", lambda: None)())
        if address_key is not None or def_key is not None:
            return ("varnode", address_key, def_key)
        return ("varnode_id", id(varnode))

    def _same_varnode_value(self, left, right) -> bool:
        if left is None or right is None:
            return False
        if left is right:
            return True
        try:
            if left == right:
                return True
        except Exception:
            pass
        try:
            left_addr = left.getAddress()
            right_addr = right.getAddress()
            if (
                left_addr is not None
                and right_addr is not None
                and left_addr.getAddressSpace().getName() == right_addr.getAddressSpace().getName()
                and int(left.getOffset()) == int(right.getOffset())
                and int(left.getSize()) == int(right.getSize())
            ):
                return True
        except Exception:
            pass
        left_high = getattr(left, "getHigh", lambda: None)()
        right_high = getattr(right, "getHigh", lambda: None)()
        if left_high is not None and right_high is not None:
            if left_high is right_high:
                return True
            left_rep = getattr(left_high, "getRepresentative", lambda: None)()
            right_rep = getattr(right_high, "getRepresentative", lambda: None)()
            if left_rep is not None and left_rep is right_rep:
                return True
        return False

    def _same_placeholder_varnode(self, left, right) -> bool:
        if left is None or right is None:
            return False
        if left is right:
            return True
        try:
            if left == right:
                return True
        except Exception:
            pass
        left_high = getattr(left, "getHigh", lambda: None)()
        right_high = getattr(right, "getHigh", lambda: None)()
        if left_high is not None and right_high is not None:
            if left_high is right_high:
                return True
            left_rep = getattr(left_high, "getRepresentative", lambda: None)()
            right_rep = getattr(right_high, "getRepresentative", lambda: None)()
            if left_rep is not None and left_rep is right_rep:
                return True
        return False

    def _varnode_matches_parameter(
        self,
        varnode,
        param_name: str,
    ) -> bool:
        varnode = self._follow_passthrough_varnode(varnode)
        high = getattr(varnode, "getHigh", lambda: None)()
        high_name = getattr(high, "getName", lambda: None)
        if callable(high_name):
            try:
                if high_name() == param_name:
                    return True
            except Exception:
                pass
        symbol_getter = getattr(high, "getSymbol", lambda: None)
        if callable(symbol_getter):
            try:
                symbol = symbol_getter()
                symbol_name = getattr(symbol, "getName", lambda: None)
                if callable(symbol_name) and symbol_name() == param_name:
                    return True
            except Exception:
                pass
        expr = self._trace_varnode_expression(varnode)
        return self._parameter_name_from_expr(expr) == param_name

    def _varnode_constant_value(
        self,
        varnode,
    ) -> Optional[int]:
        try:
            address = varnode.getAddress()
            if address is not None and address.getAddressSpace().getName() == "const":
                return int(varnode.getOffset())
        except Exception:
            pass
        expr = self._trace_varnode_expression(varnode)
        return self._raw_constant_value(expr)

    def _varnode_unsigned_constant_value(self, varnode) -> Optional[int]:
        value = self._varnode_constant_value(varnode)
        if value is None:
            return None
        return int(value)

    def _signed_varnode_constant_value(self, varnode) -> Optional[int]:
        value = self._varnode_constant_value(varnode)
        if value is None:
            return None
        try:
            bit_width = max(1, int(getattr(varnode, "getSize", lambda: 0)() or 0)) * 8
        except Exception:
            bit_width = 0
        if bit_width <= 0:
            return int(value)
        modulus = 1 << bit_width
        signed = int(value) % modulus
        if signed >= (1 << (bit_width - 1)):
            signed -= modulus
        return signed

    def _choose_return_reaching_accumulator(
        self,
        candidates: Sequence[CountedLoopAccumulator],
    ) -> CountedLoopAccumulator:
        reaching = [
            candidate for candidate in candidates
            if self._varnode_reaches_return(candidate.phi_output)
        ]
        if reaching:
            return reaching[0]
        return candidates[0]

    def _varnode_reaches_return(
        self,
        start_varnode,
        *,
        budget: int = 128,
    ) -> bool:
        stack = [start_varnode]
        seen = set()
        while stack and len(seen) < budget:
            current = stack.pop()
            if current is None:
                continue
            current_id = id(current)
            if current_id in seen:
                continue
            seen.add(current_id)
            descendants = getattr(current, "getDescendants", lambda: None)()
            if descendants is None:
                continue
            try:
                iterator = iter(descendants)
            except TypeError:
                iterator = None
            if iterator is not None:
                for op in iterator:
                    mnemonic = getattr(op, "getMnemonic", lambda: None)()
                    if mnemonic == "RETURN":
                        return True
                    output = getattr(op, "getOutput", lambda: None)()
                    if output is not None:
                        stack.append(output)
                continue
            while descendants.hasNext():
                op = descendants.next()
                mnemonic = getattr(op, "getMnemonic", lambda: None)()
                if mnemonic == "RETURN":
                    return True
                output = getattr(op, "getOutput", lambda: None)()
                if output is not None:
                    stack.append(output)
        return False

    def _trace_varnode_expression(
        self,
        varnode,
    ) -> Optional[Expression]:
        if varnode is None:
            return None
        try:
            return self.tracer.trace_varnode(varnode, 0, use_cache=False)
        except TypeError:
            try:
                return self.tracer.trace_varnode(varnode, use_cache=False)
            except Exception:
                return None
        except Exception:
            return None

    def _try_summarize_branch_accumulator_loop(
        self,
        analysis,
    ) -> Optional[Tuple[List[ReturnInfo], str]]:
        if analysis is None or not analysis.returns or len(analysis.parameters or []) < 3:
            self._debug("Declined branch-accumulator summary: insufficient returns/parameters")
            return None
        effect_summary = getattr(analysis, "effect_summary", None)
        if effect_summary is None:
            self._debug("Declined branch-accumulator summary: no effect summary")
            return None

        loop_params = self._infer_loop_parameter_pair(analysis)
        if loop_params is None:
            self._debug("Declined branch-accumulator summary: could not infer loop parameter pair")
            return None
        start_name, limit_name = loop_params

        pointer_param = self._infer_pointer_parameter_name(analysis)
        if not pointer_param:
            self._debug("Declined branch-accumulator summary: could not infer pointer parameter")
            return None

        working_returns = list(analysis.returns)
        null_case = self._find_pointer_null_case(working_returns, pointer_param)
        require_pointer_nonnull = null_case is not None
        base_case = self._find_no_loop_base_case(
            working_returns,
            pointer_param,
            start_name,
            limit_name,
            require_pointer_nonnull=require_pointer_nonnull,
        )
        if base_case is None:
            self._debug(
                "Declined branch-accumulator summary: could not identify no-loop base case "
                f"(pointer={pointer_param}, start={start_name}, limit={limit_name})"
            )
            return None

        step_cases = self._find_one_step_cases(
            working_returns,
            pointer_param,
            start_name,
            limit_name,
            require_pointer_nonnull=require_pointer_nonnull,
        )
        if step_cases is None:
            synthesized = self._synthesize_one_step_cases_from_effects(
                analysis,
                base_case,
                pointer_param,
                start_name,
                limit_name,
                require_pointer_nonnull=require_pointer_nonnull,
            )
            if not synthesized:
                self._debug("Declined branch-accumulator summary: could not synthesize one-step cases from effects")
                return None
            working_returns.extend(synthesized)
            step_cases = self._find_one_step_cases(
                working_returns,
                pointer_param,
                start_name,
                limit_name,
                require_pointer_nonnull=require_pointer_nonnull,
            )
            if step_cases is None:
                self._debug("Declined branch-accumulator summary: synthesized one-step cases still did not match")
                return None

        even_case, odd_case = step_cases
        base_expr = base_case.value
        even_delta = self._extract_additive_delta(even_case.value, base_expr, analysis.parameters or [])
        odd_delta = self._extract_additive_delta(odd_case.value, base_expr, analysis.parameters or [])
        if even_delta is None or odd_delta is None:
            self._debug("Declined branch-accumulator summary: could not isolate additive deltas")
            return None

        even_affine = self._extract_affine_term(even_delta, start_name)
        odd_affine = self._extract_affine_term(odd_delta, start_name)
        if even_affine is None or odd_affine is None:
            self._debug("Declined branch-accumulator summary: one-step deltas are not affine in the loop counter")
            return None

        loop_even_value = self._build_parity_split_loop_value(
            base_expr,
            start_name,
            limit_name,
            even_affine,
            odd_affine,
            start_is_even=True,
        )
        loop_odd_value = self._build_parity_split_loop_value(
            base_expr,
            start_name,
            limit_name,
            even_affine,
            odd_affine,
            start_is_even=False,
        )
        if loop_even_value is None or loop_odd_value is None:
            self._debug("Declined branch-accumulator summary: failed to build closed-form loop values")
            return None

        loop_conditions_common = [
            self._pointer_nonnull_condition(pointer_param, analysis),
            Condition(
                Expression.binary_op(
                    "INT_SLESS",
                    self._param_expr(analysis, start_name),
                    self._param_expr(analysis, limit_name),
                ),
                False,
            ),
        ]
        even_start_cond = Condition(
            Expression.binary_op(
                "INT_EQUAL",
                Expression.binary_op(
                    "INT_AND",
                    self._param_expr(analysis, start_name),
                    Expression.constant(1, self._param_expr(analysis, start_name).size or 4),
                ),
                Expression.constant(0, self._param_expr(analysis, start_name).size or 4),
            ),
            False,
        )
        odd_start_cond = even_start_cond.negate()

        summarized: List[ReturnInfo] = []
        if null_case is not None:
            summarized.append(null_case)
        summarized.append(base_case)
        summarized.append(
            ReturnInfo(
                address=base_case.address,
                value=loop_even_value,
                conditions=ConditionSimplifier.simplify_conditions_object_centric(loop_conditions_common + [even_start_cond]),
                branch_index=10_100,
                pcode_identity=base_case.pcode_identity,
                pcode_order=base_case.pcode_order,
                pcode_time=base_case.pcode_time,
            )
        )
        summarized.append(
            ReturnInfo(
                address=base_case.address,
                value=loop_odd_value,
                conditions=ConditionSimplifier.simplify_conditions_object_centric(loop_conditions_common + [odd_start_cond]),
                branch_index=10_101,
                pcode_identity=base_case.pcode_identity,
                pcode_order=base_case.pcode_order,
                pcode_time=base_case.pcode_time,
            )
        )
        self._debug(
            "Recovered counted loop branch-accumulator summary "
            f"(start={start_name}, limit={limit_name}, even={even_affine}, odd={odd_affine})"
        )
        return summarized, "counted_loop_branch_accumulator_summary"

    def _infer_pointer_parameter_name(self, analysis) -> Optional[str]:
        for param in analysis.parameters or []:
            name = str(param.get("name") or "")
            if not name:
                continue
            if is_pointer_data_type(
                param.get("data_type_obj"),
                param.get("data_type"),
                program=getattr(self.tracer, "program", None),
            ):
                return name
        return None

    def _infer_loop_parameter_pair(self, analysis) -> Optional[Tuple[str, str]]:
        candidates: Counter[Tuple[str, str]] = Counter()
        all_conditions: List[Condition] = []
        for ret in analysis.returns or []:
            all_conditions.extend(ret.conditions or [])
        effect_summary = getattr(analysis, "effect_summary", None)
        if effect_summary is not None:
            for effect in effect_summary.effects or []:
                all_conditions.extend(effect.conditions or [])

        for cond in all_conditions:
            pair = self._match_less_parameter_pair(cond)
            if pair is not None:
                candidates[pair] += 1
        if not candidates:
            return None
        return candidates.most_common(1)[0][0]

    def _match_less_parameter_pair(self, condition: Condition) -> Optional[Tuple[str, str]]:
        relation = self._parameter_comparison_relation(condition)
        if relation is None:
            return None
        left_name, relation_name, right_name = relation
        if relation_name == "<":
            return left_name, right_name
        if relation_name == ">":
            return right_name, left_name
        return None

    def _parameter_name_from_expr(self, expr: Optional[Expression]) -> Optional[str]:
        if expr is None:
            return None
        if expr.expr_type == ExpressionType.PARAMETER and expr.name:
            return expr.name
        normalized = self._normalize_counter_view(expr, getattr(expr, "name", None) or "")
        if normalized is not None and normalized[0].name:
            return normalized[0].name
        return None

    def _param_expr(self, analysis, name: str) -> Expression:
        for param in analysis.parameters or []:
            if param.get("name") != name:
                continue
            return Expression.parameter(
                name,
                index=int(param.get("index", 0)),
                data_type=param.get("data_type"),
                data_type_obj=param.get("data_type_obj"),
                size=int(param.get("size", 4) or 4),
            )
        return Expression.parameter(name, size=4)

    def _find_pointer_null_case(
        self,
        returns: Sequence[ReturnInfo],
        pointer_name: str,
    ) -> Optional[ReturnInfo]:
        for ret in returns:
            if not self._return_is_constant(ret):
                continue
            if any(self._condition_is_pointer_null(cond, pointer_name) for cond in ret.conditions or []):
                return ret
        return None

    def _find_no_loop_base_case(
        self,
        returns: Sequence[ReturnInfo],
        pointer_name: str,
        start_name: str,
        limit_name: str,
        *,
        require_pointer_nonnull: bool,
    ) -> Optional[ReturnInfo]:
        for ret in returns:
            if self._return_is_constant(ret):
                continue
            has_nonnull = any(self._condition_is_pointer_nonnull(cond, pointer_name) for cond in ret.conditions or [])
            has_not_less = any(self._condition_is_not_less(cond, start_name, limit_name) for cond in ret.conditions or [])
            if has_not_less and (has_nonnull or not require_pointer_nonnull):
                return ret
        return None

    def _find_one_step_cases(
        self,
        returns: Sequence[ReturnInfo],
        pointer_name: str,
        start_name: str,
        limit_name: str,
        *,
        require_pointer_nonnull: bool,
    ) -> Optional[Tuple[ReturnInfo, ReturnInfo]]:
        even_case = None
        odd_case = None
        for ret in returns:
            conditions = ret.conditions or []
            has_nonnull = any(self._condition_is_pointer_nonnull(cond, pointer_name) for cond in conditions)
            has_loop = any(self._condition_is_less(cond, start_name, limit_name) for cond in conditions)
            has_one_step = any(self._condition_is_step_equality(cond, start_name, limit_name) for cond in conditions)
            if not (has_loop and has_one_step and (has_nonnull or not require_pointer_nonnull)):
                continue
            parity = self._extract_counter_parity(conditions, start_name)
            if parity is True:
                even_case = ret
            elif parity is False:
                odd_case = ret
        if even_case is None or odd_case is None:
            return None
        return even_case, odd_case

    def _synthesize_one_step_cases_from_effects(
        self,
        analysis,
        base_case: ReturnInfo,
        pointer_name: str,
        start_name: str,
        limit_name: str,
        *,
        require_pointer_nonnull: bool,
    ) -> List[ReturnInfo]:
        effect_summary = getattr(analysis, "effect_summary", None)
        if effect_summary is None:
            return []
        coeffs = self._extract_linear_location_coefficients(base_case.value, analysis.parameters or [])
        if not coeffs:
            return []

        grouped: Dict[Tuple[object, ...], List] = {}
        for effect in effect_summary.effects or []:
            conds = ConditionSimplifier.simplify_conditions_object_centric(effect.conditions or [])
            key = _runtime_conditions_signature(conds)
            grouped.setdefault(key, []).append((conds, effect))

        synthesized: List[ReturnInfo] = []
        for grouped_effects in grouped.values():
            conds = grouped_effects[0][0]
            has_nonnull = any(self._condition_is_pointer_nonnull(cond, pointer_name) for cond in conds)
            if require_pointer_nonnull and not has_nonnull:
                self._debug(
                    "Skipping effect-derived one-step candidate: missing local pointer-nonnull guard "
                    f"for conditions {[cond.to_string() for cond in conds]}"
                )
                continue
            if not any(self._condition_is_less(cond, start_name, limit_name) for cond in conds):
                self._debug(
                    "Skipping effect-derived one-step candidate: missing loop-progress guard "
                    f"for conditions {[cond.to_string() for cond in conds]}"
                )
                continue
            parity = self._extract_counter_parity(conds, start_name)
            if parity is None:
                self._debug(
                    "Skipping effect-derived one-step candidate: could not determine counter parity "
                    f"for conditions {[cond.to_string() for cond in conds]}"
                )
                continue
            step_eq = Condition(
                Expression.binary_op(
                    "INT_EQUAL",
                    self._param_expr(analysis, limit_name),
                    Expression.binary_op(
                        "INT_ADD",
                        self._param_expr(analysis, start_name),
                        Expression.constant(1, self._param_expr(analysis, start_name).size or 4),
                    ),
                ),
                False,
            )
            step_context = ConditionSimplifier.simplify_conditions_object_centric(list(conds) + [step_eq])
            if ConditionSimplifier.object_centric_is_contradiction(step_context):
                self._debug(
                    "Skipping effect-derived one-step candidate: one-step context is contradictory "
                    f"for conditions {[cond.to_string() for cond in conds]}"
                )
                continue

            delta_terms: List[Expression] = []
            for _conds, effect in grouped_effects:
                coeff = coeffs.get(effect.location)
                if coeff in (None, 0):
                    continue
                delta_expr = self._extract_store_delta_expr(
                    effect,
                    analysis.parameters or [],
                    step_context,
                )
                if delta_expr is None:
                    self._debug(
                        "Aborting effect-derived one-step synthesis: could not isolate store delta "
                        f"for location={effect.location} value={effect.value.to_string()} "
                        f"conditions={[cond.to_string() for cond in step_context]}"
                    )
                    return []
                reduced_delta = _reduce_expression_under_conditions(delta_expr, step_context)
                scaled = self._scale_expression(reduced_delta, coeff)
                if scaled is not None:
                    delta_terms.append(scaled)
            if not delta_terms:
                self._debug(
                    "Skipping effect-derived one-step candidate: no additive delta terms matched "
                    f"for conditions {[cond.to_string() for cond in conds]}"
                )
                continue

            delta_sum = self._sum_expression_terms(delta_terms)
            if delta_sum is None:
                continue
            value = Expression.binary_op("INT_ADD", base_case.value, delta_sum)
            value.size = base_case.value.size
            synthesized.append(
                ReturnInfo(
                    address=base_case.address,
                    value=value,
                    conditions=step_context,
                    branch_index=9_000 if parity else 9_001,
                    pcode_identity=base_case.pcode_identity,
                    pcode_order=base_case.pcode_order,
                    pcode_time=base_case.pcode_time,
                )
            )
        return synthesized

    def _extract_linear_location_coefficients(
        self,
        expr: Expression,
        parameters: Sequence[dict],
    ) -> Dict[CanonicalLocation, int]:
        coeffs: Dict[CanonicalLocation, int] = {}
        for sign, term in self._flatten_add_terms(expr):
            if term.expr_type == ExpressionType.CONSTANT:
                continue
            if term.expr_type != ExpressionType.MEMORY or not term.operands:
                return {}
            location = canonicalize_location(term.operands[0], parameters, size=term.size)
            if location is None:
                return {}
            coeffs[location] = coeffs.get(location, 0) + sign
        return {loc: coeff for loc, coeff in coeffs.items() if coeff != 0}

    def _extract_store_delta_expr(
        self,
        effect,
        parameters: Sequence[dict],
        conditions: Optional[Sequence[Condition]] = None,
    ) -> Optional[Expression]:
        active_conditions = list(conditions or [])
        reduced_value = _reduce_expression_under_conditions(effect.value, active_conditions)
        current_read = Expression.memory(
            self._address_expr_for_location(effect.location, parameters),
            size=effect.location.size,
        )
        reduced_current_read = _reduce_expression_under_conditions(current_read, active_conditions)
        delta = self._extract_additive_delta(reduced_value, reduced_current_read, parameters)
        if delta is not None:
            return delta
        if reduced_value.equals(reduced_current_read):
            return Expression.constant(0, size=effect.location.size)
        return None

    def _address_expr_for_location(
        self,
        location: CanonicalLocation,
        parameters: Sequence[dict],
    ) -> Expression:
        base_param = None
        for param in parameters:
            if location.base_ref.matches_parameter(param):
                base_param = param
                break
        base_expr = Expression.parameter(
            location.base_ref.parameter_name or location.base_param,
            index=int((base_param or {}).get("index", 0)),
            data_type=(base_param or {}).get("data_type"),
            data_type_obj=(base_param or {}).get("data_type_obj"),
            size=int((base_param or {}).get("size", 8) or 8),
        )
        if location.offset == 0:
            return base_expr
        return Expression.binary_op(
            "INT_ADD",
            base_expr,
            Expression.constant(location.offset, size=base_expr.size or 8),
        )

    def _extract_additive_delta(
        self,
        expr: Expression,
        base_expr: Expression,
        parameters: Sequence[dict],
    ) -> Optional[Expression]:
        expr_terms = self._flatten_add_terms(expr)
        base_terms = self._flatten_add_terms(base_expr)
        remaining = list(expr_terms)
        for sign, term in base_terms:
            matched = False
            for index, (cand_sign, cand_term) in enumerate(remaining):
                if cand_sign != sign:
                    continue
                if not self._terms_equivalent(cand_term, term, parameters):
                    continue
                del remaining[index]
                matched = True
                break
            if not matched:
                return None
        return self._sum_expression_terms(
            [self._scale_expression(term, sign) for sign, term in remaining if self._scale_expression(term, sign) is not None]
        )

    def _terms_equivalent(
        self,
        left: Expression,
        right: Expression,
        parameters: Sequence[dict],
    ) -> bool:
        if _expressions_equivalent_under_conditions(left, right, [], parameters):
            return True
        if (
            left.expr_type == ExpressionType.MEMORY
            and right.expr_type == ExpressionType.MEMORY
            and left.operands
            and right.operands
        ):
            left_loc = canonicalize_location(left.operands[0], parameters, size=left.size)
            right_loc = canonicalize_location(right.operands[0], parameters, size=right.size)
            if left_loc is not None and right_loc is not None:
                return left_loc == right_loc
        return _runtime_expression_signature(left) == _runtime_expression_signature(right)

    def _flatten_add_terms(
        self,
        expr: Expression,
        sign: int = 1,
    ) -> List[Tuple[int, Expression]]:
        if expr.expr_type == ExpressionType.BINARY_OP and expr.operator == "INT_ADD" and len(expr.operands) == 2:
            return self._flatten_add_terms(expr.operands[0], sign) + self._flatten_add_terms(expr.operands[1], sign)
        if expr.expr_type == ExpressionType.BINARY_OP and expr.operator == "INT_SUB" and len(expr.operands) == 2:
            return self._flatten_add_terms(expr.operands[0], sign) + self._flatten_add_terms(expr.operands[1], -sign)
        if expr.expr_type == ExpressionType.UNARY_OP and expr.operator == "INT_2COMP" and expr.operands:
            return self._flatten_add_terms(expr.operands[0], -sign)
        return [(sign, expr)]

    def _scale_expression(self, expr: Expression, factor: int) -> Optional[Expression]:
        if factor == 0:
            return None
        if factor == 1:
            return expr
        if factor == -1:
            negated = Expression.unary_op("INT_2COMP", expr)
            negated.size = expr.size
            return negated
        return Expression.binary_op(
            "INT_MULT",
            Expression.constant(factor, size=expr.size or 4),
            expr,
        )

    def _sum_expression_terms(
        self,
        terms: Sequence[Optional[Expression]],
    ) -> Optional[Expression]:
        normalized = [term for term in terms if term is not None]
        if not normalized:
            return Expression.constant(0, 4)
        total = normalized[0]
        for term in normalized[1:]:
            total = Expression.binary_op("INT_ADD", total, term)
            total.size = max(total.size, term.size)
        return total

    def _build_parity_split_loop_value(
        self,
        base_expr: Expression,
        start_name: str,
        limit_name: str,
        even_affine: Tuple[int, int],
        odd_affine: Tuple[int, int],
        start_is_even: bool,
    ) -> Optional[Expression]:
        start_expr = self._param_expr_placeholder(start_name, base_expr.size or 4)
        limit_expr = self._param_expr_placeholder(limit_name, base_expr.size or 4)
        size = start_expr.size or 4
        n_expr = Expression.binary_op("INT_SUB", limit_expr, start_expr)
        n_expr.size = size
        one = Expression.constant(1, size)
        two = Expression.constant(2, size)

        if start_is_even:
            n_even = Expression.binary_op("INT_SDIV", Expression.binary_op("INT_ADD", n_expr, one), two)
            n_odd = Expression.binary_op("INT_SDIV", n_expr, two)
            first_even = start_expr
            first_odd = Expression.binary_op("INT_ADD", start_expr, one)
        else:
            n_even = Expression.binary_op("INT_SDIV", n_expr, two)
            n_odd = Expression.binary_op("INT_SDIV", Expression.binary_op("INT_ADD", n_expr, one), two)
            first_even = Expression.binary_op("INT_ADD", start_expr, one)
            first_odd = start_expr
        for item in (n_even, n_odd, first_even, first_odd):
            item.size = size

        sum_even = self._build_arithmetic_progression_sum(first_even, n_even, size)
        sum_odd = self._build_arithmetic_progression_sum(first_odd, n_odd, size)
        contrib_terms: List[Expression] = []
        even_sum_term = self._scale_expression(sum_even, even_affine[0])
        odd_sum_term = self._scale_expression(sum_odd, odd_affine[0])
        if even_sum_term is not None:
            contrib_terms.append(even_sum_term)
        if odd_sum_term is not None:
            contrib_terms.append(odd_sum_term)
        even_count_term = self._scale_expression(n_even, even_affine[1])
        odd_count_term = self._scale_expression(n_odd, odd_affine[1])
        if even_count_term is not None:
            contrib_terms.append(even_count_term)
        if odd_count_term is not None:
            contrib_terms.append(odd_count_term)
        contrib = self._sum_expression_terms(contrib_terms)
        if contrib is None:
            return None
        total = Expression.binary_op("INT_ADD", base_expr, contrib)
        total.size = base_expr.size
        return total

    def _param_expr_placeholder(self, name: str, size: int) -> Expression:
        return Expression.parameter(name, size=size)

    def _build_arithmetic_progression_sum(
        self,
        first_term: Expression,
        count: Expression,
        size: int,
    ) -> Expression:
        one = Expression.constant(1, size)
        count_minus_one = Expression.binary_op("INT_SUB", count, one)
        count_minus_one.size = size
        tail = Expression.binary_op("INT_ADD", first_term, count_minus_one)
        tail.size = size
        pair_sum = Expression.binary_op("INT_ADD", first_term, tail)
        pair_sum.size = size
        product = Expression.binary_op("INT_MULT", count, pair_sum)
        product.size = size
        half = Expression.binary_op("INT_SDIV", product, Expression.constant(2, size))
        half.size = size
        return half

    def _condition_is_pointer_null(self, condition: Condition, pointer_name: str) -> bool:
        return self._match_pointer_equality(condition, pointer_name, expect_zero=True)

    def _condition_is_pointer_nonnull(self, condition: Condition, pointer_name: str) -> bool:
        return self._match_pointer_equality(condition, pointer_name, expect_zero=False)

    def _pointer_nonnull_condition(self, pointer_name: str, analysis) -> Condition:
        ptr_expr = self._param_expr(analysis, pointer_name)
        return Condition(
            Expression.binary_op(
                "INT_NOTEQUAL",
                ptr_expr,
                Expression.constant(0, size=ptr_expr.size or 8),
            ),
            False,
        )

    def _match_pointer_equality(self, condition: Condition, pointer_name: str, expect_zero: bool) -> bool:
        expr = getattr(condition, "expression", None)
        if expr is None or expr.expr_type != ExpressionType.BINARY_OP or len(expr.operands) != 2:
            return False
        if expr.operator not in {"INT_EQUAL", "INT_NOTEQUAL"}:
            return False
        left_name = self._parameter_name_from_expr(expr.operands[0])
        right_name = self._parameter_name_from_expr(expr.operands[1])
        left_const = self._constant_value(expr.operands[0])
        right_const = self._constant_value(expr.operands[1])
        matches = (
            (left_name == pointer_name and right_const == 0)
            or (right_name == pointer_name and left_const == 0)
        )
        if not matches:
            return False
        is_equal = expr.operator == "INT_EQUAL"
        if condition.negated:
            is_equal = not is_equal
        return is_equal if expect_zero else not is_equal

    def _condition_is_less(self, condition: Condition, start_name: str, limit_name: str) -> bool:
        relation = self._parameter_comparison_relation(condition)
        if relation is None:
            return False
        left_name, relation_name, right_name = relation
        return (
            (left_name == start_name and right_name == limit_name and relation_name == "<")
            or (left_name == limit_name and right_name == start_name and relation_name == ">")
        )

    def _condition_is_not_less(self, condition: Condition, start_name: str, limit_name: str) -> bool:
        relation = self._parameter_comparison_relation(condition)
        if relation is None:
            return False
        left_name, relation_name, right_name = relation
        return (
            (left_name == start_name and right_name == limit_name and relation_name == ">=")
            or (left_name == limit_name and right_name == start_name and relation_name == "<=")
        )

    def _condition_is_step_equality(self, condition: Condition, start_name: str, limit_name: str) -> bool:
        expr = getattr(condition, "expression", None)
        if expr is None or expr.expr_type != ExpressionType.BINARY_OP or expr.operator != "INT_EQUAL" or len(expr.operands) != 2:
            return False
        left_name = self._parameter_name_from_expr(expr.operands[0])
        right_name = self._parameter_name_from_expr(expr.operands[1])
        if left_name == limit_name and self._expr_is_add_one_of_param(expr.operands[1], start_name):
            return not condition.negated
        if right_name == limit_name and self._expr_is_add_one_of_param(expr.operands[0], start_name):
            return not condition.negated
        return False

    def _expr_is_add_one_of_param(self, expr: Expression, param_name: str) -> bool:
        if expr.expr_type != ExpressionType.BINARY_OP or expr.operator != "INT_ADD" or len(expr.operands) != 2:
            return False
        left_name = self._parameter_name_from_expr(expr.operands[0])
        right_name = self._parameter_name_from_expr(expr.operands[1])
        left_const = self._constant_value(expr.operands[0])
        right_const = self._constant_value(expr.operands[1])
        return (
            (left_name == param_name and right_const == 1)
            or (right_name == param_name and left_const == 1)
        )

    def _extract_counter_parity(
        self,
        conditions: Sequence[Condition],
        counter_name: str,
    ) -> Optional[bool]:
        for condition in conditions or []:
            expr = getattr(condition, "expression", None)
            if (
                expr is None
                or expr.expr_type != ExpressionType.BINARY_OP
                or expr.operator not in {"INT_EQUAL", "INT_NOTEQUAL"}
                or len(expr.operands) != 2
            ):
                continue
            bitand = None
            parity_const = None
            if self._constant_value(expr.operands[0]) in {0, 1}:
                bitand = expr.operands[1]
                parity_const = self._constant_value(expr.operands[0])
            elif self._constant_value(expr.operands[1]) in {0, 1}:
                bitand = expr.operands[0]
                parity_const = self._constant_value(expr.operands[1])
            if bitand is None or parity_const is None:
                continue
            if bitand.expr_type != ExpressionType.BINARY_OP or bitand.operator != "INT_AND" or len(bitand.operands) != 2:
                continue
            if self._constant_value(bitand.operands[0]) == 1:
                counter_expr = bitand.operands[1]
            elif self._constant_value(bitand.operands[1]) == 1:
                counter_expr = bitand.operands[0]
            else:
                continue
            if self._parameter_name_from_expr(counter_expr) != counter_name:
                continue
            is_equal = expr.operator == "INT_EQUAL"
            if condition.negated:
                is_equal = not is_equal
            is_even = is_equal if parity_const == 0 else not is_equal
            return is_even
        return None

    def _return_is_constant(self, ret: ReturnInfo) -> bool:
        return ret.value is not None and ret.value.expr_type == ExpressionType.CONSTANT

    def _iter_pcode_ops(self, high_function) -> Iterable:
        for basic_block in high_function.getBasicBlocks():
            pcode_iter = basic_block.getIterator()
            while pcode_iter.hasNext():
                yield pcode_iter.next()

    def _parameter_can_be_counter(self, param_info: dict) -> bool:
        size = int(param_info.get("size") or 0)
        if size not in {1, 2, 4, 8}:
            return False
        data_type_obj = param_info.get("data_type_obj")
        if data_type_obj is None:
            return True
        return is_integral_data_type(
            data_type_obj,
            param_info.get("data_type"),
            program=getattr(self.tracer, "program", None),
        )

    def _parameter_expression(self, param_info: dict) -> Expression:
        size = int(param_info.get("size") or 4)
        return Expression.parameter(
            param_info.get("name", "param_1"),
            index=int(param_info.get("index", 0)),
            data_type=param_info.get("data_type"),
            data_type_obj=param_info.get("data_type_obj"),
            size=size,
            storage_info=param_info.get("storage_info"),
        )

    def _is_direct_self_call(self, op, function_name: str) -> bool:
        resolver = getattr(self.tracer, "resolve_call_target_ref", None)
        if not callable(resolver):
            return False
        target_ref = resolver(
            op.getInput(0),
            allow_containing=True,
            allow_code_address=False,
        )
        return bool(target_ref is not None and target_ref.function_name == function_name)

    def _expression_contains_recursive_unknown(self, expr: Optional[Expression], function_name: str) -> bool:
        if expr is None:
            return False
        if expr.expr_type == ExpressionType.UNKNOWN:
            runtime_ref = getattr(expr, "runtime_ref", None)
            if not isinstance(runtime_ref, UnknownValueRef):
                return False
            target_ref = runtime_ref.target_ref
            return bool(
                target_ref is not None
                and target_ref.function_name == function_name
            )
        if expr.expr_type == ExpressionType.PHI and expr.value:
            return any(
                (cond is not None and self._expression_contains_recursive_unknown(cond.expression, function_name))
                or self._expression_contains_recursive_unknown(value, function_name)
                for cond, value in expr.value
            )
        return any(self._expression_contains_recursive_unknown(operand, function_name) for operand in expr.operands or [])

    def _is_constant_expression(self, expr: Optional[Expression]) -> bool:
        return expr is not None and expr.expr_type == ExpressionType.CONSTANT

    def _constant_value(self, expr: Optional[Expression]) -> Optional[int]:
        raw = self._raw_constant_value(expr)
        if raw is None:
            return None
        return raw

    def _raw_constant_value(self, expr: Optional[Expression]) -> Optional[int]:
        if expr is None:
            return None
        if expr.expr_type == ExpressionType.CONSTANT:
            return int(expr.value)
        evaluated = eval_constant_raw(expr)
        if evaluated is None:
            return None
        return int(evaluated[0])

    def _signed_constant_value(
        self,
        expr: Optional[Expression],
        bit_width_hint: Optional[int] = None,
    ) -> Optional[int]:
        raw_value = self._raw_constant_value(expr)
        if raw_value is None:
            return None
        assert expr is not None
        bit_width = int(bit_width_hint or ((expr.size or 0) * 8))
        if bit_width <= 0:
            return raw_value
        modulus = 1 << bit_width
        signed = raw_value % modulus
        if signed >= (1 << (bit_width - 1)):
            signed -= modulus
        return signed

    def _extract_addend_expression(self, expr: Expression, function_name: str) -> Optional[Expression]:
        if expr.expr_type != ExpressionType.BINARY_OP or len(expr.operands) != 2:
            return None
        if expr.operator not in {"INT_ADD", "INT_SUB"}:
            return None

        left, right = expr.operands
        if self._expression_contains_recursive_unknown(left, function_name) and not self._expression_contains_recursive_unknown(right, function_name):
            if expr.operator == "INT_ADD":
                return right
            if expr.operator == "INT_SUB":
                return Expression.unary_op("INT_2COMP", right)
        if self._expression_contains_recursive_unknown(right, function_name) and not self._expression_contains_recursive_unknown(left, function_name):
            if expr.operator == "INT_ADD":
                return left
        return None

    def _extract_unit_step_from_call_argument(self, expr: Expression, param_name: str) -> Optional[int]:
        bit_width_hint = self._infer_counter_bit_width(expr, param_name)
        affine = self._extract_affine_term(expr, param_name, bit_width_hint=bit_width_hint)
        if affine is None:
            return None
        coeff, bias = affine
        if coeff != 1:
            return None
        if bias in {-1, 1}:
            return bias
        return None

    def _extract_affine_term(
        self,
        expr: Expression,
        param_name: str,
        bit_width_hint: Optional[int] = None,
    ) -> Optional[Tuple[int, int]]:
        normalized_counter = self._normalize_counter_view(expr, param_name)
        if normalized_counter is not None:
            return 1, 0
        if expr.expr_type == ExpressionType.CONSTANT:
            signed_value = self._signed_constant_value(expr, bit_width_hint=bit_width_hint)
            if signed_value is None:
                return None
            return 0, signed_value
        if expr.expr_type == ExpressionType.UNARY_OP and expr.operator in {"INT_2COMP", "INT_NEGATE"} and len(expr.operands) == 1:
            operand = self._extract_affine_term(
                expr.operands[0],
                param_name,
                bit_width_hint=bit_width_hint,
            )
            if operand is None:
                return None
            coeff, bias = operand
            return -coeff, -bias
        if expr.expr_type != ExpressionType.BINARY_OP or len(expr.operands) != 2:
            return None

        node_bit_width = bit_width_hint or self._infer_counter_bit_width(expr, param_name)
        left = self._extract_affine_term(expr.operands[0], param_name, bit_width_hint=node_bit_width)
        right = self._extract_affine_term(expr.operands[1], param_name, bit_width_hint=node_bit_width)

        if expr.operator == "INT_ADD" and left is not None and right is not None:
            return left[0] + right[0], left[1] + right[1]
        if expr.operator == "INT_SUB" and left is not None and right is not None:
            return left[0] - right[0], left[1] - right[1]
        if expr.operator == "INT_MULT":
            left_const = self._signed_constant_value(expr.operands[0], bit_width_hint=node_bit_width)
            right_const = self._signed_constant_value(expr.operands[1], bit_width_hint=node_bit_width)
            if left_const is not None and right is not None:
                return left_const * right[0], left_const * right[1]
            if right_const is not None and left is not None:
                return right_const * left[0], right_const * left[1]
        return None

    def _normalize_counter_view(
        self,
        expr: Optional[Expression],
        param_name: str,
    ) -> Optional[Tuple[Expression, Optional[int]]]:
        if expr is None:
            return None
        if expr.expr_type == ExpressionType.PARAMETER and expr.name == param_name:
            return expr, (expr.size * 8) if expr.size else None
        if expr.expr_type == ExpressionType.UNARY_OP and expr.operator in {"INT_ZEXT", "INT_SEXT"} and len(expr.operands) == 1:
            return self._normalize_counter_view(expr.operands[0], param_name)
        if expr.expr_type != ExpressionType.BINARY_OP or expr.operator != "INT_AND" or len(expr.operands) != 2:
            return None

        left_counter = self._normalize_counter_view(expr.operands[0], param_name)
        right_counter = self._normalize_counter_view(expr.operands[1], param_name)
        left_const = self._raw_constant_value(expr.operands[0])
        right_const = self._raw_constant_value(expr.operands[1])

        if left_counter is not None and right_const is not None:
            mask_bits = self._bit_width_from_low_bit_mask(right_const)
            if mask_bits is not None:
                return left_counter[0], mask_bits
        if right_counter is not None and left_const is not None:
            mask_bits = self._bit_width_from_low_bit_mask(left_const)
            if mask_bits is not None:
                return right_counter[0], mask_bits
        return None

    def _infer_counter_bit_width(self, expr: Optional[Expression], param_name: str) -> Optional[int]:
        normalized = self._normalize_counter_view(expr, param_name)
        if normalized is not None:
            return normalized[1]
        if expr is None:
            return None
        for operand in expr.operands or []:
            operand_bit_width = self._infer_counter_bit_width(operand, param_name)
            if operand_bit_width is not None:
                return operand_bit_width
        return None

    def _bit_width_from_low_bit_mask(self, value: int) -> Optional[int]:
        if value <= 0:
            return None
        if (value & (value + 1)) != 0:
            return None
        bit_width = value.bit_length()
        if bit_width < 8 or bit_width % 8 != 0:
            return None
        return bit_width

    def _infer_lower_bound_from_conditions(self, conditions: Sequence[Condition], param_name: str) -> Optional[int]:
        lower_bounds: List[int] = []
        for condition in conditions or []:
            relation = self._condition_relation(condition, param_name)
            if relation is None:
                continue
            relation_name, constant = relation
            if relation_name == ">":
                lower_bounds.append(constant)
            elif relation_name == ">=":
                lower_bounds.append(constant - 1)
        if not lower_bounds:
            return None
        return max(lower_bounds)

    def _infer_lower_bound_from_base_conditions(self, conditions: Sequence[Condition], param_name: str) -> Optional[int]:
        upper_bounds: List[int] = []
        for condition in conditions or []:
            relation = self._condition_relation(condition, param_name)
            if relation is None:
                continue
            relation_name, constant = relation
            if relation_name == "<=":
                upper_bounds.append(constant)
            elif relation_name == "<":
                upper_bounds.append(constant - 1)
        if not upper_bounds:
            return None
        return min(upper_bounds)

    def _condition_relation(self, condition: Condition, param_name: str) -> Optional[Tuple[str, int]]:
        expr = getattr(condition, "expression", None)
        if expr is None or expr.expr_type != ExpressionType.BINARY_OP or len(expr.operands) != 2:
            return None
        left, right = expr.operands
        right_const = self._constant_value(right)
        left_const = self._constant_value(left)

        op = expr.operator
        relation: Optional[str] = None

        if self._is_condition_counter_view(left, param_name) and right_const is not None:
            relation = self._comparison_to_relation(op, swapped=False)
            constant = right_const
        elif self._is_condition_counter_view(right, param_name) and left_const is not None:
            relation = self._comparison_to_relation(op, swapped=True)
            constant = left_const
        else:
            return None

        if relation is None:
            return None
        if condition.negated:
            relation = self._negate_relation(relation)
            if relation is None:
                return None
        return relation, constant

    def _exact_counter_value_from_conditions(
        self,
        conditions: Sequence[Condition],
        param_name: str,
    ) -> Optional[int]:
        lower_bounds: List[int] = []
        upper_bounds: List[int] = []
        for condition in conditions or []:
            expr = getattr(condition, "expression", None)
            if expr is None or expr.expr_type != ExpressionType.BINARY_OP or len(expr.operands) != 2:
                relation = self._condition_relation(condition, param_name)
                if relation is None:
                    continue
                relation_name, constant = relation
            else:
                operator = getattr(expr, "operator", None)
                left, right = expr.operands
                right_const = self._constant_value(right)
                left_const = self._constant_value(left)
                if self._is_condition_counter_view(left, param_name) and right_const is not None:
                    if operator == "INT_EQUAL" and not condition.negated:
                        return right_const
                    if operator == "INT_NOTEQUAL" and condition.negated:
                        return right_const
                if self._is_condition_counter_view(right, param_name) and left_const is not None:
                    if operator == "INT_EQUAL" and not condition.negated:
                        return left_const
                    if operator == "INT_NOTEQUAL" and condition.negated:
                        return left_const
                affine_left = self._solve_counter_affine_equality(left, right_const, operator, condition.negated, param_name)
                if affine_left is not None:
                    return affine_left
                affine_right = self._solve_counter_affine_equality(right, left_const, operator, condition.negated, param_name)
                if affine_right is not None:
                    return affine_right
                relation = self._condition_relation(condition, param_name)
                if relation is None:
                    continue
                relation_name, constant = relation

            if relation_name == ">":
                lower_bounds.append(constant + 1)
            elif relation_name == ">=":
                lower_bounds.append(constant)
            elif relation_name == "<":
                upper_bounds.append(constant - 1)
            elif relation_name == "<=":
                upper_bounds.append(constant)
        if not lower_bounds or not upper_bounds:
            return None
        exact_lower = max(lower_bounds)
        exact_upper = min(upper_bounds)
        if exact_lower == exact_upper:
            return exact_lower
        return None

    def _solve_counter_affine_equality(
        self,
        expr: Optional[Expression],
        other_const: Optional[int],
        operator: Optional[str],
        negated: bool,
        param_name: str,
    ) -> Optional[int]:
        if (
            expr is None
            or other_const is None
            or operator not in {"INT_EQUAL", "INT_NOTEQUAL"}
        ):
            return None
        if operator == "INT_EQUAL" and negated:
            return None
        if operator == "INT_NOTEQUAL" and not negated:
            return None

        bit_width_hint = self._infer_counter_bit_width(expr, param_name)
        affine = self._extract_affine_term(expr, param_name, bit_width_hint=bit_width_hint)
        if affine is None:
            return None
        coeff, bias = affine
        if coeff != 1:
            return None
        return other_const - bias

    def _parameter_comparison_relation(self, condition: Condition) -> Optional[Tuple[str, str, str]]:
        expr = getattr(condition, "expression", None)
        if expr is None or expr.expr_type != ExpressionType.BINARY_OP or len(expr.operands) != 2:
            return None
        relation = self._comparison_to_relation(expr.operator, swapped=False)
        if relation is None:
            return None
        left_name = self._parameter_name_from_expr(expr.operands[0])
        right_name = self._parameter_name_from_expr(expr.operands[1])
        if not left_name or not right_name or left_name == right_name:
            return None
        if condition.negated:
            relation = self._negate_relation(relation)
            if relation is None:
                return None
        return left_name, relation, right_name

    def _is_condition_counter_view(self, expr: Optional[Expression], param_name: str) -> bool:
        if expr is None:
            return False
        if self._normalize_counter_view(expr, param_name) is not None:
            return True
        if expr.expr_type == ExpressionType.BINARY_OP and expr.operator == "PIECE" and len(expr.operands) == 2:
            return self._normalize_counter_view(expr.operands[1], param_name) is not None
        if expr.expr_type != ExpressionType.BINARY_OP or expr.operator not in {"INT_OR", "INT_ADD"} or len(expr.operands) != 2:
            return False
        left, right = expr.operands
        return self._matches_shifted_high_reconstruction(left, right, param_name) or self._matches_shifted_high_reconstruction(right, left, param_name)

    def _matches_shifted_high_reconstruction(
        self,
        high_expr: Optional[Expression],
        low_expr: Optional[Expression],
        param_name: str,
    ) -> bool:
        low_counter = self._normalize_counter_view(low_expr, param_name)
        if low_counter is None:
            return False
        if high_expr is None:
            return False
        if high_expr.expr_type != ExpressionType.BINARY_OP or high_expr.operator != "INT_LEFT" or len(high_expr.operands) != 2:
            return False
        shift_bits = self._raw_constant_value(high_expr.operands[1])
        if shift_bits is None:
            return False
        low_bits = low_counter[1]
        if low_bits is None:
            return False
        return shift_bits == low_bits

    def _comparison_to_relation(self, operator: str, swapped: bool) -> Optional[str]:
        mapping = {
            "INT_SLESS": "<",
            "INT_SLESSEQUAL": "<=",
            "INT_LESS": "<",
            "INT_LESSEQUAL": "<=",
        }
        relation = mapping.get(operator)
        if relation is None:
            return None
        if not swapped:
            return relation
        if relation == "<":
            return ">"
        if relation == "<=":
            return ">="
        return None

    def _negate_relation(self, relation: str) -> Optional[str]:
        return {
            "<": ">=",
            "<=": ">",
            ">": "<=",
            ">=": "<",
        }.get(relation)

    def _build_closed_form(
        self,
        param_expr: Expression,
        lower_bound: int,
        coeff: int,
        bias: int,
        base_value: int,
    ) -> Optional[Expression]:
        size = param_expr.size or 4
        wide_size = self._summary_working_size(size)
        lower_const = Expression.constant(lower_bound, size)
        wide_param = self._zero_extend_bitpattern(param_expr, wide_size)
        wide_lower = self._zero_extend_bitpattern(lower_const, wide_size)
        shift_amount = Expression.constant(1, wide_size)

        triangular_n = self._triangular(wide_param, wide_size, shift_amount)
        if lower_bound == 0:
            triangular_delta = triangular_n
        else:
            triangular_lower = self._triangular(wide_lower, wide_size, shift_amount)
            triangular_delta = Expression.binary_op("INT_SUB", triangular_n, triangular_lower)
            triangular_delta.size = wide_size

        term_exprs: List[Expression] = []
        coeff_term = self._scale_term(triangular_delta, coeff, wide_size)
        if coeff_term is not None:
            term_exprs.append(coeff_term)
        if bias != 0:
            distance = Expression.binary_op("INT_SUB", wide_param, wide_lower)
            distance.size = wide_size
            bias_term = self._scale_term(distance, bias, wide_size)
            if bias_term is not None:
                term_exprs.append(bias_term)

        total = self._sum_terms(term_exprs, base_value, size, wide_size)
        return self._truncate_to_width(total, size)

    def _triangular(self, expr: Expression, size: int, shift_amount: Expression) -> Expression:
        one = Expression.constant(1, size)
        incremented = Expression.binary_op("INT_ADD", expr, one)
        incremented.size = size
        product = Expression.binary_op("INT_MULT", expr, incremented)
        product.size = size
        tri = Expression.binary_op("INT_RIGHT", product, shift_amount)
        tri.size = size
        return tri

    def _summary_working_size(self, narrow_size: int) -> int:
        narrow_bits = max(8, narrow_size * 8)
        wide_bits = max(64, narrow_bits * 2)
        return max(narrow_size, (wide_bits + 7) // 8)

    def _zero_extend_bitpattern(self, expr: Expression, target_size: int) -> Expression:
        source_size = expr.size or 0
        if source_size <= 0 or source_size >= target_size:
            copied = expr
            copied.size = max(source_size, target_size)
            if source_size > target_size:
                return self._truncate_to_width(copied, target_size)
            return copied
        widened = Expression.unary_op("INT_ZEXT", expr)
        widened.size = target_size
        return widened

    def _truncate_to_width(self, expr: Expression, target_size: int) -> Expression:
        if (expr.size or 0) <= target_size:
            expr.size = target_size
            return expr
        truncated = Expression.binary_op("SUBPIECE", expr, Expression.constant(0, 4))
        truncated.size = target_size
        return truncated

    def _scale_term(
        self,
        expr: Expression,
        factor: int,
        wide_size: int,
    ) -> Optional[Expression]:
        if factor == 0:
            return None
        if factor == 1:
            expr.size = wide_size
            return expr
        if factor == -1:
            negated = Expression.unary_op("INT_2COMP", expr)
            negated.size = wide_size
            return negated
        factor_const = self._zero_extend_bitpattern(Expression.constant(factor, expr.size or wide_size), wide_size)
        scaled = Expression.binary_op("INT_MULT", factor_const, expr)
        scaled.size = wide_size
        return scaled

    def _sum_terms(
        self,
        term_exprs: Sequence[Expression],
        base_value: int,
        size: int,
        wide_size: int,
    ) -> Expression:
        total: Optional[Expression] = None
        if base_value != 0:
            total = self._zero_extend_bitpattern(Expression.constant(base_value, size), wide_size)
        for term in term_exprs:
            if total is None:
                total = term
                continue
            total = Expression.binary_op("INT_ADD", total, term)
            total.size = wide_size
        if total is None:
            total = self._zero_extend_bitpattern(Expression.constant(0, size), wide_size)
        total.size = wide_size
        return total

    def _build_recursive_conditions(self, param_expr: Expression, lower_bound: int) -> Optional[List[Condition]]:
        size = param_expr.size or 4
        lower_const = Expression.constant(lower_bound, size)
        cond_expr = Expression.binary_op("INT_SLESS", lower_const, param_expr)
        return [Condition(cond_expr, False)]

    def _build_base_conditions(self, param_expr: Expression, lower_bound: int) -> Optional[List[Condition]]:
        size = param_expr.size or 4
        lower_const = Expression.constant(lower_bound, size)
        cond_expr = Expression.binary_op("INT_SLESSEQUAL", param_expr, lower_const)
        return [Condition(cond_expr, False)]

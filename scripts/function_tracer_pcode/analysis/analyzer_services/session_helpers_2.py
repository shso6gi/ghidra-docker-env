"""Stateless method implementations extracted from ``scripts.function_tracer_pcode.analysis.analyzer``."""

from __future__ import annotations

from typing import Any, Dict, List, Mapping, Optional, Sequence, Set, Tuple
from ._shared import (
    CallTargetRef,
    CanonicalLocation,
    Condition,
    ConditionNormalizer,
    ConditionSMTOracle,
    ConditionSimplifier,
    EffectSummary,
    Expression,
    ExpressionType,
    FunctionReturnAnalysis,
    Iterable,
    ReadonlyReductionRef,
    ReturnInfo,
    SignednessDetector,
    SignednessResult,
    StorageInfo,
    StructuralKey,
    StructuralRecurrenceSummarizer,
    UnknownValueRef,
    _PCODE_OPCODE_BY_MNEMONIC,
    _TrackedReturnValue,
    _expression_contains_observed_loads,
    _expression_location_ref,
    _expressions_equivalent,
    _expressions_equivalent_under_conditions,
    _iter_expression_nodes,
    _materialize_existing_effect_value_carrier,
    _resolve_call_target_ref,
    canonicalize_expr_read_location,
    cast,
    eval_constant_raw,
    expression_contains_post_state_reads,
    expression_key_safe,
    get_declared_type_signedness,
    is_void_data_type,
    lower_post_state_expression_for_smt,
    promote_observed_loads_to_post_state_reads,
    rewrite_observed_loads_from_effects,
)
from ._api import PcodeTracer

def _impl__signed_unit_constant_matches(self, value: int, expected: int, size: Optional[int]) -> bool:
    if value == expected:
        return True
    bits = max(1, int(size or 4)) * 8
    mask = (1 << bits) - 1
    return (int(value) & mask) == (int(expected) & mask)

def _impl__expressions_same_key(self, left: Optional[Expression], right: Optional[Expression]) -> bool:
    if left is None or right is None:
        return False
    try:
        return left.structural_key() == right.structural_key()
    except Exception:
        return False

def _impl__state_phi_feeds_positive_loop_guard(
    self,
    high_function,
    *,
    summarizer: StructuralRecurrenceSummarizer,
    header_block,
    backedge_indices: Sequence[int],
    state_phi,
    state_placeholder: Expression,
    target_conditions: Sequence[Condition],
    allow_latch_progress_guard: bool,
) -> bool:
    state_output = getattr(state_phi, "getOutput", lambda: None)()
    if state_output is None:
        return False
    positive_guard = Expression.binary_op("INT_SLESS", Expression.constant(0, size=state_placeholder.size or 4), state_placeholder)
    positive_guard.size = 1
    candidate_blocks = [header_block]
    try:
        in_size = int(getattr(header_block, "getInSize", lambda: 0)() or 0)
    except Exception:
        in_size = 0
    for backedge_index in backedge_indices or ():
        if 0 <= int(backedge_index) < in_size:
            try:
                predecessor = header_block.getIn(int(backedge_index))
            except Exception:
                predecessor = None
            if predecessor is not None and predecessor not in candidate_blocks:
                candidate_blocks.append(predecessor)
    header_key = self._block_debug_key(header_block)
    for block in candidate_blocks:
        cbranch = summarizer._find_cbranch_op(block)
        if cbranch is None or summarizer._safe_pcode_input_count(cbranch) < 2:
            continue
        if block is not header_block:
            successor_keys = {self._block_debug_key(successor) for successor in self._block_successors(block)}
            if header_key not in successor_keys:
                continue
        guard_expr = summarizer._build_pcode_expression(
            cbranch.getInput(1),
            placeholders={state_output: state_placeholder},
        )
        if guard_expr is None:
            continue
        if self._expressions_same_key(
            summarizer._canonicalize_expression(guard_expr),
            summarizer._canonicalize_expression(positive_guard),
        ):
            return True
        if allow_latch_progress_guard and self._expression_is_positive_after_unit_progress_guard(
            guard_expr,
            state_placeholder,
            target_conditions,
        ):
            return True
    return False

def _impl__expression_is_positive_after_unit_progress_guard(
    self,
    expr: Optional[Expression],
    state_placeholder: Expression,
    conditions: Sequence[Condition],
) -> bool:
    current = expr
    while (
        current is not None
        and getattr(current, "expr_type", None) == ExpressionType.UNARY_OP
        and getattr(current, "operator", None) in {"COPY", "CAST", "SUBPIECE", "INT_ZEXT", "INT_SEXT"}
        and len(tuple(getattr(current, "operands", ()) or ())) == 1
    ):
        current = tuple(getattr(current, "operands", ()) or ())[0]
    if current is None or getattr(current, "expr_type", None) != ExpressionType.BINARY_OP:
        return False
    if getattr(current, "operator", None) != "INT_SLESS":
        return False
    operands = tuple(getattr(current, "operands", ()) or ())
    if len(operands) != 2 or self._constant_int_value(operands[0]) != 0:
        return False
    right = operands[1]
    if self._expression_is_placeholder_minus_one_under_conditions(
        right,
        state_placeholder,
        conditions,
    ):
        return True
    if getattr(right, "expr_type", None) != ExpressionType.BINARY_OP:
        return False
    if getattr(right, "operator", None) != "INT_SUB":
        return False
    right_operands = tuple(getattr(right, "operands", ()) or ())
    if len(right_operands) != 2:
        return False
    return self._expressions_same_key(right_operands[0], state_placeholder) and self._expression_is_one_under_conditions(
        right_operands[1],
        conditions,
    )

def _impl__phi_circular_additive_signature(self, expr: Optional[Expression]) -> Optional[Tuple[int, int]]:
    if expr is None:
        return None
    if self._expression_contains_phi_circular_marker(expr):
        if getattr(expr, "expr_type", None) == ExpressionType.UNKNOWN:
            return (1, 0)
    expr_type = getattr(expr, "expr_type", None)
    if expr_type == ExpressionType.CONSTANT:
        value = self._constant_int_value(expr)
        if value is None:
            return None
        return (0, int(value))
    if expr_type == ExpressionType.UNARY_OP and getattr(expr, "operator", None) in {"COPY", "CAST", "SUBPIECE", "INT_ZEXT", "INT_SEXT"}:
        operands = tuple(getattr(expr, "operands", ()) or ())
        if len(operands) != 1:
            return None
        return self._phi_circular_additive_signature(operands[0])
    if expr_type != ExpressionType.BINARY_OP:
        return None
    operands = tuple(getattr(expr, "operands", ()) or ())
    if len(operands) != 2:
        return None
    left = self._phi_circular_additive_signature(operands[0])
    right = self._phi_circular_additive_signature(operands[1])
    if left is None or right is None:
        return None
    operator = getattr(expr, "operator", None)
    if operator == "INT_ADD":
        return (left[0] + right[0], left[1] + right[1])
    if operator == "INT_SUB":
        return (left[0] - right[0], left[1] - right[1])
    return None

def _impl__condition_is_param_minus_one_nonpositive(
    self,
    condition: Condition,
    param: Expression,
    target_conditions: Sequence[Condition] = (),
) -> bool:
    if condition is None:
        return False
    expr = getattr(condition, "expression", None)
    if expr is None or getattr(expr, "expr_type", None) != ExpressionType.BINARY_OP:
        return False
    operands = tuple(getattr(expr, "operands", ()) or ())
    if len(operands) != 2:
        return False
    operator = getattr(expr, "operator", None)
    if operator == "INT_SLESSEQUAL" and not getattr(condition, "negated", False):
        return self._branch_guarded_expression_is_param_minus_one(operands[0], param, target_conditions) and self._constant_int_value(operands[1]) == 0
    if operator == "INT_SLESS" and getattr(condition, "negated", False):
        return self._constant_int_value(operands[0]) == 0 and self._branch_guarded_expression_is_param_minus_one(operands[1], param, target_conditions)
    return False

def _impl__expression_is_one_under_conditions(
    self,
    expr: Optional[Expression],
    target_conditions: Sequence[Condition],
) -> bool:
    if self._constant_int_value(expr) == 1:
        return True
    current = expr
    while (
        current is not None
        and getattr(current, "expr_type", None) == ExpressionType.UNARY_OP
        and getattr(current, "operator", None) in {"INT_ZEXT", "INT_SEXT", "CAST", "COPY"}
        and len(tuple(getattr(current, "operands", ()) or ())) == 1
    ):
        current = tuple(getattr(current, "operands", ()) or ())[0]
    if current is None:
        return False
    if getattr(current, "expr_type", None) != ExpressionType.BINARY_OP:
        return False
    if getattr(current, "operator", None) == "INT_SLESS":
        operands = tuple(getattr(current, "operands", ()) or ())
        if (
            len(operands) == 2
            and self._constant_int_value(operands[1]) == 1
            and getattr(operands[0], "expr_type", None) == ExpressionType.PARAMETER
            and any(
                self._condition_is_signed_nonpositive_of_param(condition, operands[0])
                for condition in target_conditions or ()
            )
        ):
            return True
    as_condition = Condition(current, False)
    if any(
        existing is not None
        and (
            existing.equals(as_condition)
            or ConditionNormalizer.are_equivalent(existing, as_condition)
        )
        for existing in target_conditions or ()
    ):
        return True
    return self._conditions_imply(tuple(target_conditions or ()), (as_condition,))

def _impl__conditions_overlap(
    self,
    left: Sequence[Condition],
    right: Sequence[Condition],
) -> bool:
    for left_condition in left or ():
        if left_condition is None:
            continue
        for right_condition in right or ():
            if right_condition is None:
                continue
            if (
                left_condition.equals(right_condition.negate())
                or ConditionNormalizer.are_equivalent(left_condition, right_condition.negate())
                or left_condition.negate().equals(right_condition)
                or ConditionNormalizer.are_equivalent(left_condition.negate(), right_condition)
            ):
                return False
    try:
        return ConditionSMTOracle.conjunction_is_unsat(list(left or ()) + list(right or ())) is not True
    except Exception:
        return False

def _impl__conditions_imply(
    self,
    left: Sequence[Condition],
    right: Sequence[Condition],
) -> bool:
    for condition in right or ():
        if any(
            existing is not None
            and (
                existing.equals(condition)
                or ConditionNormalizer.are_equivalent(existing, condition)
            )
            for existing in left or ()
        ):
            continue
        try:
            if ConditionSMTOracle.conjunction_is_unsat(list(left or ()) + [condition.negate()]) is not True:
                return False
        except Exception:
            return False
    return True

def _impl__expressions_equal_under_conditions_smt(
    self,
    left: Optional[Expression],
    right: Optional[Expression],
    conditions: Sequence[Condition],
    parameters: Sequence[Dict],
) -> bool:
    if _expressions_equivalent_under_conditions(left, right, conditions, parameters):
        return True
    if left is None or right is None:
        return False
    equality = Condition(Expression.binary_op("INT_NOTEQUAL", left, right), False)
    try:
        return ConditionSMTOracle.conjunction_is_unsat(list(conditions or ()) + [equality]) is True
    except Exception:
        return False

def _impl__reachable_cycle_keys(
    self,
    reachable: Set[Any],
    adjacency: Mapping[Any, Sequence[Any]],
) -> Set[Any]:
    visiting: Set[Any] = set()
    visited: Set[Any] = set()
    cycle_nodes: Set[Any] = set()

    def dfs(key: Any, path: List[Any]) -> None:
        if key in visiting:
            try:
                start = path.index(key)
                cycle_nodes.update(path[start:])
            except ValueError:
                cycle_nodes.add(key)
            return
        if key in visited:
            return
        visiting.add(key)
        path.append(key)
        for successor in adjacency.get(key, ()) or ():
            if successor in reachable:
                dfs(successor, path)
        path.pop()
        visiting.remove(key)
        visited.add(key)

    for key in sorted(reachable, key=str):
        dfs(key, [])
    return cycle_nodes

def _impl__condition_contradicts_any(
    self,
    condition: Condition,
    others: Sequence[Condition],
) -> bool:
    if condition is None:
        return False
    for other in others or ():
        if other is None:
            continue
        try:
            if (
                condition.equals(other.negate())
                or condition.negate().equals(other)
                or ConditionNormalizer.are_equivalent(condition, other.negate())
                or ConditionNormalizer.are_equivalent(condition.negate(), other)
            ):
                return True
        except Exception:
            continue
    try:
        return ConditionSMTOracle.conjunction_is_unsat(list(others or ()) + [condition]) is True
    except Exception:
        return False

def _impl__parameter_expression(
    self,
    analysis: FunctionReturnAnalysis,
    index: int,
) -> Optional[Expression]:
    params = list(getattr(analysis, "parameters", []) or [])
    if index < 0 or index >= len(params):
        return None
    param = dict(params[index] or {})
    size = int(param.get("size", 0) or 4)
    return Expression.parameter(
        str(param.get("name") or f"param_{index + 1}"),
        index=index,
        data_type=param.get("data_type"),
        data_type_obj=param.get("data_type_obj"),
        size=max(1, size),
    )

def _impl__signed_positive_condition(self, expr: Expression) -> Condition:
    zero = Expression.constant(0, max(1, int(expr.size or 4)))
    return Condition(Expression.binary_op("INT_SLESS", zero, expr), False)

def _impl__condition_is_signed_nonpositive_of_param(self, condition: Condition, param: Expression) -> bool:
    if condition is None or not getattr(condition, "negated", False):
        return False
    expr = getattr(condition, "expression", None)
    if expr is None or expr.expr_type != ExpressionType.BINARY_OP or expr.operator != "INT_SLESS":
        return False
    operands = list(getattr(expr, "operands", None) or ())
    if len(operands) != 2:
        return False
    left, right = operands
    return self._constant_int_value(left) == 0 and self._expression_is_same_parameter_ignoring_subpiece(right, param)

def _impl__condition_is_signed_positive_of_param(self, condition: Condition, param: Expression) -> bool:
    if condition is None or getattr(condition, "negated", False):
        return False
    expr = getattr(condition, "expression", None)
    if expr is None or expr.expr_type != ExpressionType.BINARY_OP or expr.operator != "INT_SLESS":
        return False
    operands = list(getattr(expr, "operands", None) or ())
    if len(operands) != 2:
        return False
    left, right = operands
    return self._constant_int_value(left) == 0 and self._expression_is_same_parameter_ignoring_subpiece(right, param)

def _impl__condition_is_signed_less_than_one_of_param(self, condition: Condition, param: Expression) -> bool:
    if condition is None or getattr(condition, "negated", False):
        return False
    expr = getattr(condition, "expression", None)
    if expr is None or expr.expr_type != ExpressionType.BINARY_OP or expr.operator != "INT_SLESS":
        return False
    operands = list(getattr(expr, "operands", None) or ())
    if len(operands) != 2:
        return False
    left, right = operands
    return self._expression_is_same_parameter_ignoring_subpiece(left, param) and self._constant_int_value(right) == 1

def _impl__condition_is_param_equal_const(self, condition: Condition, param: Expression, value: int) -> bool:
    if condition is None:
        return False
    expr = getattr(condition, "expression", None)
    if expr is None or expr.expr_type != ExpressionType.BINARY_OP:
        return False
    operator = getattr(expr, "operator", None)
    negated = bool(getattr(condition, "negated", False))
    if operator == "INT_NOTEQUAL" and negated:
        pass
    elif operator == "INT_EQUAL" and not negated:
        pass
    else:
        return False
    operands = list(getattr(expr, "operands", None) or ())
    if len(operands) != 2:
        return False
    left, right = operands
    if (
        self._expression_is_same_parameter_ignoring_subpiece(left, param)
    ) and self._constant_int_value(right) == value:
        return True
    if (
        self._expression_is_same_parameter_ignoring_subpiece(right, param)
    ) and self._constant_int_value(left) == value:
        return True
    return False

def _impl__coerce_expression_size(self, expr: Expression, size: int) -> Expression:
    if int(getattr(expr, "size", 0) or 0) == int(size or 0):
        return expr
    return expr.clone_with(size=max(1, int(size or getattr(expr, "size", 0) or 4)))

def _impl__expression_is_param_minus_one(self, expr: Expression, param: Expression) -> bool:
    if expr is None or expr.expr_type != ExpressionType.BINARY_OP or expr.operator not in {"INT_ADD", "INT_SUB"}:
        return False
    if len(expr.operands or ()) != 2:
        return False
    left, right = expr.operands
    if not self._expression_is_same_parameter(left, param):
        return False
    if right.expr_type != ExpressionType.CONSTANT:
        return False
    try:
        value = int(right.value)
    except (TypeError, ValueError):
        return False
    bits = max(1, int(getattr(left, "size", 0) or getattr(expr, "size", 0) or 4)) * 8
    mask = (1 << bits) - 1
    if expr.operator == "INT_SUB":
        return value == 1
    return (value & mask) == mask

def _impl__expression_is_same_parameter(self, expr: Expression, param: Expression) -> bool:
    if expr is None or param is None:
        return False
    if expr.expr_type != ExpressionType.PARAMETER or param.expr_type != ExpressionType.PARAMETER:
        return False
    expr_index = getattr(expr, "value", None)
    param_index = getattr(param, "value", None)
    if isinstance(expr_index, int) and isinstance(param_index, int) and expr_index >= 0 and param_index >= 0:
        return expr_index == param_index
    return (getattr(expr, "name", None) or "") == (getattr(param, "name", None) or "")

def _impl__expression_is_same_parameter_ignoring_subpiece(self, expr: Expression, param: Expression) -> bool:
    current = expr
    if (
        current is not None
        and current.expr_type == ExpressionType.BINARY_OP
        and current.operator == "SUBPIECE"
        and current.operands
    ):
        current = current.operands[0]
    return self._expression_is_same_parameter(current, param)

def _impl__expression_contains_phi_circular(self, expr: Optional[Expression]) -> bool:
    if expr is None:
        return False
    if expr.expr_type == ExpressionType.UNKNOWN and "phi_circular" in str(getattr(expr, "value", "")):
        return True
    runtime_ref = getattr(expr, "runtime_ref", None)
    if getattr(runtime_ref, "reason", None) == "phi_circular" or getattr(runtime_ref, "kind", None) == "phi_circular":
        return True
    return any(self._expression_contains_phi_circular(operand) for operand in getattr(expr, "operands", []) or [])

def _impl__conditions_equivalent(
    self,
    left: Sequence[Condition],
    right: Sequence[Condition],
) -> bool:
    left_conditions = tuple(left or ())
    right_conditions = tuple(right or ())
    left_implies_right = ConditionSMTOracle.conjunction_is_unsat(
        list(left_conditions) + [condition.negate() for condition in right_conditions]
    )
    right_implies_left = ConditionSMTOracle.conjunction_is_unsat(
        list(right_conditions) + [condition.negate() for condition in left_conditions]
    )
    return left_implies_right is True and right_implies_left is True

def _impl__high_function_has_cfg_cycle(self, high_function) -> bool:
    blocks = list(self._iter_high_basic_blocks(high_function))
    block_keys = {self._block_debug_key(block) for block in blocks}
    visiting: Set[Any] = set()
    visited: Set[Any] = set()

    def visit(block) -> bool:
        key = self._block_debug_key(block)
        if key in visiting:
            return True
        if key in visited:
            return False
        visiting.add(key)
        for succ in self._block_successors(block):
            if self._block_debug_key(succ) not in block_keys:
                continue
            if visit(succ):
                return True
        visiting.remove(key)
        visited.add(key)
        return False

    for block in blocks:
        if visit(block):
            return True
    return False

def _impl__analysis_needs_wrapper_recovery(
    self,
    analysis: Optional[FunctionReturnAnalysis],
) -> bool:
    if analysis is None or not analysis.returns:
        return False
    return analysis.has_unknown_return() or analysis.has_unresolved_return_value()

def _impl__get_pcode_opcode(self, pcode_op) -> Optional[int]:
    if pcode_op is None:
        return None
    get_opcode = getattr(pcode_op, "getOpcode", None)
    if callable(get_opcode):
        try:
            return int(get_opcode())
        except Exception:
            pass
    get_mnemonic = getattr(pcode_op, "getMnemonic", None)
    if callable(get_mnemonic):
        try:
            mnemonic = str(get_mnemonic())
        except Exception:
            mnemonic = ""
        return _PCODE_OPCODE_BY_MNEMONIC.get(mnemonic)
    return None

def _impl__pcode_op_debug_name(self, pcode_op) -> str:
    if pcode_op is None:
        return "<none>"
    get_mnemonic = getattr(pcode_op, "getMnemonic", None)
    if callable(get_mnemonic):
        try:
            return str(get_mnemonic())
        except Exception:
            return "<pcode>"
    return "<pcode>"

def _impl__pcode_op_affects_tracked_storage(
    self,
    pcode_op,
    target_storage: Optional[StorageInfo],
    tracer: Optional[PcodeTracer],
    current_function=None,
) -> bool:
    if pcode_op is None or target_storage is None or tracer is None:
        return False

    output = getattr(pcode_op, "getOutput", lambda: None)()
    if output is not None:
        output_storage = None
        try:
            output_storage = tracer._get_storage_info_from_varnode(output)
        except Exception:
            output_storage = None
        if output_storage is not None and self._storages_overlap_for_return_recovery(
            output_storage,
            target_storage,
        ):
            return True

    if not self._is_pcode_call_op(pcode_op):
        return False

    for return_storage in self._get_implicit_return_target_storages(current_function, tracer):
        if self._storages_overlap_for_return_recovery(target_storage, return_storage):
            return True
    return False

def _impl__propagate_passthrough_input_from_op(
    self,
    pcode_op,
    tracer: Optional[PcodeTracer],
) -> List[_TrackedReturnValue]:
    input_varnode = getattr(pcode_op, "getInput", lambda _idx: None)(0)
    if input_varnode is None:
        return []
    return [self._make_tracked_return_value(input_varnode, tracer)]

def _impl__is_zero_constant_varnode(self, varnode) -> bool:
    if varnode is None:
        return False
    is_constant = getattr(varnode, "isConstant", None)
    if callable(is_constant):
        try:
            if bool(is_constant()):
                return int(varnode.getOffset()) == 0
        except Exception:
            pass
    address = getattr(varnode, "getAddress", lambda: None)()
    if address is not None:
        is_constant_address = getattr(address, "isConstantAddress", None)
        if callable(is_constant_address):
            try:
                if bool(is_constant_address()):
                    return int(address.getOffset()) == 0
            except Exception:
                pass
    return False

def _impl__parameter_storages_overlap_for_passthrough(
    self,
    caller_storage: Optional[Dict],
    callee_storage: Optional[Dict],
) -> bool:
    caller = self._coerce_wrapper_storage_info(caller_storage)
    callee = self._coerce_wrapper_storage_info(callee_storage)
    if caller is None or callee is None:
        return False
    if not caller.is_register or not callee.is_register:
        return False
    try:
        return (
            caller.shares_base_register_with(callee)
            and caller.bit_range_overlaps_with(callee)
        )
    except Exception:
        return False

def _impl__parameter_storages_match_for_passthrough(
    self,
    caller_storage: Optional[Dict],
    callee_storage: Optional[Dict],
) -> bool:
    caller = self._coerce_wrapper_storage_info(caller_storage)
    callee = self._coerce_wrapper_storage_info(callee_storage)
    if caller is None or callee is None:
        return False
    if not caller.is_register or not callee.is_register:
        return False
    if not caller.shares_base_register_with(callee):
        return False
    if int(caller.bit_offset_in_base or 0) != int(callee.bit_offset_in_base or 0):
        return False
    caller_bits = int(caller.size_bits or (caller.size or 0) * 8)
    callee_bits = int(callee.size_bits or (callee.size or 0) * 8)
    return caller_bits == callee_bits and caller_bits > 0

def _impl__coerce_wrapper_storage_info(self, storage: Optional[object]) -> Optional[StorageInfo]:
    if storage is None:
        return None
    if isinstance(storage, StorageInfo):
        return storage
    if isinstance(storage, dict):
        try:
            return StorageInfo(
                is_register=bool(storage.get("is_register", False)),
                space_name=str(storage.get("space_name", "")),
                space_id=self._coerce_optional_int(storage.get("space_id")),
                offset=int(storage.get("offset", 0)),
                size=int(storage.get("size", 0)),
                size_bits=int(storage.get("size_bits", 0)),
                register_name=storage.get("register_name"),
                register_offset=self._coerce_optional_int(storage.get("register_offset")),
                register_size=self._coerce_optional_int(storage.get("register_size")),
                register_size_bits=self._coerce_optional_int(storage.get("register_size_bits")),
                base_register_name=storage.get("base_register_name"),
                base_register_offset=int(storage.get("base_register_offset", 0)),
                base_register_size=int(storage.get("base_register_size", 0)),
                base_register_size_bits=int(storage.get("base_register_size_bits", 0)),
                bit_offset_in_base=int(storage.get("bit_offset_in_base", 0)),
                is_stack_pointer=bool(storage.get("is_stack_pointer", False)),
                is_frame_pointer=bool(storage.get("is_frame_pointer", False)),
            )
        except Exception:
            return None
    return None

def _impl__parameter_descriptor_quality(self, parameters: Optional[List[Dict]]) -> Tuple[int, int, int, int]:
    params = list(parameters or [])
    return (
        len(params),
        sum(1 for param in params if param.get("storage")),
        sum(1 for param in params if param.get("data_type")),
        sum(1 for param in params if int(param.get("size", 0) or 0) > 0),
    )

def _impl__choose_richer_parameter_descriptors(
    self,
    cached_parameters: Optional[List[Dict]],
    fresh_parameters: Optional[List[Dict]],
) -> List[Dict]:
    cached = list(cached_parameters or [])
    fresh = list(fresh_parameters or [])
    if self._parameter_descriptor_quality(fresh) > self._parameter_descriptor_quality(cached):
        return fresh
    return cached

def _impl__function_cache_key(self, function) -> Optional[Tuple[Any, ...]]:
    if function is None:
        return None
    try:
        return (str(function.getEntryPoint()),)
    except Exception:
        return None

def _impl__analysis_scope_key(
    self,
    target,
    bound_parameter_values: Optional[Dict[int, Expression]] = None,
    bound_parameter_storage_values: Optional[Dict[Tuple[Any, ...], Expression]] = None,
) -> Tuple[Any, ...]:
    target_ref = self._coerce_runtime_target_ref(target)
    if target_ref is None and target is not None:
        try:
            if hasattr(target, "getEntryPoint"):
                target_ref = CallTargetRef.from_function(target)
        except Exception:
            target_ref = None
    target_key = (
        self._target_active_key(target_ref)
        if target_ref is not None
        else self._function_cache_key(target)
    ) or ("unknown_target",)
    normalized_bound_parameter_values = self._normalize_bound_parameter_values(
        bound_parameter_values,
    )
    bound_signature = tuple(
        (
            int(index),
            ConditionNormalizer.expression_signature(
                expr,
                include_memory_read_order=False,
            ),
        )
        for index, expr in sorted(normalized_bound_parameter_values.items())
    )
    normalized_bound_parameter_storage_values = self._normalize_bound_parameter_storage_values(
        bound_parameter_storage_values,
    )
    storage_bound_signature = tuple(
        (
            tuple(key),
            ConditionNormalizer.expression_signature(
                expr,
                include_memory_read_order=False,
            ),
        )
        for key, expr in sorted(
            normalized_bound_parameter_storage_values.items(),
            key=lambda item: repr(item[0]),
        )
    )
    return ("analysis_scope", target_key, bound_signature, storage_bound_signature)

def _impl__extend_active_functions(
    self,
    active_functions: Optional[Set[Tuple[Any, ...]]],
    target_ref: Optional[CallTargetRef],
) -> Set[Tuple[Any, ...]]:
    scoped = set(active_functions or set())
    active_key = self._target_active_key(target_ref)
    if active_key is not None:
        scoped.add(active_key)
    return scoped

def _impl__augment_parameters_with_implicit_passthrough(
    self,
    parameters: List[Dict],
    tracer: Any,
    active_functions: Set[Tuple[Any, ...]],
) -> List[Dict]:
    augmented = [dict(param) for param in (parameters or [])]
    changed = False

    try:
        pcode_ops = list(tracer.get_all_pcode_ops())
    except Exception:
        return augmented

    for op in pcode_ops:
        try:
            if op.getMnemonic() not in {"CALL", "CALLIND"} or op.getNumInputs() < 1:
                continue
        except Exception:
            continue

        target_ref = _resolve_call_target_ref(tracer, op)
        if target_ref is None:
            continue
        active_key = self._target_active_key(target_ref)
        if target_ref.is_unknown():
            continue
        if active_key is not None and active_key in active_functions:
            continue

        explicit_count = max(0, int(op.getNumInputs()) - 1)
        callee_parameters = self._get_freshest_callee_parameters(target_ref)
        if len(callee_parameters) <= explicit_count:
            continue

        for callee_param in callee_parameters[explicit_count:]:
            callee_storage = self._coerce_wrapper_storage_info(callee_param.get("storage"))
            if callee_storage is None or not callee_storage.is_register:
                continue
            if any(
                self._parameter_storages_overlap_for_passthrough(
                    existing.get("storage"),
                    callee_param.get("storage"),
                )
                for existing in augmented
            ):
                continue
            if not self._should_synthesize_implicit_passthrough_for_call(
                tracer,
                op,
                callee_storage,
            ):
                continue
            augmented.append(
                self._synthesize_implicit_passthrough_parameter(
                    augmented,
                    callee_param,
                    callee_storage,
                )
            )
            changed = True

    if changed:
        augmented.sort(key=lambda param: int(param.get("index", 1 << 20)))
    return augmented

def _impl__has_non_parameter_symbol_for_storage(
    self,
    tracer: PcodeTracer,
    target_storage: StorageInfo,
) -> bool:
    high_function = getattr(tracer, "high_function", None)
    if high_function is None:
        return False
    try:
        local_map = high_function.getLocalSymbolMap()
    except Exception:
        return False
    if local_map is None:
        return False

    for sym in local_map.getSymbols() or []:
        try:
            if sym.isParameter():
                continue
        except Exception:
            continue
        candidate_storage = self._coerce_wrapper_storage_info(self._get_storage_info(sym))
        if candidate_storage is None or not candidate_storage.is_register:
            continue
        try:
            same_base = candidate_storage.shares_base_register_with(target_storage)
            overlaps = candidate_storage.bit_range_overlaps_with(target_storage)
        except Exception:
            same_base = False
            overlaps = False
        if same_base and overlaps:
            return True
    return False

def _impl__coerce_order_key(self, value: object) -> Optional[int]:
    if value is None:
        return None
    if isinstance(value, bool):
        return int(value)
    if isinstance(value, int):
        return value
    try:
        return int(cast(Any, value))
    except Exception:
        return None

def _impl__synthesize_implicit_passthrough_parameter(
    self,
    current_parameters: List[Dict],
    callee_param: Dict,
    callee_storage: StorageInfo,
) -> Dict:
    used_names = {param.get("name") for param in current_parameters if param.get("name")}
    next_index = max((int(param.get("index", -1)) for param in current_parameters), default=-1) + 1
    suggested_name = callee_param.get("name") or f"param_{next_index + 1}"
    if suggested_name in used_names:
        suggested_name = f"param_{next_index + 1}"

    return {
        "name": suggested_name,
        "index": next_index,
        "size": callee_param.get("size") or callee_storage.size or 0,
        "data_type": callee_param.get("data_type"),
        "data_type_obj": callee_param.get("data_type_obj"),
        "is_signed": callee_param.get("is_signed", True),
        "storage": callee_storage.to_dict(),
        "implicit_passthrough": True,
    }

def _impl__clone_expression(self, expr: Expression) -> Expression:
    return expr.clone_with(operands=[self._clone_expression(op) for op in expr.operands])

def _impl__make_tracer(
    self,
    high_function,
    *,
    bound_parameter_values: Optional[Dict[int, Expression]] = None,
    bound_parameter_storage_values: Optional[Dict[Tuple[Any, ...], Expression]] = None,
) -> PcodeTracer:
    try:
        return PcodeTracer(
            self.program,
            high_function,
            debug=self.debug,
            bound_parameter_values=bound_parameter_values,
            bound_parameter_storage_values=bound_parameter_storage_values,
            binary_id=self._binary_id,
        )
    except TypeError:
        return PcodeTracer(
            self.program,
            high_function,
            debug=self.debug,
        )

def _impl__analysis_is_fully_argument_specialized(
    self,
    analysis: Optional[FunctionReturnAnalysis],
) -> bool:
    if analysis is None:
        return False
    parameter_count = len(getattr(analysis, "parameters", ()) or ())
    if parameter_count <= 0:
        return False
    scope_key = getattr(analysis, "analysis_scope_key", None)
    if not isinstance(scope_key, tuple) or len(scope_key) < 4:
        return False
    bound_by_index = scope_key[2] if isinstance(scope_key[2], tuple) else ()
    bound_by_storage = scope_key[3] if isinstance(scope_key[3], tuple) else ()
    return bool(bound_by_index or bound_by_storage)

def _impl__local_varnode_key(self, varnode) -> Tuple[str, int, int]:
    try:
        addr = varnode.getAddress()
        return (addr.getAddressSpace().getName(), int(varnode.getOffset()), int(varnode.getSize()))
    except Exception:
        return ("synthetic", id(varnode), int(getattr(varnode, "getSize", lambda: 0)()))

def _impl__evaluate_local_varnode_expression(
    self,
    varnode,
    tracer,
    local_values: Dict[Tuple[str, int, int], Expression],
    local_storages: Dict[Tuple[str, int, int], Any],
    local_memory: Dict[Tuple[StructuralKey, int], Expression],
    visiting: Optional[Set[int]] = None,
) -> Expression:
    if varnode is None:
        return Expression.unknown("local_none")

    key = self._local_varnode_key(varnode)
    cached = local_values.get(key)
    if cached is not None:
        return cached

    aliased = self._lookup_local_alias_expression(varnode, tracer, local_values, local_storages)
    if aliased is not None:
        local_values[key] = aliased
        return aliased

    is_constant = getattr(varnode, "isConstant", None)
    if callable(is_constant) and is_constant():
        return Expression.constant(varnode.getOffset(), varnode.getSize())

    if visiting is None:
        visiting = set()
    marker = id(varnode)
    if marker in visiting:
        return Expression.unknown("local_cycle")
    visiting.add(marker)
    try:
        get_def = getattr(varnode, "getDef", None)
        def_op = get_def() if callable(get_def) else None
        if def_op is not None:
            evaluated = self._evaluate_local_pcode_expression(
                def_op,
                tracer,
                local_values,
                local_storages,
                local_memory,
                visiting,
            )
            if evaluated is not None:
                local_values[key] = evaluated
                return evaluated
    finally:
        visiting.discard(marker)

    return tracer.trace_varnode(varnode, use_cache=False)

def _impl__evaluate_local_pcode_expression(
    self,
    pcode_op,
    tracer,
    local_values: Dict[Tuple[str, int, int], Expression],
    local_storages: Dict[Tuple[str, int, int], Any],
    local_memory: Dict[Tuple[StructuralKey, int], Expression],
    visiting: Optional[Set[int]] = None,
) -> Optional[Expression]:
    mnemonic = pcode_op.getMnemonic()

    def _input(index: int) -> Expression:
        return self._evaluate_local_varnode_expression(
            pcode_op.getInput(index),
            tracer,
            local_values,
            local_storages,
            local_memory,
            visiting,
        )

    if mnemonic in {"COPY", "CAST"} and pcode_op.getNumInputs() >= 1:
        expr = _input(0)
        output = pcode_op.getOutput()
        if output is not None:
            expr = self._clone_expression(expr)
            expr.size = output.getSize()
        return expr

    binary_ops = {
        "INT_ADD", "INT_SUB", "INT_MULT", "INT_DIV", "INT_SDIV",
        "INT_REM", "INT_SREM", "INT_AND", "INT_OR", "INT_XOR",
        "INT_LEFT", "INT_RIGHT", "INT_SRIGHT",
        "INT_EQUAL", "INT_NOTEQUAL", "INT_LESS", "INT_SLESS",
        "INT_LESSEQUAL", "INT_SLESSEQUAL",
        "FLOAT_ADD", "FLOAT_SUB", "FLOAT_MULT", "FLOAT_DIV",
        "FLOAT_EQUAL", "FLOAT_NOTEQUAL", "FLOAT_LESS", "FLOAT_LESSEQUAL",
        "BOOL_AND", "BOOL_OR", "BOOL_XOR", "PIECE", "SUBPIECE",
        "PTRADD", "PTRSUB",
    }
    if mnemonic in binary_ops and pcode_op.getNumInputs() >= 2:
        if mnemonic == "PTRADD" and pcode_op.getNumInputs() >= 3:
            base = _input(0)
            index = _input(1)
            element_size = _input(2)
            return Expression.binary_op(
                "INT_ADD",
                base,
                Expression.binary_op("INT_MULT", index, element_size),
            )
        return Expression.binary_op(mnemonic, _input(0), _input(1))

    unary_ops = {
        "INT_NEGATE", "INT_2COMP", "BOOL_NEGATE", "INT_ZEXT", "INT_SEXT",
        "FLOAT_NEG", "FLOAT_ABS", "FLOAT_SQRT",
        "TRUNC", "FLOAT_FLOAT2FLOAT", "FLOAT_INT2FLOAT", "FLOAT_CEIL", "FLOAT_FLOOR",
        "POPCOUNT", "LZCOUNT",
    }
    if mnemonic in unary_ops and pcode_op.getNumInputs() >= 1:
        expr = Expression.unary_op(mnemonic, _input(0))
        output = pcode_op.getOutput()
        if output is not None:
            expr.size = output.getSize()
        return expr

    if mnemonic == "LOAD" and pcode_op.getNumInputs() >= 2:
        output = pcode_op.getOutput()
        size = output.getSize() if output is not None else 4
        addr_expr = _input(1)
        cached = local_memory.get(self._local_memory_key(addr_expr, size))
        if cached is not None:
            return cached
        return Expression.memory(addr_expr, size)

    return None

def _impl__lookup_local_alias_expression(
    self,
    varnode,
    tracer,
    local_values: Dict[Tuple[str, int, int], Expression],
    local_storages: Dict[Tuple[str, int, int], Any],
) -> Optional[Expression]:
    try:
        target_storage = tracer._get_storage_info_from_varnode(varnode)
    except Exception:
        return None
    if target_storage is None or not getattr(target_storage, "is_register", False):
        return None

    for key, candidate_storage in local_storages.items():
        if candidate_storage is None:
            continue
        try:
            same_base = candidate_storage.shares_base_register_with(target_storage)
            overlaps = candidate_storage.bit_range_overlaps_with(target_storage)
        except Exception:
            continue
        if not same_base or not overlaps:
            continue
        candidate_expr = local_values.get(key)
        if candidate_expr is None:
            continue
        aliased = self._clone_expression(candidate_expr)
        aliased.size = target_storage.size
        self._debug_print(
            "Local alias resolution: "
            f"{getattr(candidate_storage, 'register_name', None)} -> "
            f"{getattr(target_storage, 'register_name', None)} as {aliased.to_string()}"
        )
        return aliased
    return None

def _impl__lookup_local_expression_for_storage(
    self,
    target_storage: Optional[StorageInfo],
    local_values: Dict[Tuple[str, int, int], Expression],
    local_storages: Dict[Tuple[str, int, int], Any],
) -> Optional[Expression]:
    if target_storage is None or not getattr(target_storage, "is_register", False):
        return None

    best_expr: Optional[Expression] = None
    best_score: Optional[Tuple[int, int, int, int]] = None

    for key, candidate_storage in local_storages.items():
        if candidate_storage is None:
            continue
        try:
            same_base = candidate_storage.shares_base_register_with(target_storage)
            overlaps = candidate_storage.bit_range_overlaps_with(target_storage)
        except Exception:
            continue
        if not same_base or not overlaps:
            continue

        candidate_expr = local_values.get(key)
        if candidate_expr is None:
            continue

        candidate_size = int(getattr(candidate_storage, "size", 0) or 0)
        target_size = int(getattr(target_storage, "size", 0) or 0)
        candidate_offset = int(getattr(candidate_storage, "bit_offset_in_base", 0) or 0)
        target_offset = int(getattr(target_storage, "bit_offset_in_base", 0) or 0)
        score = (
            1 if candidate_offset == target_offset else 0,
            1 if candidate_size == target_size else 0,
            min(candidate_size, target_size),
            -abs(candidate_offset - target_offset),
        )
        if best_score is not None and score <= best_score:
            continue

        aliased = self._clone_expression(candidate_expr)
        aliased.size = max(1, target_size or getattr(aliased, "size", 0) or 0)
        best_expr = aliased
        best_score = score

    return best_expr

def _impl__deduplicate_storage_infos(
    self,
    storages: List[StorageInfo],
) -> List[StorageInfo]:
    deduped: List[StorageInfo] = []
    seen: Set[Tuple[Any, ...]] = set()
    for storage in storages:
        key = (
            bool(getattr(storage, "is_register", False)),
            getattr(storage, "space_name", None),
            getattr(storage, "offset", None),
            getattr(storage, "size", None),
            getattr(storage, "size_bits", None),
            getattr(storage, "register_name", None),
            getattr(storage, "base_register_name", None),
            getattr(storage, "bit_offset_in_base", None),
        )
        if key in seen:
            continue
        seen.add(key)
        deduped.append(storage)
    return deduped

def _impl__get_instruction_with_fallback(self, addr):
    listing = self.program.getListing()
    instruction = listing.getInstructionAt(addr)
    if instruction is not None:
        return instruction

    containing_instruction = getattr(listing, "getInstructionContaining", None)
    if callable(containing_instruction):
        instruction = containing_instruction(addr)
        if instruction is not None:
            return instruction

    if self._attempt_disassemble_at(addr):
        instruction = listing.getInstructionAt(addr)
        if instruction is not None:
            return instruction
        if callable(containing_instruction):
            instruction = containing_instruction(addr)
            if instruction is not None:
                return instruction

    return None

def _impl__attempt_disassemble_at(self, addr) -> bool:
    try:
        from ghidra.app.cmd.disassemble import DisassembleCommand  # type: ignore[import]
    except Exception:
        self._debug_print(f"Local target disassembly unavailable at {addr}: import failed")
        return False

    try:
        command = DisassembleCommand(addr, None, True)
    except TypeError:
        try:
            command = DisassembleCommand(addr, None)
        except Exception as exc:
            self._debug_print(f"Local target disassembly setup failed at {addr}: {exc}")
            return False
    except Exception as exc:
        self._debug_print(f"Local target disassembly setup failed at {addr}: {exc}")
        return False

    try:
        with self._program_transaction(f"Disassemble local target {addr}"):
            applied = command.applyTo(self.program)
    except Exception as exc:
        self._debug_print(f"Local target disassembly failed at {addr}: {exc}")
        return False

    if applied:
        self._debug_print(f"Local target disassembly materialized instructions at {addr}")
    else:
        self._debug_print(f"Local target disassembly produced no instructions at {addr}")
    return bool(applied)

def _impl__expression_contains_phi(self, expr: Optional[Expression]) -> bool:
    if expr is None:
        return False
    if expr.expr_type == ExpressionType.PHI:
        return True
    for operand in getattr(expr, "operands", []) or []:
        if self._expression_contains_phi(operand):
            return True
    return False

def _impl__collect_expression_object_keys(
    self,
    expr: Optional[Expression],
    out: Set[Tuple[object, ...]],
) -> None:
    if expr is None:
        return
    key = expression_key_safe(expr, include_memory_read_order=False)
    if key is not None:
        out.add(key)
    if expr.expr_type == ExpressionType.PHI and expr.value:
        for cond, value in expr.value:
            if cond is not None:
                self._collect_expression_object_keys(cond.expression, out)
            self._collect_expression_object_keys(value, out)
        return
    for operand in expr.operands or []:
        self._collect_expression_object_keys(operand, out)

def _impl__expression_references_only_allowed_objects(
    self,
    expr: Optional[Expression],
    args: List[Expression],
) -> bool:
    if expr is None:
        return True

    allowed_subtrees: Set[Tuple[object, ...]] = set()
    for arg in args or []:
        self._collect_expression_object_keys(arg, allowed_subtrees)
    return self._expression_references_allowed_subtrees(expr, allowed_subtrees)

def _impl__expression_references_allowed_subtrees(
    self,
    expr: Optional[Expression],
    allowed_subtrees: Set[Tuple[object, ...]],
) -> bool:
    if expr is None:
        return True
    expr_key = expression_key_safe(expr, include_memory_read_order=False)
    if expr_key in allowed_subtrees:
        return True

    if expr.expr_type == ExpressionType.UNKNOWN:
        runtime_ref = getattr(expr, "runtime_ref", None)
        return getattr(runtime_ref, "deferred_call_ref", None) is not None
    if expr.expr_type == ExpressionType.CALL:
        return False

    if expr.expr_type in {ExpressionType.CONSTANT, ExpressionType.LITERAL}:
        return True

    if expr.expr_type in {ExpressionType.PARAMETER, ExpressionType.VARIABLE}:
        if getattr(expr, "runtime_ref", None) is not None:
            return True
        return False

    if expr.expr_type == ExpressionType.PHI and expr.value:
        for cond, value in expr.value:
            if cond is not None and not self._expression_references_allowed_subtrees(
                cond.expression,
                allowed_subtrees,
            ):
                return False
            if not self._expression_references_allowed_subtrees(value, allowed_subtrees):
                return False
        return True

    if expr.expr_type == ExpressionType.MEMORY and not expr.operands:
        return getattr(expr, "runtime_ref", None) is not None

    for operand in expr.operands or []:
        if not self._expression_references_allowed_subtrees(operand, allowed_subtrees):
            return False
    return True

def _impl__detect_signedness(self, high_function) -> Optional[SignednessResult]:
    """
    Phase 1: P-code証拠から符号性を推定

    Args:
        high_function: GhidraのHighFunctionオブジェクト

    Returns:
        SignednessResult: 推定結果（エラー時はNone）
    """
    try:
        detector = SignednessDetector(high_function, debug=self.debug)
        evidence = detector.detect()
        return SignednessResult.from_evidence(evidence)
    except Exception as e:
        self._debug_print(f"Signedness detection failed: {e}")
        return None

def _impl__collect_parameters(self, high_function) -> List[Dict]:
    """パラメータ情報を収集（ストレージ情報付き）"""
    params = []
    local_map = high_function.getLocalSymbolMap()
    owner_program_id = None
    owner_entry_offset = None
    try:
        if self.program is not None and hasattr(self.program, "getUniqueProgramID"):
            owner_program_id = int(self.program.getUniqueProgramID())
    except Exception:
        owner_program_id = None
    try:
        function = getattr(high_function, "getFunction", lambda: None)()
        if function is not None and hasattr(function, "getEntryPoint"):
            entry_point = function.getEntryPoint()
            if entry_point is not None:
                owner_entry_offset = int(entry_point.getOffset())
    except Exception:
        owner_entry_offset = None

    if local_map:
        for sym in local_map.getSymbols():
            if sym.isParameter():
                data_type = sym.getDataType()
                param_info = {
                    "name": sym.getName(),
                    "data_type": str(data_type) if data_type else None,
                    "data_type_obj": data_type,
                    "size": sym.getSize(),
                    "is_signed": self._is_signed_type(data_type),
                    "storage": self._get_storage_info(sym),
                    "owner_program_id": owner_program_id,
                    "owner_entry_offset": owner_entry_offset,
                }
                try:
                    param_info["index"] = sym.getCategoryIndex()
                except:
                    param_info["index"] = -1

                if self.debug:
                    self._debug_print(f"Parameter '{sym.getName()}': "
                                     f"type={param_info['data_type']}, "
                                     f"signed={param_info['is_signed']}, "
                                     f"storage={param_info['storage']}")

                params.append(param_info)

    params.sort(key=lambda x: x.get("index", -1))
    return params

def _impl__is_signed_type(self, data_type) -> bool:
    """データ型が符号付きかどうかを判定"""
    return get_declared_type_signedness(data_type, fallback_signed=True)

def _impl__is_void_type(self, data_type) -> bool:
    """データ型が void かどうかを判定"""
    return is_void_data_type(data_type)

def _impl__get_storage_info(self, sym) -> Optional[Dict]:
    """シンボルのストレージ情報を取得"""
    try:
        storage = sym.getStorage()
        if storage is None:
            return None

        # Varnodeリストを取得
        raw_varnodes = getattr(storage, "getVarnodes", lambda: [])()
        varnodes = [vn for vn in cast(Iterable[Any], raw_varnodes) if vn is not None]
        if not varnodes:
            return None

        first_vn = varnodes[0]
        addr = first_vn.getAddress()
        space = addr.getAddressSpace()

        storage_info = {
            "is_register": space.isRegisterSpace(),
            "offset": first_vn.getOffset(),
            "size": first_vn.getSize(),
            "size_bits": first_vn.getSize() * 8,
            "space_name": space.getName(),
        }

        if space.isRegisterSpace():
            # レジスタ情報を取得
            reg = self.program.getRegister(addr, first_vn.getSize())
            if reg:
                storage_info["register_name"] = reg.getName()

                # 親レジスタ情報
                base_reg = reg.getBaseRegister()
                if base_reg and base_reg != reg:
                    storage_info["base_register_name"] = base_reg.getName()
                    storage_info["base_register_size"] = base_reg.getBitLength() // 8
                    storage_info["base_register_size_bits"] = base_reg.getBitLength()
                    # パラメータのビットオフセット（親レジスタ内での位置）
                    byte_offset_in_base = reg.getOffset() - base_reg.getOffset()
                    storage_info["bit_offset_in_base"] = byte_offset_in_base * 8
                else:
                    # 親レジスタと同じ場合
                    storage_info["base_register_name"] = reg.getName()
                    storage_info["base_register_size"] = reg.getBitLength() // 8
                    storage_info["base_register_size_bits"] = reg.getBitLength()
                    storage_info["bit_offset_in_base"] = 0

        return storage_info
    except Exception as e:
        if self.debug:
            self._debug_print(f"Failed to get storage info: {e}")
        return None

def _impl__get_function_manager(self):
    if self.program is None:
        return None
    try:
        return self.program.getFunctionManager()
    except Exception:
        return None

def _impl__resolve_function_from_address(self, address):
    if address is None:
        return None
    try:
        function_manager = self._get_function_manager()
        if function_manager is None:
            return None
        get_function_at = getattr(function_manager, "getFunctionAt", None)
        if callable(get_function_at):
            function = get_function_at(address)
            if function is not None:
                return function
        get_referenced_function = getattr(function_manager, "getReferencedFunction", None)
        if callable(get_referenced_function):
            function = get_referenced_function(address)
            if function is not None:
                return function
    except Exception:
        return None
    return None

def _impl__build_condition_signature_set(self, conditions: List[Condition]) -> Set[object]:
    signatures: Set[object] = set()
    for condition in conditions:
        try:
            signatures.add(condition.structural_key(budget=256))
        except Exception:
            try:
                signatures.add(ConditionNormalizer.normalize_for_contradiction(condition))
            except Exception:
                continue
    return signatures

def _impl__varnode_location_key(varnode) -> Optional[Tuple[str, int, int]]:
    if varnode is None:
        return None
    try:
        address = varnode.getAddress()
        size = int(varnode.getSize())
        if address is None:
            return None
        space = address.getAddressSpace()
        space_name = space.getName() if space is not None else "unknown"
        return (space_name, int(address.getOffset()), size)
    except Exception:
        return None

def _impl__varnodes_may_alias(cls, lhs, rhs) -> bool:
    if lhs is None or rhs is None:
        return False
    if lhs is rhs:
        return True
    return cls._varnode_location_key(lhs) == cls._varnode_location_key(rhs)

def _impl__phi_origin_keys_from_varnode_defs(
    self,
    varnode,
    *,
    max_depth: int = 8,
) -> Set[Tuple[Any, ...]]:
    keys: Set[Tuple[Any, ...]] = set()
    seen: Set[int] = set()

    def visit(current, depth: int) -> None:
        if current is None or depth > int(max_depth):
            return
        marker = id(current)
        if marker in seen:
            return
        seen.add(marker)
        try:
            op = current.getDef()
        except Exception:
            op = None
        if op is None:
            return
        if getattr(op, "getMnemonic", lambda: None)() == "MULTIEQUAL":
            key = self._pcode_op_stable_key(op)
            if isinstance(key, tuple):
                keys.add(key)
        try:
            input_count = int(op.getNumInputs())
        except Exception:
            input_count = 0
        for index in range(input_count):
            try:
                visit(op.getInput(index), depth + 1)
            except Exception:
                continue

    visit(varnode, 0)
    return keys

def _impl__condition_set_conjunction_expression(
    self,
    conditions: Sequence[Condition],
) -> Optional[Expression]:
    terms = [self._condition_to_expression(condition) for condition in conditions or ()]
    terms = [term for term in terms if term is not None]
    if not terms:
        one = Expression.constant(1, size=1)
        return one
    result = terms[0]
    for term in terms[1:]:
        result = Expression.binary_op("BOOL_AND", result, term)
        result.size = 1
    return result

def _impl__condition_to_expression(self, condition: Condition) -> Optional[Expression]:
    expr = getattr(condition, "expression", None)
    if expr is None:
        return None
    if not bool(getattr(condition, "negated", False)):
        return expr
    negated = Expression.unary_op("BOOL_NEGATE", expr)
    negated.size = 1
    return negated

def _impl__phi_free_finite_fallback_candidates(
    self,
    fallback_value: Expression,
    conditions: Sequence[Condition],
) -> List[Tuple[List[Condition], Expression]]:
    finite_condition_sets = self._split_small_finite_parameter_reachability_conditions(
        conditions,
    )
    if len(finite_condition_sets) <= 1:
        return []
    candidates: List[Tuple[List[Condition], Expression]] = []
    skipped_phi = 0
    skipped_none = 0
    for finite_conditions in finite_condition_sets:
        finite_value = self._normalize_expanded_return_value(
            fallback_value,
            finite_conditions,
        )
        if finite_value is None:
            skipped_none += 1
            continue
        if self._expression_contains_phi(finite_value):
            skipped_phi += 1
            continue
        candidates.append((finite_conditions, finite_value))
    if self.debug and (skipped_phi or skipped_none):
        self._debug_print(
            "Finite PHI fallback split retained "
            f"{len(candidates)}/{len(finite_condition_sets)} cases "
            f"(skipped_phi={skipped_phi}, skipped_none={skipped_none})"
        )
    return candidates

def _impl__split_small_finite_parameter_reachability_conditions(
    self,
    conditions: Sequence[Condition],
    *,
    search_min: int = -8,
    search_max: int = 64,
    max_cases: int = 16,
) -> List[List[Condition]]:
    parameter = self._single_parameter_expression_in_conditions(conditions)
    if parameter is None:
        return [list(conditions or [])]
    feasible_values: List[int] = []
    for value in range(int(search_min), int(search_max) + 1):
        equality = self._parameter_equals_condition(parameter, value)
        if not self._conditions_are_unsat(list(conditions or []) + [equality]):
            feasible_values.append(value)
            if len(feasible_values) > int(max_cases):
                return [list(conditions or [])]
    if len(feasible_values) <= 1:
        return [list(conditions or [])]
    uncovered_conditions = list(conditions or [])
    for value in feasible_values:
        uncovered_conditions.append(self._parameter_equals_condition(parameter, value).negate())
    if not self._conditions_are_unsat(uncovered_conditions):
        return [list(conditions or [])]
    result: List[List[Condition]] = []
    for value in feasible_values:
        split_conditions = ConditionSimplifier.simplify_conditions_object_centric(
            list(conditions or []) + [self._parameter_equals_condition(parameter, value)]
        )
        if ConditionSimplifier.object_centric_is_contradiction(split_conditions):
            continue
        result.append(split_conditions)
    return result or [list(conditions or [])]

def _impl__single_parameter_expression_in_conditions(
    self,
    conditions: Sequence[Condition],
) -> Optional[Expression]:
    parameters: Dict[Tuple[Any, ...], Expression] = {}
    for condition in conditions or []:
        for node in _iter_expression_nodes(getattr(condition, "expression", None), include_phi_conditions=True):
            if getattr(node, "expr_type", None) != ExpressionType.PARAMETER:
                continue
            try:
                key = node.structural_key()
            except Exception:
                continue
            parameters[key] = node
            if len(parameters) > 1:
                return None
    return next(iter(parameters.values()), None)

def _impl__parameter_equals_condition(self, parameter: Expression, value: int) -> Condition:
    size = max(1, int(getattr(parameter, "size", 0) or 4))
    expr = Expression.binary_op("INT_EQUAL", parameter, Expression.constant(int(value), size=size))
    expr.size = 1
    return Condition(expr)

def _impl__conditions_are_unsat(self, conditions: Sequence[Condition]) -> bool:
    try:
        solver_result = ConditionSMTOracle.conjunction_is_unsat(list(conditions or []))
    except Exception:
        solver_result = None
    if solver_result is not None:
        return bool(solver_result)
    return ConditionSimplifier.object_centric_is_contradiction(list(conditions or []))

def _impl__phi_expression_key_set(
    self,
    expr: Optional[Expression],
) -> Set[Tuple[Any, ...]]:
    keys: Set[Tuple[Any, ...]] = set()

    def visit(node: Optional[Expression]) -> None:
        if node is None:
            return
        if getattr(node, "expr_type", None) == ExpressionType.PHI:
            try:
                keys.add(node.structural_key(budget=256))
            except Exception:
                pass
            for condition, value in getattr(node, "value", None) or []:
                if condition is not None:
                    visit(getattr(condition, "expression", None))
                visit(value)
            return
        for operand in getattr(node, "operands", None) or []:
            visit(operand)

    visit(expr)
    return keys

def _impl__fold_constant_expression(
    self,
    expr: Optional[Expression],
    *,
    fallback_expr: Optional[Expression] = None,
) -> Optional[Expression]:
    if expr is None:
        return None
    evaluated = eval_constant_raw(expr)
    if evaluated is None:
        return expr
    raw_value, bits = evaluated
    template = fallback_expr or expr
    size_bytes = int(getattr(template, "size", 0) or 0)
    if size_bytes <= 0:
        size_bytes = max(1, (bits + 7) // 8)
    return Expression.constant(raw_value, size=size_bytes)

def _impl__resolve_precise_object_state_value(
    self,
    value: Optional[Expression],
    conditions: List[Condition],
    effect_summary: EffectSummary,
) -> Optional[Expression]:
    if value is None:
        return None

    candidates: List[Expression] = [value]
    comparison_targets: List[Expression] = [value]
    if _expression_contains_observed_loads(value):
        observed_rewritten = rewrite_observed_loads_from_effects(
            value,
            conditions,
            effect_summary.effects,
            self._current_parameters,
        )
        if observed_rewritten is not None:
            candidates.append(observed_rewritten)
            comparison_targets.append(observed_rewritten)
        observed_post_state = promote_observed_loads_to_post_state_reads(
            value,
            conditions,
            effect_summary.effects,
            self._current_parameters,
            symbolic_post_state=True,
        )
        if observed_post_state is not None:
            comparison_targets.append(observed_post_state)
            lowered_observed_post_state = lower_post_state_expression_for_smt(
                observed_post_state,
                conditions,
                effect_summary.effects,
                self._current_parameters,
            )
            if lowered_observed_post_state is not None:
                comparison_targets.append(lowered_observed_post_state)

    for candidate in candidates:
        materialized = _materialize_existing_effect_value_carrier(
            candidate,
            conditions,
            effect_summary.effects,
            self._current_parameters,
        )
        if materialized is None or materialized is candidate:
            continue
        if expression_contains_post_state_reads(materialized):
            continue
        if not any(
            _expressions_equivalent_under_conditions(
                materialized,
                comparison_target,
                conditions,
                self._current_parameters,
            )
            for comparison_target in comparison_targets
        ):
            continue
        return materialized

    return value

def _impl__is_direct_location_carrier(self, expr: Optional[Expression]) -> bool:
    if expr is None:
        return False
    if _expression_location_ref(expr) is not None:
        return True
    return expr.expr_type == ExpressionType.MEMORY and bool(expr.operands)

def _impl__expression_has_nontrivial_location_wrapper(
    self,
    expr: Optional[Expression],
    location: CanonicalLocation,
) -> bool:
    if expr is None:
        return False
    if expr.expr_type == ExpressionType.BINARY_OP and len(expr.operands) == 2:
        for index, operand in enumerate(expr.operands):
            operand_location = canonicalize_expr_read_location(
                operand,
                self._current_parameters,
            )
            if operand_location is None or operand_location != location:
                continue
            other_operand = expr.operands[1 - index]
            if self._wrapper_preserves_collapsed_operand(
                expr.operator,
                other_operand,
                kept_operand_index=index,
            ):
                return False
            return True
        return False
    if expr.expr_type == ExpressionType.UNARY_OP:
        return True
    if expr.expr_type in {ExpressionType.CALL, ExpressionType.INTRINSIC}:
        return True
    return False

def _impl__wrapper_preserves_collapsed_operand(
    self,
    operator: Optional[str],
    shared_operand: Optional[Expression],
    *,
    kept_operand_index: int,
) -> bool:
    if shared_operand is None or shared_operand.expr_type != ExpressionType.CONSTANT:
        return False

    try:
        shared_value = int(shared_operand.value)
    except Exception:
        return False

    bit_width = max(1, int(shared_operand.get_bit_width() or 0))
    mask = (1 << bit_width) - 1
    normalized = shared_value & mask

    if operator in {"INT_ADD", "INT_OR", "INT_XOR"}:
        return normalized == 0
    if operator == "INT_AND":
        return normalized == mask
    if operator in {"INT_LEFT", "INT_RIGHT", "INT_SRIGHT"}:
        return kept_operand_index == 0 and normalized == 0
    if operator == "INT_SUB":
        return kept_operand_index == 0 and normalized == 0
    return False

def _impl__count_unresolved_value_nodes(self, expr: Optional[Expression]) -> int:
    if expr is None:
        return 1
    count = 1 if expr.expr_type == ExpressionType.UNKNOWN else 0
    if expr.expr_type == ExpressionType.PHI and expr.value:
        for cond, value in expr.value:
            cond_expr = getattr(cond, "expression", None) if cond is not None else None
            if cond_expr is not None:
                count += self._count_unresolved_value_nodes(cond_expr)
            count += self._count_unresolved_value_nodes(value)
        return count
    for operand in getattr(expr, "operands", []) or []:
        count += self._count_unresolved_value_nodes(operand)
    return count

def _impl__count_object_centric_unknowns(self, expr: Optional[Expression]) -> int:
    count = 0
    for current in _iter_expression_nodes(expr):
        if getattr(current, "expr_type", None) != ExpressionType.UNKNOWN:
            continue
        runtime_ref = getattr(current, "runtime_ref", None)
        stable_key = getattr(runtime_ref, "stable_key", None)
        if callable(stable_key):
            try:
                if stable_key() is not None:
                    count += 1
            except Exception:
                continue
    return count

def _impl__count_opaque_unknowns(self, expr: Optional[Expression]) -> int:
    count = 0
    for current in _iter_expression_nodes(expr):
        if getattr(current, "expr_type", None) != ExpressionType.UNKNOWN:
            continue
        runtime_ref = getattr(current, "runtime_ref", None)
        kind = getattr(runtime_ref, "kind", None)
        stable_key = getattr(runtime_ref, "stable_key", None)
        if kind == "opaque_unknown" or not callable(stable_key):
            count += 1
    return count

def _impl__count_phi_nodes(self, expr: Optional[Expression]) -> int:
    count = 0
    for current in _iter_expression_nodes(expr):
        if getattr(current, "expr_type", None) == ExpressionType.PHI:
            count += 1
    return count

def _impl__expand_object_centric_expression_cases(
    self,
    expr: Optional[Expression],
    base_conditions: List[Condition],
) -> List[Tuple[Expression, List[Condition]]]:
    if expr is None:
        return []

    simplified_base = ConditionSimplifier.simplify_conditions_object_centric(base_conditions)
    if ConditionSimplifier.object_centric_is_contradiction(simplified_base):
        return []
    direct_runtime_guards = self._direct_expression_runtime_guard_conditions(expr)
    if direct_runtime_guards:
        simplified_base = ConditionSimplifier.simplify_conditions_object_centric(
            list(simplified_base) + list(direct_runtime_guards)
        )
        if ConditionSimplifier.object_centric_is_contradiction(simplified_base):
            return []

    folded_expr = self._fold_constant_expression(
        expr,
        fallback_expr=expr,
    )
    if folded_expr is not None:
        expr = folded_expr

    boolean_cases = self._expand_boolean_expression_cases(
        expr,
        simplified_base,
    )
    if boolean_cases is not None:
        return self._deduplicate_expression_cases(boolean_cases)

    if expr.expr_type == ExpressionType.PHI and expr.value:
        expanded: List[Tuple[Expression, List[Condition]]] = []
        prior_guards: List[Condition] = []
        for cond, value in expr.value:
            combined_conditions = list(simplified_base)
            for prior in prior_guards:
                combined_conditions.append(prior.negate())
            if cond is not None:
                combined_conditions.append(cond)
                prior_guards.append(cond)
            nested_conditions = ConditionSimplifier.simplify_conditions_object_centric(
                combined_conditions
            )
            if ConditionSimplifier.object_centric_is_contradiction(nested_conditions):
                continue
            expanded.extend(
                self._expand_object_centric_expression_cases(
                    value,
                    nested_conditions,
                )
            )
        return self._deduplicate_expression_cases(expanded)

    if expr.expr_type == ExpressionType.MEMORY and expr.operands:
        address_cases = self._expand_object_centric_expression_cases(
            expr.operands[0],
            simplified_base,
        )
        if not address_cases:
            return [(expr, simplified_base)]
        expanded = [
            (expr.clone_with(operands=[address]), case_conditions)
            for address, case_conditions in address_cases
            if not ConditionSimplifier.object_centric_is_contradiction(case_conditions)
        ]
        return self._deduplicate_expression_cases(expanded)

    if expr.expr_type == ExpressionType.UNARY_OP and expr.operands:
        operand_cases = self._expand_object_centric_expression_cases(
            expr.operands[0],
            simplified_base,
        )
        if not operand_cases:
            return [(expr, simplified_base)]
        expanded = []
        for operand, case_conditions in operand_cases:
            if ConditionSimplifier.object_centric_is_contradiction(case_conditions):
                continue
            rebuilt = expr.clone_with(operands=[operand])
            rebuilt = self._fold_constant_expression(rebuilt, fallback_expr=expr)
            expanded.append((rebuilt, case_conditions))
        return self._deduplicate_expression_cases(expanded)

    if expr.expr_type == ExpressionType.BINARY_OP and len(expr.operands) == 2:
        left_cases = self._expand_object_centric_expression_cases(
            expr.operands[0],
            simplified_base,
        )
        right_cases = self._expand_object_centric_expression_cases(
            expr.operands[1],
            simplified_base,
        )
        if not left_cases:
            left_cases = [(expr.operands[0], simplified_base)]
        if not right_cases:
            right_cases = [(expr.operands[1], simplified_base)]

        expanded: List[Tuple[Expression, List[Condition]]] = []
        for left_value, left_conditions in left_cases:
            for right_value, right_conditions in right_cases:
                combined_conditions = ConditionSimplifier.simplify_conditions_object_centric(
                    list(simplified_base) + list(left_conditions) + list(right_conditions)
                )
                if ConditionSimplifier.object_centric_is_contradiction(combined_conditions):
                    continue
                rebuilt = expr.clone_with(operands=[left_value, right_value])
                rebuilt = self._fold_constant_expression(rebuilt, fallback_expr=expr)
                expanded.append(
                    (
                        rebuilt,
                        combined_conditions,
                    )
                )
        return self._deduplicate_expression_cases(expanded)

    return [(expr, simplified_base)]

def _impl__expand_boolean_expression_cases(
    self,
    expr: Optional[Expression],
    base_conditions: List[Condition],
) -> Optional[List[Tuple[Expression, List[Condition]]]]:
    if expr is None or not self._is_boolean_expression(expr):
        return None

    condition = Condition(expr, False)
    if ConditionSimplifier.object_centric_is_contradiction(
        list(base_conditions) + [condition.negate()]
    ):
        return [(Expression.constant(1, size=max(1, expr.size or 1)), base_conditions)]
    if ConditionSimplifier.object_centric_is_contradiction(
        list(base_conditions) + [condition]
    ):
        return [(Expression.constant(0, size=max(1, expr.size or 1)), base_conditions)]

    true_conditions = ConditionSimplifier.simplify_conditions_object_centric(
        list(base_conditions) + [condition]
    )
    false_conditions = ConditionSimplifier.simplify_conditions_object_centric(
        list(base_conditions) + [condition.negate()]
    )

    cases: List[Tuple[Expression, List[Condition]]] = []
    if not ConditionSimplifier.object_centric_is_contradiction(true_conditions):
        cases.append((Expression.constant(1, size=max(1, expr.size or 1)), true_conditions))
    if not ConditionSimplifier.object_centric_is_contradiction(false_conditions):
        cases.append((Expression.constant(0, size=max(1, expr.size or 1)), false_conditions))
    if not cases:
        return []
    return cases

def _impl__is_boolean_expression(self, expr: Optional[Expression]) -> bool:
    if expr is None:
        return False
    if expr.expr_type == ExpressionType.BINARY_OP:
        return expr.operator in {
            "INT_EQUAL",
            "INT_NOTEQUAL",
            "INT_LESS",
            "INT_LESSEQUAL",
            "INT_SLESS",
            "INT_SLESSEQUAL",
            "BOOL_AND",
            "BOOL_OR",
            "BOOL_XOR",
        }
    return expr.expr_type == ExpressionType.UNARY_OP and expr.operator == "BOOL_NEGATE"

def _impl__deduplicate_expression_cases(
    self,
    cases: List[Tuple[Expression, List[Condition]]],
) -> List[Tuple[Expression, List[Condition]]]:
    deduplicated: List[Tuple[Expression, List[Condition]]] = []
    for value, conditions in cases:
        simplified_conditions = ConditionSimplifier.simplify_conditions_object_centric(
            conditions
        )
        if ConditionSimplifier.object_centric_is_contradiction(simplified_conditions):
            continue
        duplicate = False
        for existing_value, existing_conditions in deduplicated:
            if (
                _expressions_equivalent(existing_value, value)
                and self._condition_lists_equivalent(existing_conditions, simplified_conditions)
            ):
                duplicate = True
                break
        if not duplicate:
            deduplicated.append((value, simplified_conditions))
    return deduplicated

def _impl__condition_lists_equivalent(
    self,
    left: List[Condition],
    right: List[Condition],
) -> bool:
    if len(left) != len(right):
        return False
    unmatched = list(right)
    for left_condition in left:
        matched_index = next(
            (
                index for index, right_condition in enumerate(unmatched)
                if ConditionNormalizer.are_equivalent(left_condition, right_condition)
            ),
            None,
        )
        if matched_index is None:
            return False
        unmatched.pop(matched_index)
    return not unmatched

def _impl__expression_contains_phi_circular_marker(self, expr: Optional[Expression]) -> bool:
    if expr is None:
        return False
    if getattr(expr, "expr_type", None) == ExpressionType.UNKNOWN:
        if str(getattr(expr, "name", "") or getattr(expr, "value", "") or "") == "phi_circular":
            return True
        runtime_ref = getattr(expr, "runtime_ref", None)
        if (
            isinstance(runtime_ref, UnknownValueRef)
            and getattr(runtime_ref, "reason", None) == "phi_circular"
        ):
            return True
        if getattr(runtime_ref, "kind", None) == "phi_circular":
            return True
    return any(
        self._expression_contains_phi_circular_marker(operand)
        for operand in (getattr(expr, "operands", None) or ())
    )

def _impl__expression_runtime_guard_conditions(
    self,
    expr: Optional[Expression],
) -> List[Condition]:
    guards: List[Condition] = []
    seen: Set[tuple] = set()
    for node in self._iter_expression_nodes_for_unconditional_runtime_guards(expr):
        runtime_ref = getattr(node, "runtime_ref", None)
        for guard in self._runtime_ref_guard_conditions(runtime_ref):
            try:
                key = guard.structural_key(budget=256)
            except Exception:
                key = (id(guard),)
            if key in seen:
                continue
            seen.add(key)
            guards.append(guard)
    return guards

def _impl__iter_expression_nodes_for_unconditional_runtime_guards(
    self,
    expr: Optional[Expression],
):
    if expr is None:
        return
    stack = [expr]
    while stack:
        current = stack.pop()
        if current is None:
            continue
        yield current
        if getattr(current, "expr_type", None) == ExpressionType.PHI:
            continue
        operands = getattr(current, "operands", None) or ()
        stack.extend(reversed([operand for operand in operands if operand is not None]))

def _impl__direct_expression_runtime_guard_conditions(
    self,
    expr: Optional[Expression],
) -> List[Condition]:
    if expr is None:
        return []
    return self._runtime_ref_guard_conditions(getattr(expr, "runtime_ref", None))

def _impl__runtime_ref_guard_conditions(
    self,
    runtime_ref,
) -> List[Condition]:
    guards: List[Condition] = []
    for owner in (
        runtime_ref,
        getattr(runtime_ref, "accumulator_proof", None),
        getattr(runtime_ref, "loop_summary", None),
    ):
        for guard in tuple(getattr(owner, "guard_constraints", ()) or ()):
            if isinstance(guard, Condition):
                guards.append(guard)
    return guards

def _impl__condition_is_constant_equality_guard(self, condition: Condition) -> bool:
    if condition is None:
        return False
    expr = getattr(condition, "expression", None)
    if expr is None or getattr(expr, "expr_type", None) != ExpressionType.BINARY_OP:
        return False
    if self._condition_logical_operator(condition) != "INT_EQUAL" or len(getattr(expr, "operands", ()) or ()) != 2:
        return False
    left, right = expr.operands
    left_is_const = getattr(left, "expr_type", None) == ExpressionType.CONSTANT
    right_is_const = getattr(right, "expr_type", None) == ExpressionType.CONSTANT
    return left_is_const != right_is_const

def _impl__condition_logical_operator(
    self,
    condition: Condition,
) -> Optional[str]:
    expr = getattr(condition, "expression", None)
    if expr is None or getattr(expr, "expr_type", None) != ExpressionType.BINARY_OP:
        return None
    operator = getattr(expr, "operator", None)
    if not getattr(condition, "negated", False):
        return operator
    if operator == "INT_EQUAL":
        return "INT_NOTEQUAL"
    if operator == "INT_NOTEQUAL":
        return "INT_EQUAL"
    return operator

def _impl__readonly_reduction_contract_priority_score(
    self,
    info: ReturnInfo,
) -> int:
    best_score = 0
    for node in _iter_expression_nodes(info.value, include_phi_conditions=False):
        runtime_ref = getattr(node, "runtime_ref", None)
        if isinstance(runtime_ref, ReadonlyReductionRef):
            best_score = max(
                best_score,
                self._readonly_reduction_ref_contract_priority_score(runtime_ref),
            )
    return best_score

def _impl__readonly_reduction_ref_contract_priority_score(
    self,
    runtime_ref: ReadonlyReductionRef,
) -> int:
    proof = getattr(runtime_ref, "accumulator_proof", None)
    if proof is None:
        return 0
    if not bool(getattr(proof, "return_region_value_proven", False)):
        return 0
    contract_key = None
    contract_key_fn = getattr(runtime_ref, "readonly_term_sequence_contract_key", None)
    if callable(contract_key_fn):
        try:
            contract_key = contract_key_fn()
        except (AttributeError, TypeError, ValueError):
            contract_key = None
    if contract_key is None:
        return 0

    semantic_witnesses = tuple(getattr(runtime_ref, "semantic_witnesses", ()) or ())
    exact_return_witnesses = tuple(getattr(proof, "exact_return_witnesses", ()) or ())
    loop_body_witnesses = tuple(getattr(proof, "loop_body_witnesses", ()) or ())
    seed_terms = tuple(getattr(proof, "seed_terms", ()) or ())
    return 1 + len(semantic_witnesses) + len(exact_return_witnesses) + len(loop_body_witnesses) + len(seed_terms)

def _impl__pruning_conditions_signature(
    self,
    conditions: List[Condition],
):
    parts = [
        ConditionNormalizer.normalize_for_contradiction(condition)
        for condition in (conditions or [])
    ]
    parts.sort()
    return tuple(parts)

def _impl__condition_sets_are_complementary(
    self,
    left_conditions: List[Condition],
    right_conditions: List[Condition],
) -> bool:
    if not left_conditions or not right_conditions:
        return False
    if len(left_conditions) != len(right_conditions):
        return False

    unmatched = list(right_conditions)
    for left_condition in left_conditions:
        match_index = None
        for index, right_condition in enumerate(unmatched):
            if left_condition.equals(right_condition.negate()) or left_condition.negate().equals(right_condition):
                match_index = index
                break
        if match_index is None:
            return False
        unmatched.pop(match_index)
    return not unmatched

def _impl__substitute_parameter_constants_under_conditions(
    self,
    expr: Optional[Expression],
    conditions: Sequence[Condition],
) -> Optional[Expression]:
    assignments = self._parameter_constant_assignments_from_conditions(conditions)
    if not assignments:
        return expr
    substituted = self._substitute_parameter_constants(expr, assignments)
    if substituted is None:
        return expr
    folded = self._fold_constant_expression(substituted, fallback_expr=expr)
    return folded if folded is not None else substituted

def _impl__parameter_constant_assignments_from_conditions(
    self,
    conditions: Sequence[Condition],
) -> Dict[Tuple[Any, ...], Tuple[Expression, int]]:
    assignments: Dict[Tuple[Any, ...], Tuple[Expression, int]] = {}
    for condition in conditions or ():
        if getattr(condition, "negated", False):
            continue
        expr = getattr(condition, "expression", None)
        if getattr(expr, "expr_type", None) != ExpressionType.BINARY_OP:
            continue
        if getattr(expr, "operator", None) != "INT_EQUAL":
            continue
        operands = list(getattr(expr, "operands", None) or [])
        if len(operands) != 2:
            continue
        for parameter, constant in ((operands[0], operands[1]), (operands[1], operands[0])):
            if getattr(parameter, "expr_type", None) != ExpressionType.PARAMETER:
                continue
            if getattr(constant, "expr_type", None) != ExpressionType.CONSTANT:
                continue
            try:
                key = parameter.structural_key()
                value = int(getattr(constant, "value", 0) or 0)
            except Exception:
                continue
            existing = assignments.get(key)
            if existing is not None and existing[1] != value:
                assignments.pop(key, None)
                continue
            assignments[key] = (parameter, value)
    return assignments

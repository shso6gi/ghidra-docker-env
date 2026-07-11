"""Stateless method implementations extracted from ``scripts.function_tracer_pcode.analysis.recurrence_summary``."""

from __future__ import annotations

from typing import Any
from ._shared import (
    Condition,
    ConditionNormalizer,
    Expression,
    ExpressionType,
    LoopVariableIdentityRef,
    StorageInfo,
    _runtime_expression_signature,
    parameter_identity_key_from_descriptor,
    parameter_identity_key_from_expression,
)

def invoke(_service_name: str, *args: Any, **kwargs: Any) -> Any:
    implementation_function = globals().get(f"_impl_{_service_name}")
    if implementation_function is None:
        raise AttributeError(_service_name)
    return implementation_function(*args, **kwargs)


def implementation(_service_name: str):
    return globals().get(f"_impl_{_service_name}")

def _impl__storage_infos_refer_to_same_parameter_slot(
    self,
    left: Optional[StorageInfo],
    right: Optional[StorageInfo],
) -> bool:
    if left is None or right is None:
        return False
    if left == right:
        return True
    left_key = getattr(left, "storage_identity_key", None)
    right_key = getattr(right, "storage_identity_key", None)
    if callable(left_key):
        try:
            left_key = left_key()
        except Exception:
            left_key = None
    if callable(right_key):
        try:
            right_key = right_key()
        except Exception:
            right_key = None
    if left_key is not None and right_key is not None and left_key == right_key:
        return True
    if not bool(getattr(left, "is_register", False)) or not bool(getattr(right, "is_register", False)):
        return False
    shares_base = getattr(left, "shares_base_register_with", None)
    overlaps = getattr(left, "bit_range_overlaps_with", None)
    if not callable(shares_base) or not callable(overlaps):
        return False
    try:
        return bool(shares_base(right)) and bool(overlaps(right))
    except Exception:
        return False

def _impl__parameter_expression_semantic_identity(self, expr: Optional[Expression]) -> Optional[Tuple[Any, ...]]:
    runtime_ref = getattr(expr, "runtime_ref", None)
    if runtime_ref is None:
        return None
    semantic_key = getattr(runtime_ref, "semantic_key", None)
    if callable(semantic_key):
        try:
            key = semantic_key()
        except Exception:
            key = None
        if key is not None:
            return ("semantic", key)
    stable_key = getattr(runtime_ref, "stable_key", None)
    if callable(stable_key):
        try:
            key = stable_key()
        except Exception:
            key = None
        if key is not None:
            return ("stable", key)
    return None

def _impl__same_counter_expression(self, expr: Optional[Expression], counter_expr: Optional[Expression]) -> bool:
    if expr is None or counter_expr is None:
        return False
    if (
        getattr(expr, "expr_type", None) == ExpressionType.PARAMETER
        or getattr(counter_expr, "expr_type", None) == ExpressionType.PARAMETER
    ):
        return self._parameter_expressions_share_counter_identity(expr, counter_expr)
    try:
        if expr.equals(counter_expr):
            return True
    except Exception:
        pass
    return False

def _impl__parameter_expressions_share_counter_identity(
    self,
    expr: Optional[Expression],
    counter_expr: Optional[Expression],
) -> bool:
    if getattr(expr, "expr_type", None) != ExpressionType.PARAMETER:
        return False
    if getattr(counter_expr, "expr_type", None) != ExpressionType.PARAMETER:
        return False
    try:
        expr_index = int(getattr(expr, "value", -1))
        counter_index = int(getattr(counter_expr, "value", -1))
    except (TypeError, ValueError):
        expr_index = counter_index = -1
    if expr_index >= 0 and counter_index >= 0 and expr_index == counter_index:
        return True
    expr_storage = getattr(expr, "storage_info", None)
    counter_storage = getattr(counter_expr, "storage_info", None)
    if expr_storage is not None or counter_storage is not None:
        return (
            expr_storage is not None
            and counter_storage is not None
            and self._storage_infos_refer_to_same_parameter_slot(expr_storage, counter_storage)
        )
    expr_identity = self._parameter_expression_semantic_identity(expr)
    counter_identity = self._parameter_expression_semantic_identity(counter_expr)
    if expr_identity is not None or counter_identity is not None:
        return expr_identity is not None and expr_identity == counter_identity
    return False

def _impl__pcode_op_order_key(self, op) -> Optional[int]:
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

def _impl__summary_value_source_key(self, value: Optional[Expression]) -> Optional[Tuple[Any, ...]]:
    runtime_ref = getattr(value, "runtime_ref", None)
    handoff_proof_key = getattr(runtime_ref, "handoff_proof_key", None)
    if handoff_proof_key is not None:
        return handoff_proof_key
    stable_key = getattr(runtime_ref, "stable_key", None)
    if callable(stable_key):
        try:
            key = stable_key()
        except Exception:
            key = None
        if key is not None:
            return key if isinstance(key, tuple) else ("stable", key)
    fallback = self._counted_loop_summary_source_key_fallback(runtime_ref)
    if fallback is not None:
        return fallback
    return None

def _impl__sanitize_summary_evidence_key(self, value: Any) -> Any:
    if value is None:
        return ("none",)
    if isinstance(value, tuple):
        return tuple(self._sanitize_summary_evidence_key(item) for item in value)
    if isinstance(value, list):
        return tuple(self._sanitize_summary_evidence_key(item) for item in value)
    if isinstance(value, dict):
        return tuple(
            sorted(
                (
                    self._sanitize_summary_evidence_key(key),
                    self._sanitize_summary_evidence_key(item),
                )
                for key, item in value.items()
            )
        )
    return value

def _impl__return_info_summary_identity_key(self, ret: ReturnInfo) -> Tuple[Any, ...]:
    pcode_ref = getattr(ret, "pcode_op_ref", None)
    pcode_key = None
    stable_key = getattr(pcode_ref, "stable_key", None)
    if callable(stable_key):
        try:
            pcode_key = stable_key()
        except Exception:
            pcode_key = None
    return (
        "return_info",
        getattr(ret, "address", None),
        getattr(ret, "pcode_identity", None),
        getattr(ret, "pcode_order", None),
        getattr(ret, "pcode_time", None),
        pcode_key,
        self._summary_return_conditions_key(tuple(getattr(ret, "conditions", ()) or ())),
        self._summary_return_expression_key(getattr(ret, "value", None)),
    )

def _impl__summary_return_expression_key(self, expr: Optional[Expression]) -> Tuple[Any, ...]:
    if expr is None:
        return ("expr", "none")
    try:
        return expr.structural_key(
            budget=256,
            normalize_commutative=True,
            include_memory_read_order=True,
            include_semantic_runtime_refs=True,
        )
    except Exception:
        return ("opaque_expression", type(expr).__name__)

def _impl__counter_parameter_identity_key(
    self,
    expr: Optional[Expression],
    parameters: Optional[Sequence[dict]] = None,
) -> Optional[Tuple[Any, ...]]:
    if getattr(expr, "expr_type", None) != ExpressionType.PARAMETER:
        return None
    storage_key = self._expression_storage_identity_key(expr)
    if storage_key is not None:
        return ("parameter_storage", tuple(storage_key))
    try:
        index = int(getattr(expr, "value", -1))
    except (TypeError, ValueError):
        index = -1
    if index >= 0:
        descriptor = None
        for parameter in parameters or ():
            if not isinstance(parameter, dict):
                continue
            try:
                if int(parameter.get("index", -1)) == index:
                    descriptor = parameter
                    break
            except (TypeError, ValueError):
                continue
        descriptor_storage = self._parameter_storage_identity_key(descriptor) if descriptor is not None else None
        if descriptor_storage is not None:
            return ("parameter_storage", tuple(descriptor_storage))
        return ("parameter_index", index)
    name = str(getattr(expr, "name", "") or "")
    if not name:
        return None
    unique_by_name = self._unique_parameters_by_name(parameters)
    descriptor = unique_by_name.get(name) if unique_by_name else None
    if descriptor is None:
        return None
    descriptor_storage = self._parameter_storage_identity_key(descriptor)
    if descriptor_storage is not None:
        return ("parameter_storage", tuple(descriptor_storage))
    try:
        return ("parameter_index", int(descriptor.get("index")))
    except (TypeError, ValueError):
        return None

def _impl__expression_storage_identity_key(self, expr: Expression) -> Optional[Tuple[Any, ...]]:
    storage = getattr(expr, "storage_info", None)
    storage_key_fn = getattr(storage, "storage_identity_key", None)
    if callable(storage_key_fn):
        try:
            storage_key = storage_key_fn()
        except (AttributeError, TypeError, ValueError):
            storage_key = None
        if storage_key is not None:
            return tuple(storage_key)
    return None

def _impl__canonicalize_expression_parameters_for_analysis(
    self,
    expr: Expression,
    *,
    by_index: Dict[int, dict],
    by_name: Dict[str, dict],
) -> Expression:
    if getattr(expr, "expr_type", None) == ExpressionType.PARAMETER:
        descriptor = None
        try:
            descriptor = by_index.get(int(getattr(expr, "value", -1)))
        except (TypeError, ValueError):
            descriptor = None
        if descriptor is None:
            descriptor = by_name.get(str(getattr(expr, "name", "") or ""))
        if descriptor is not None:
            return self._parameter_expression(descriptor)
    operands = [
        self._canonicalize_expression_parameters_for_analysis(
            operand,
            by_index=by_index,
            by_name=by_name,
        )
        for operand in (getattr(expr, "operands", None) or ())
    ]
    return Expression(
        getattr(expr, "expr_type", None),
        value=getattr(expr, "value", None),
        operator=getattr(expr, "operator", None),
        operands=operands,
        size=int(getattr(expr, "size", 0) or 0),
        name=getattr(expr, "name", None),
        data_type=getattr(expr, "data_type", None),
        data_type_obj=getattr(expr, "data_type_obj", None),
        storage_info=getattr(expr, "storage_info", None),
        read_order_key=getattr(expr, "read_order_key", None),
        runtime_ref=getattr(expr, "runtime_ref", None),
        opcode=getattr(expr, "opcode", None),
        call_argument_width_evidence=getattr(expr, "call_argument_width_evidence", None),
    )

def _impl__positive_summary_parameter_key(
    self,
    conditions: Sequence[Condition],
) -> Optional[Tuple[Any, ...]]:
    keys: List[Tuple[Any, ...]] = []
    for condition in conditions or ():
        if bool(getattr(condition, "negated", False)):
            continue
        expr = getattr(condition, "expression", None)
        if getattr(expr, "expr_type", None) != ExpressionType.BINARY_OP:
            continue
        if getattr(expr, "operator", None) not in {"INT_SLESS", "INT_SLESSEQUAL", "INT_LESS", "INT_LESSEQUAL"}:
            continue
        operands = list(getattr(expr, "operands", ()) or ())
        if len(operands) != 2:
            continue
        left, right = operands
        if getattr(right, "expr_type", None) != ExpressionType.PARAMETER:
            continue
        left_value = self._raw_constant_value(left)
        if left_value is None:
            continue
        operator = getattr(expr, "operator", None)
        if operator in {"INT_SLESS", "INT_LESS"} and int(left_value) != 0:
            continue
        if operator in {"INT_SLESSEQUAL", "INT_LESSEQUAL"} and int(left_value) != 1:
            continue
        keys.append(_runtime_expression_signature(right))
    unique_keys = tuple(dict.fromkeys(keys))
    if len(unique_keys) != 1:
        return None
    return unique_keys[0]

def _impl__summary_symbol_identity_from_descriptor(
    self,
    parameter: dict,
) -> Optional[Tuple[Any, ...]]:
    identity = parameter_identity_key_from_descriptor(parameter)
    if identity is not None:
        return identity
    try:
        index = int(parameter.get("index", -1))
    except (TypeError, ValueError):
        return None
    if index < -1:
        return ("synthetic_parameter_index", index)
    return None

def _impl__summary_symbol_identity_from_expression(
    self,
    expr: Expression,
) -> Optional[Tuple[Any, ...]]:
    expr_type = getattr(expr, "expr_type", None)
    if expr_type == ExpressionType.PARAMETER:
        identity = parameter_identity_key_from_expression(expr)
        if identity is not None:
            return identity
        try:
            index = int(getattr(expr, "value", -1) or -1)
        except (TypeError, ValueError):
            return None
        if index < -1:
            return ("synthetic_parameter_index", index)
        return None
    if expr_type == ExpressionType.VARIABLE:
        storage_key = self._summary_storage_identity_key(getattr(expr, "storage_info", None))
        if storage_key is not None:
            return ("variable_storage", storage_key)
        runtime_ref = getattr(expr, "runtime_ref", None)
        semantic_key = getattr(runtime_ref, "semantic_key", None)
        if callable(semantic_key):
            try:
                key = semantic_key()
            except (AttributeError, TypeError, ValueError):
                key = None
            if key is not None:
                return ("variable_runtime_semantic", key)
        stable_key = getattr(runtime_ref, "stable_key", None)
        if callable(stable_key):
            try:
                key = stable_key()
            except (AttributeError, TypeError, ValueError):
                key = None
            if key is not None:
                return ("variable_runtime_stable", key)
        return ("expression_object", id(expr))
    return None

def _impl__summary_storage_identity_key(self, storage_info) -> Optional[Tuple[Any, ...]]:
    if isinstance(storage_info, dict):
        try:
            storage_info = StorageInfo(**storage_info)
        except Exception:
            return None
    storage_key_fn = getattr(storage_info, "storage_identity_key", None)
    if callable(storage_key_fn):
        try:
            return storage_key_fn()
        except (AttributeError, TypeError, ValueError):
            return None
    return None

def _impl__parameter_storage_identity_key(self, param: dict) -> Optional[Tuple[Any, ...]]:
    return self._summary_storage_identity_key(
        param.get("storage_info", param.get("storage")) if isinstance(param, dict) else None
    )

def _impl__summary_symbol_identity_sort_key(self, identity) -> Tuple[int, str]:
    if not isinstance(identity, tuple) or not identity:
        return (9, "")
    kind = identity[0]
    if kind == "parameter_index" and len(identity) >= 2:
        try:
            return (0, f"{int(identity[1]):08d}")
        except (TypeError, ValueError):
            return (0, repr(identity[1]))
    if kind == "parameter_storage" and len(identity) >= 2:
        return (1, repr(identity[1]))
    if kind == "synthetic_parameter_index" and len(identity) >= 2:
        try:
            return (2, f"{int(identity[1]):08d}")
        except (TypeError, ValueError):
            return (2, repr(identity[1]))
    if kind == "variable_storage" and len(identity) >= 2:
        return (3, repr(identity[1]))
    if kind in {"variable_runtime_semantic", "variable_runtime_stable"} and len(identity) >= 2:
        return (4, repr(identity[1]))
    if kind == "expression_object" and len(identity) >= 2:
        try:
            return (8, f"{int(identity[1]):020d}")
        except (TypeError, ValueError):
            return (8, repr(identity[1]))
    return (8, repr(identity))

def _impl__runtime_ref_stable_key(self, value: Optional[Expression]) -> Optional[Tuple[Any, ...]]:
    runtime_ref = getattr(value, "runtime_ref", None)
    stable_key = getattr(runtime_ref, "stable_key", None)
    if callable(stable_key):
        try:
            key = stable_key()
        except Exception:
            return None
        return key if isinstance(key, tuple) else ("stable", key)
    return None

def _impl__same_varnode_object_identity(self, left, right) -> bool:
    if left is None or right is None:
        return False
    if left is right:
        return True
    left_key = self._value_flow_varnode_key(left)
    right_key = self._value_flow_varnode_key(right)
    return left_key is not None and right_key is not None and left_key == right_key

def _impl__value_flow_varnode_key(self, varnode) -> Optional[Tuple[Any, ...]]:
    key = self._varnode_cache_key(varnode)
    if not isinstance(key, tuple) or len(key) != 3 or key[0] != "varnode":
        return None
    _tag, _address_key, def_key = key
    if def_key is None:
        return None
    return key

def _impl__value_preserving_edge_key(
    self,
    edge_kind: str,
    source_varnode,
    target_varnode,
    *,
    op=None,
) -> Optional[Tuple[Any, ...]]:
    source_key = self._value_flow_varnode_key(source_varnode)
    target_key = self._value_flow_varnode_key(target_varnode)
    if source_key is None or target_key is None:
        return None
    location_key: Tuple[Any, ...]
    if op is None:
        location_key = ("edge_location", "identity")
    else:
        op_ref = self._make_pcode_op_ref(op)
        block_ref = self._make_pcode_block_ref(getattr(op, "getParent", lambda: None)())
        if op_ref is None or block_ref is None:
            return None
        location_key = (
            "edge_location",
            op_ref.stable_key(),
            block_ref.stable_key(),
        )
    return (
        "edge",
        edge_kind,
        source_key,
        target_key,
        self._varnode_size_bits(source_varnode),
        self._varnode_size_bits(target_varnode),
        location_key,
    )

def _impl__clean_edge_specific_handoff_blocks_key(
    self,
    start_block,
    predecessor_block,
    target_block,
    *,
    budget: int = 64,
) -> Optional[Tuple[Any, ...]]:
    if start_block is None or predecessor_block is None or target_block is None:
        return None
    start_ref = self._make_pcode_block_ref(start_block)
    predecessor_ref = self._make_pcode_block_ref(predecessor_block)
    target_ref = self._make_pcode_block_ref(target_block)
    if start_ref is None or predecessor_ref is None or target_ref is None:
        return None
    target_key = self._block_key(target_block)
    predecessor_key = self._block_key(predecessor_block)
    if not any(
        self._block_key(successor) == target_key
        for successor in self._collect_block_successors(predecessor_block)
    ):
        return None
    stack = [start_block]
    seen = set()
    exhausted = False
    found_phi_edge = False
    while stack:
        if len(seen) >= budget:
            exhausted = True
            break
        block = stack.pop()
        if block is None:
            continue
        block_key = self._block_key(block)
        if block_key in seen:
            continue
        seen.add(block_key)
        if block_key == target_key:
            continue
        for op in self._iter_block_ops(block):
            mnemonic = getattr(op, "getMnemonic", lambda: None)()
            if mnemonic in {"STORE", "CALL", "CALLIND", "BRANCHIND", "CALLOTHER"}:
                return None
        for successor in self._collect_block_successors(block):
            successor_key = self._block_key(successor)
            if successor_key == target_key:
                if block_key != predecessor_key:
                    return None
                found_phi_edge = True
                continue
            if successor_key not in seen and self._can_reach_block(successor, target_block):
                stack.append(successor)
    if exhausted or not found_phi_edge:
        return None
    return (
        "handoff_blocks",
        start_ref.stable_key(),
        predecessor_ref.stable_key(),
        target_ref.stable_key(),
        "all_paths_clean_to_phi_predecessor",
    )

def _impl__handoff_widths_key(
    self,
    *,
    prior_accumulator: CountedLoopAccumulator,
    current_init_varnode,
    result_size: int,
    value_flow_key: Tuple[Any, ...],
) -> Optional[Tuple[Any, ...]]:
    source_bits = max(
        self._varnode_size_bits(prior_accumulator.update_varnode),
        self._varnode_size_bits(prior_accumulator.phi_output),
    )
    target_bits = self._varnode_size_bits(current_init_varnode)
    return_bits = max(1, int(result_size or 0)) * 8
    if source_bits <= 0 or target_bits <= 0 or return_bits <= 0:
        return None
    conversion = "same_width"
    edges = value_flow_key[3] if isinstance(value_flow_key, tuple) and len(value_flow_key) == 4 else ()
    if any(isinstance(edge, tuple) and len(edge) > 1 and edge[1] == "INT_ZEXT" for edge in edges):
        conversion = "zero_extend"
    if any(isinstance(edge, tuple) and len(edge) > 1 and edge[1] == "INT_SEXT" for edge in edges):
        conversion = "sign_extend"
    if conversion == "same_width" and source_bits != target_bits:
        return None
    return ("handoff_widths", source_bits, target_bits, return_bits, conversion)

def _impl__block_key(self, block) -> object:
    if block is None:
        return None
    block_index = getattr(block, "getIndex", lambda: None)()
    if block_index is not None:
        return ("index", int(block_index))
    return ("id", id(block))

def _impl__zero_iteration_exit_region_op_key(self, op, block) -> Tuple[Any, ...]:
    op_ref = self._make_pcode_op_ref(op)
    if op_ref is not None:
        return ("pcode_op_ref", op_ref.stable_key())
    return (
        "pcode_op_fallback",
        self._block_key(block),
        str(getattr(op, "getMnemonic", lambda: "")() or ""),
        self._safe_pcode_input_count(op),
    )

def _impl__stable_key_or_none(self, value) -> Optional[Tuple[Any, ...]]:
    if value is None:
        return None
    stable_key = getattr(value, "stable_key", None)
    if callable(stable_key):
        try:
            key = stable_key()
        except Exception:
            return None
        if key is None:
            return None
        return key if isinstance(key, tuple) else ("stable", key)
    if isinstance(value, tuple):
        return value
    return None

def _impl__stable_key_looks_like_loop_summary(self, stable_key: Tuple[Any, ...]) -> bool:
    text = repr(stable_key)
    return (
        "loop_summary" in text
        or "COUNTED_LOOP" in text
        or "STATE_TRANSITION_LOOP" in text
        or "READONLY_SUM" in text
    )

def _impl__summary_expression_evidence_key(expr: Optional[Expression]) -> Optional[Tuple[Any, ...]]:
    if expr is None:
        return None
    try:
        return ("expression", ConditionNormalizer.expression_signature(expr))
    except Exception:
        return None

def _impl__expressions_have_same_structural_key(
    self,
    left: Optional[Expression],
    right: Optional[Expression],
) -> bool:
    if left is None or right is None:
        return False
    try:
        return left.structural_key() == right.structural_key()
    except (AttributeError, TypeError, ValueError, RecursionError):
        return False

def _impl__canonicalize_expression(self, expr: Optional[Expression]) -> Optional[Expression]:
    if expr is None:
        return None
    if expr.expr_type == ExpressionType.BINARY_OP and len(expr.operands) == 2:
        left = self._canonicalize_expression(expr.operands[0])
        right = self._canonicalize_expression(expr.operands[1])
        operator = expr.operator
        if operator in {
            "INT_ADD",
            "INT_MULT",
            "INT_AND",
            "INT_OR",
            "INT_XOR",
            "BOOL_AND",
            "BOOL_OR",
            "BOOL_XOR",
            "INT_EQUAL",
            "INT_NOTEQUAL",
        } and _runtime_expression_signature(right) < _runtime_expression_signature(left):
            left, right = right, left
        if left is expr.operands[0] and right is expr.operands[1]:
            return expr
        rebuilt = Expression.binary_op(operator, left, right)
        rebuilt.size = expr.size
        return rebuilt
    if expr.expr_type == ExpressionType.UNARY_OP and len(expr.operands) == 1:
        operand = self._canonicalize_expression(expr.operands[0])
        if expr.operator == "BOOL_NEGATE" and operand.expr_type == ExpressionType.UNARY_OP and operand.operator == "BOOL_NEGATE" and operand.operands:
            return self._canonicalize_expression(operand.operands[0])
        if expr.operator == "BOOL_NEGATE" and operand.expr_type == ExpressionType.BINARY_OP and len(operand.operands) == 2:
            if operand.operator == "INT_NOTEQUAL":
                rebuilt = Expression.binary_op("INT_EQUAL", operand.operands[0], operand.operands[1])
                rebuilt.size = operand.size or expr.size
                return self._canonicalize_expression(rebuilt)
            if operand.operator == "INT_EQUAL":
                rebuilt = Expression.binary_op("INT_NOTEQUAL", operand.operands[0], operand.operands[1])
                rebuilt.size = operand.size or expr.size
                return self._canonicalize_expression(rebuilt)
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
                new_condition_expr = self._canonicalize_expression(condition.expression)
                if new_condition_expr is not condition.expression:
                    new_condition = Condition(new_condition_expr, condition.negated)
                    changed = True
            new_value = self._canonicalize_expression(value)
            if new_value is not value:
                changed = True
            branches.append((new_condition, new_value))
        branches.sort(
            key=lambda item: (
                _runtime_expression_signature(item[0].expression) if item[0] is not None else ("none",),
                bool(getattr(item[0], "negated", False)) if item[0] is not None else False,
                _runtime_expression_signature(item[1]),
            )
        )
        if tuple(branches) != tuple(expr.value):
            changed = True
        if not changed:
            return expr
        rebuilt = Expression.phi(branches)
        rebuilt.size = expr.size
        return rebuilt
    return expr

def _impl__block_identity_key(self, block) -> object:
    if block is None:
        return None
    try:
        return ("block_index", int(block.getIndex()))
    except Exception:
        return ("block_id", id(block))

def _impl__same_varnode_identity(self, left, right) -> bool:
    if left is None or right is None:
        return False
    if left is right:
        return True
    left_key = self._varnode_cache_key(left)
    right_key = self._varnode_cache_key(right)
    return left_key is not None and right_key is not None and left_key == right_key

def _impl__same_pcode_block(self, left, right) -> bool:
    if left is None or right is None:
        return False
    if left is right:
        return True
    try:
        equals = getattr(left, "equals", None)
        if callable(equals) and bool(equals(right)):
            return True
    except Exception:
        pass
    try:
        equals = getattr(right, "equals", None)
        if callable(equals) and bool(equals(left)):
            return True
    except Exception:
        pass
    left_ref = self._make_pcode_block_ref(left)
    right_ref = self._make_pcode_block_ref(right)
    return (
        left_ref is not None
        and right_ref is not None
        and left_ref.stable_key() == right_ref.stable_key()
    )

def _impl__same_storage_varnode(self, left, right) -> bool:
    if left is None or right is None:
        return False
    if left is right:
        return True
    try:
        left_addr = left.getAddress()
        right_addr = right.getAddress()
        if left_addr is None or right_addr is None:
            return False
        return (
            left_addr.getAddressSpace().getName() == right_addr.getAddressSpace().getName()
            and int(left.getOffset()) == int(right.getOffset())
            and int(left.getSize()) == int(right.getSize())
        )
    except Exception:
        return False

def _impl__same_high_variable(self, left, right) -> bool:
    if left is None or right is None:
        return False
    try:
        left_high = left.getHigh()
        right_high = right.getHigh()
    except Exception:
        return False
    if left_high is None or right_high is None:
        return False
    if left_high is right_high:
        return True
    try:
        if left_high == right_high:
            return True
    except Exception:
        pass
    try:
        left_symbol = left_high.getSymbol()
        right_symbol = right_high.getSymbol()
        if left_symbol is not None and right_symbol is not None and left_symbol is right_symbol:
            return True
    except Exception:
        pass
    return False

def _impl__phi_incoming_same_storage_definition(self, phi_op, input_index: int, phi_output):
    parent = getattr(phi_op, "getParent", lambda: None)()
    if parent is None or phi_output is None:
        return None
    incoming_block = self._phi_incoming_block(parent, int(input_index))
    if incoming_block is None:
        return None
    raw_input = None
    try:
        raw_input = phi_op.getInput(int(input_index))
    except Exception:
        raw_input = None
    for candidate_op in reversed(list(self._iter_block_ops(incoming_block))):
        output = getattr(candidate_op, "getOutput", lambda: None)()
        if output is None:
            continue
        if self._same_storage_varnode(output, phi_output) or self._same_storage_varnode(output, raw_input):
            return output
    return None

def _impl__pcode_block_group_key(self, block) -> Optional[Tuple[int, Optional[int]]]:
    if block is None:
        return None
    try:
        index = int(getattr(block, "getIndex", lambda: -1)() or -1)
    except Exception:
        index = -1
    try:
        start = getattr(block, "getStart", lambda: None)()
        start_offset = int(start.getOffset()) if start is not None else None
    except Exception:
        start_offset = None
    return (index, start_offset)

def _impl__varnode_cache_key(self, varnode):
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

def _impl__loop_variable_identity_ref(
    self,
    role: str,
    varnode,
    *,
    binder_ordinal: int = 0,
) -> Optional[LoopVariableIdentityRef]:
    key = self._varnode_cache_key(varnode)
    if key is None:
        return None
    return LoopVariableIdentityRef(
        role=str(role or "loop_variable"),
        binder_ordinal=max(0, int(binder_ordinal)),
        varnode_key=key,
    )

def _impl__same_varnode_value(self, left, right) -> bool:
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

def _impl__same_placeholder_varnode(self, left, right) -> bool:
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

def _impl__parameter_identity_keys_from_descriptor(
    self,
    parameter: dict,
) -> set[Tuple[Any, ...]]:
    identities: set[Tuple[Any, ...]] = set()
    try:
        index = int(parameter.get("index", -1))
    except (TypeError, ValueError):
        index = -1
    if index >= 0:
        identities.add(("parameter_index", index))
    storage_key = self._summary_storage_identity_key(
        parameter.get("storage_info", parameter.get("storage"))
    )
    if storage_key is not None:
        identities.add(("parameter_storage", storage_key))
    return identities

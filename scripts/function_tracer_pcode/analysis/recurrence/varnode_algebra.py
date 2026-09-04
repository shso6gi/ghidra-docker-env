"""Varnode value-preservation paths, scaled counter/parameter forms, constants and rounding recognition."""

from __future__ import annotations

from typing import Any, Iterable, List, Optional, Tuple
from scripts.function_tracer_pcode.core import Expression, ExpressionType, StorageInfo
from scripts.function_tracer_pcode.analysis.recurrence._shared import (
    parameter_identity_key_from_expression,
)


def _impl__value_preserving_varnode_path(
    self,
    start_varnode,
    target_varnode,
    *,
    budget: int = 128,
) -> Optional[Tuple[Tuple[Any, ...], ...]]:
    if start_varnode is None or target_varnode is None:
        return None
    if self._same_varnode_object_identity(start_varnode, target_varnode):
        edge = self._value_preserving_edge_key("identity", start_varnode, target_varnode)
        return (edge,) if edge is not None else None
    stack = [(start_varnode, ())]
    seen = set()
    exhausted = False
    while stack:
        if len(seen) >= budget:
            exhausted = True
            break
        current, path = stack.pop()
        if current is None:
            continue
        current_id = id(current)
        if current_id in seen:
            continue
        seen.add(current_id)
        descendants = getattr(current, "getDescendants", lambda: None)()
        if descendants is None:
            continue
        for op in self._iter_descendant_ops(descendants):
            edge_kind = self._value_preserving_edge_kind(op, current)
            if edge_kind is None:
                continue
            output = getattr(op, "getOutput", lambda: None)()
            if output is not None:
                edge = self._value_preserving_edge_key(edge_kind, current, output, op=op)
                if edge is None:
                    continue
                next_path = path + (edge,)
                if self._same_varnode_object_identity(output, target_varnode):
                    return next_path
                stack.append((output, next_path))
    return None if exhausted else None


def _impl__iter_descendant_ops(self, descendants) -> Iterable[Any]:
    try:
        iterator = iter(descendants)
    except TypeError:
        iterator = None
    if iterator is not None:
        yield from iterator
        return
    while descendants.hasNext():
        yield descendants.next()


def _impl__value_preserving_edge_kind(self, op, input_varnode) -> Optional[str]:
    mnemonic = getattr(op, "getMnemonic", lambda: None)()
    output = getattr(op, "getOutput", lambda: None)()
    if output is None:
        return None
    if self._safe_pcode_input_count(op) < 1:
        return None
    try:
        first_input = op.getInput(0)
    except Exception:
        return None
    if not self._same_varnode_object_identity(first_input, input_varnode):
        return None
    if mnemonic == "COPY":
        return "COPY"
    if mnemonic == "SUBPIECE":
        if self._safe_pcode_input_count(op) < 2:
            return None
        offset = self._varnode_constant_value(op.getInput(1))
        if int(offset or 0) == 0 and self._varnode_size_bits(input_varnode) == self._varnode_size_bits(output):
            return "SUBPIECE_ZERO_SAME_WIDTH"
        return None
    if mnemonic in {"INT_ZEXT", "INT_SEXT"}:
        in_bits = self._varnode_size_bits(input_varnode)
        out_bits = self._varnode_size_bits(output)
        if in_bits > 0 and out_bits >= in_bits:
            return mnemonic
    return None


def _impl__varnode_size_bits(self, varnode) -> int:
    try:
        return max(1, int(getattr(varnode, "getSize", lambda: 0)() or 0)) * 8
    except Exception:
        return 0


def _impl__round_down_quotient_source(
    self,
    quotient_vn,
    count_param: dict,
    lane_count: int,
) -> Optional[Tuple[object, int, int]]:
    quotient_vn = self._follow_passthrough_varnode(quotient_vn)
    def_op = getattr(quotient_vn, "getDef", lambda: None)()
    if def_op is None or int(getattr(def_op, "getNumInputs", lambda: 0)() or 0) < 2:
        return None
    mnemonic = getattr(def_op, "getMnemonic", lambda: None)()
    dividend = self._follow_passthrough_varnode(def_op.getInput(0))
    divisor_or_shift = self._varnode_unsigned_constant_value(def_op.getInput(1))
    if mnemonic == "INT_SUB" and divisor_or_shift == 1:
        source = self._round_down_quotient_source(dividend, count_param, lane_count)
        if source is None:
            return None
        source_vn, start_index, tail_start_index_delta = source
        return source_vn, start_index, tail_start_index_delta + int(lane_count)
    if mnemonic in {"INT_DIV", "INT_SDIV"}:
        if divisor_or_shift is None or int(divisor_or_shift) != int(lane_count):
            return None
        source = self._rounded_count_source(dividend, count_param)
        if source is None:
            return None
        _count_source_vn, start_index = source
        return dividend, start_index, 0
    if mnemonic in {"INT_RIGHT", "INT_SRIGHT"}:
        if divisor_or_shift is None or int(lane_count) != (1 << int(divisor_or_shift)):
            return None
        source = self._rounded_count_source(dividend, count_param)
        if source is None:
            return None
        _count_source_vn, start_index = source
        return dividend, start_index, 0
    return None


def _impl__rounded_count_source(
    self,
    value,
    count_param: dict,
) -> Optional[Tuple[object, int]]:
    value = self._follow_passthrough_varnode(value)
    if self._varnode_matches_parameter(value, count_param):
        return value, 0

    def_op = getattr(value, "getDef", lambda: None)()
    if def_op is None:
        return None
    mnemonic = getattr(def_op, "getMnemonic", lambda: None)()
    if int(getattr(def_op, "getNumInputs", lambda: 0)() or 0) < 2:
        return None

    left = self._follow_passthrough_varnode(def_op.getInput(0))
    right = self._follow_passthrough_varnode(def_op.getInput(1))
    if mnemonic == "INT_SUB" and self._varnode_matches_parameter(left, count_param):
        peeled = self._varnode_unsigned_constant_value(right)
        if peeled is not None and int(peeled) >= 0:
            return left, int(peeled)
        return None
    if mnemonic == "INT_ADD":
        if self._varnode_matches_parameter(left, count_param):
            delta = self._signed_varnode_constant_value(right)
            if delta is not None and int(delta) <= 0:
                return left, -int(delta)
        if self._varnode_matches_parameter(right, count_param):
            delta = self._signed_varnode_constant_value(left)
            if delta is not None and int(delta) <= 0:
                return right, -int(delta)
    return None


def _impl__power_of_two_rounding_from_mask(self, mask: int, *, count_width_bits: int) -> Optional[int]:
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


def _impl__varnode_bit_width(self, varnode) -> Optional[int]:
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


def _impl__varnode_depends_on_varnode(self, start_varnode, target_varnode, *, budget: int = 64) -> bool:
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


def _impl__varnode_input_multiplicity(self, op, varnode) -> int:
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


def _impl__iter_varnode_descendant_ops(self, varnode):
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


def _impl__varnode_is_count_minus_rounded(
    self,
    candidate_vn,
    count_param: dict,
    rounded_vn,
    *,
    start_index: int = 0,
) -> bool:
    candidate_vn = self._follow_passthrough_varnode(candidate_vn)
    if int(start_index) > 0:
        def_op = getattr(candidate_vn, "getDef", lambda: None)()
        if def_op is not None and getattr(def_op, "getMnemonic", lambda: None)() == "INT_SUB":
            if int(getattr(def_op, "getNumInputs", lambda: 0)() or 0) >= 2:
                left = self._follow_passthrough_varnode(def_op.getInput(0))
                right = self._follow_passthrough_varnode(def_op.getInput(1))
                if self._signed_varnode_constant_value(right) == int(start_index):
                    return self._varnode_is_count_minus_rounded(
                        left,
                        count_param,
                        rounded_vn,
                        start_index=0,
                    )
        if self._varnode_is_count_minus_rounded_plus_start(
            candidate_vn,
            count_param,
            rounded_vn,
            start_index=int(start_index),
        ):
            return True
    def_op = getattr(candidate_vn, "getDef", lambda: None)()
    if def_op is None or getattr(def_op, "getMnemonic", lambda: None)() != "INT_SUB":
        return False
    if int(getattr(def_op, "getNumInputs", lambda: 0)() or 0) < 2:
        return False
    left = self._follow_passthrough_varnode(def_op.getInput(0))
    right = self._follow_passthrough_varnode(def_op.getInput(1))
    return (
        self._varnode_matches_parameter(left, count_param)
        and self._same_varnode_value(right, rounded_vn)
    )


def _impl__varnode_is_count_minus_rounded_plus_start(
    self,
    candidate_vn,
    count_param: dict,
    rounded_vn,
    *,
    start_index: int,
) -> bool:
    candidate_vn = self._follow_passthrough_varnode(candidate_vn)
    def_op = getattr(candidate_vn, "getDef", lambda: None)()
    if def_op is None or getattr(def_op, "getMnemonic", lambda: None)() != "INT_SUB":
        return False
    if int(getattr(def_op, "getNumInputs", lambda: 0)() or 0) < 2:
        return False
    left = self._follow_passthrough_varnode(def_op.getInput(0))
    right = self._follow_passthrough_varnode(def_op.getInput(1))
    if not self._varnode_matches_parameter(left, count_param):
        return False
    return self._rounded_tail_index_varnode_matches(
        right,
        rounded_vn,
        start_index=int(start_index),
    )


def _impl__varnode_is_base_plus_scaled_parameter(
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
            and self._varnode_matches_parameter(base, pointer_param)
            and self._varnode_matches_parameter(index, count_param)
            and int(byte_offset) == 0
        ):
            return True
    scaled_count = self._scaled_parameter_varnode(candidate_vn, count_param, element_size=element_size)
    if scaled_count is not None and self._varnode_matches_parameter(scaled_count, pointer_param):
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
        if self._varnode_matches_parameter(left, pointer_param):
            return self._varnode_is_scaled_parameter_plus_constant(
                right,
                count_param,
                element_size=element_size,
                byte_offset=byte_offset,
            )
        if mnemonic == "INT_ADD" and self._varnode_matches_parameter(right, pointer_param):
            return self._varnode_is_scaled_parameter_plus_constant(
                left,
                count_param,
                element_size=element_size,
                byte_offset=byte_offset,
            )
    return False


def _impl__varnode_is_base_plus_scaled_counter(
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
        if elem == int(element_size):
            base_offset = self._byte_offset_from_parameter_pointer(base, pointer_param)
            if base_offset is not None and self._same_varnode_value(index, counter_vn):
                return int(base_offset) == int(byte_offset)
            index_delta = self._counter_plus_constant_delta(index, counter_vn)
            if (
                index_delta is not None
                and self._varnode_matches_parameter(base, pointer_param)
                and int(index_delta) * int(element_size) == int(byte_offset)
            ):
                return True
            if (
                int(byte_offset) % int(element_size) == 0
                and self._varnode_matches_parameter(base, pointer_param)
                and self._rounded_tail_index_varnode_matches(
                    index,
                    counter_vn,
                    start_index=int(byte_offset) // int(element_size),
                )
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
        if self._varnode_matches_parameter(left, pointer_param):
            return self._varnode_is_scaled_counter_plus_constant(
                right,
                counter_vn,
                element_size=element_size,
                byte_offset=byte_offset,
            )
        if mnemonic == "INT_ADD" and self._varnode_matches_parameter(right, pointer_param):
            return self._varnode_is_scaled_counter_plus_constant(
                left,
                counter_vn,
                element_size=element_size,
                byte_offset=byte_offset,
            )
    return False


def _impl__varnode_low_bits_clear(self, candidate_vn, bit_count: int) -> bool:
    if int(bit_count) <= 0:
        return True
    candidate_vn = self._follow_passthrough_varnode(candidate_vn)
    mask = (1 << int(bit_count)) - 1
    constant = self._varnode_unsigned_constant_value(candidate_vn)
    if constant is not None:
        return (int(constant) & mask) == 0
    def_op = getattr(candidate_vn, "getDef", lambda: None)()
    if def_op is None or int(getattr(def_op, "getNumInputs", lambda: 0)() or 0) < 2:
        return False
    mnemonic = getattr(def_op, "getMnemonic", lambda: None)()
    if mnemonic == "INT_AND":
        left = self._follow_passthrough_varnode(def_op.getInput(0))
        right = self._follow_passthrough_varnode(def_op.getInput(1))
        left_const = self._varnode_unsigned_constant_value(left)
        right_const = self._varnode_unsigned_constant_value(right)
        if left_const is not None and (int(left_const) & mask) == 0:
            return True
        if right_const is not None and (int(right_const) & mask) == 0:
            return True
    return False


def _impl__counter_plus_constant_delta(
    self,
    candidate_vn,
    counter_vn,
) -> Optional[int]:
    candidate_vn = self._follow_passthrough_varnode(candidate_vn)
    if self._same_varnode_value(candidate_vn, counter_vn):
        return 0
    def_op = getattr(candidate_vn, "getDef", lambda: None)()
    if def_op is None:
        return None
    mnemonic = getattr(def_op, "getMnemonic", lambda: None)()
    if mnemonic not in {"INT_ADD", "INT_SUB", "INT_OR"}:
        return None
    if int(getattr(def_op, "getNumInputs", lambda: 0)() or 0) < 2:
        return None
    left = self._follow_passthrough_varnode(def_op.getInput(0))
    right = self._follow_passthrough_varnode(def_op.getInput(1))
    if mnemonic == "INT_OR":
        right_const = self._signed_varnode_constant_value(right)
        if self._same_varnode_value(left, counter_vn) and right_const is not None:
            if self._counter_low_bits_clear_for_or_delta(counter_vn, int(right_const)):
                return int(right_const)
        left_const = self._signed_varnode_constant_value(left)
        if self._same_varnode_value(right, counter_vn) and left_const is not None:
            if self._counter_low_bits_clear_for_or_delta(counter_vn, int(left_const)):
                return int(left_const)
        return None
    right_const = self._signed_varnode_constant_value(right)
    if self._same_varnode_value(left, counter_vn) and right_const is not None:
        return int(right_const) if mnemonic == "INT_ADD" else -int(right_const)
    if mnemonic == "INT_ADD":
        left_const = self._signed_varnode_constant_value(left)
        if self._same_varnode_value(right, counter_vn) and left_const is not None:
            return int(left_const)
    return None


def _impl__counter_low_bits_clear_for_or_delta(
    self,
    counter_vn,
    delta: int,
) -> bool:
    if int(delta) < 0:
        return False
    if int(delta) == 0:
        return True
    counter_bits = None
    try:
        counter_expr = self._build_pcode_expression(counter_vn, placeholders={})
    except Exception:
        counter_expr = None
    if counter_expr is not None:
        candidate_names = []
        counter_name = self._parameter_name_from_expr(counter_expr)
        if counter_name is not None:
            candidate_names.append(counter_name)
        else:
            candidate_names.extend(self._parameter_names_from_expr(counter_expr))
        candidate_bits: List[int] = []
        for name in candidate_names:
            if not name:
                continue
            inferred_bits = self._infer_counter_bit_width(counter_expr, str(name))
            if inferred_bits is not None and int(inferred_bits) > 0:
                candidate_bits.append(int(inferred_bits))
        if candidate_bits:
            counter_bits = min(candidate_bits)
    if counter_bits is None:
        counter_bits = self._varnode_bit_width(counter_vn)
    if counter_bits is not None and int(delta) >= (1 << int(counter_bits)):
        return False
    counter_vn = self._follow_passthrough_varnode(counter_vn)
    def_op = getattr(counter_vn, "getDef", lambda: None)()
    if def_op is None or getattr(def_op, "getMnemonic", lambda: None)() != "INT_AND":
        return False
    if int(getattr(def_op, "getNumInputs", lambda: 0)() or 0) < 2:
        return False
    left = self._follow_passthrough_varnode(def_op.getInput(0))
    right = self._follow_passthrough_varnode(def_op.getInput(1))
    mask = self._varnode_unsigned_constant_value(left)
    if mask is None:
        mask = self._varnode_unsigned_constant_value(right)
    if mask is None:
        return False
    return (int(mask) & int(delta)) == 0


def _impl__varnode_is_scaled_parameter_plus_constant(
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


def _impl__varnode_is_scaled_counter_plus_constant(
    self,
    candidate_vn,
    counter_vn,
    *,
    element_size: int,
    byte_offset: int,
) -> bool:
    candidate_vn = self._follow_passthrough_varnode(candidate_vn)
    scaled_delta = self._scaled_counter_delta_bytes(
        candidate_vn,
        counter_vn,
        element_size=element_size,
    )
    if scaled_delta is not None:
        return int(scaled_delta) == int(byte_offset)
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


def _impl__scaled_counter_delta_bytes(
    self,
    candidate_vn,
    counter_vn,
    *,
    element_size: int,
) -> Optional[int]:
    candidate_vn = self._follow_passthrough_varnode(candidate_vn)
    def_op = getattr(candidate_vn, "getDef", lambda: None)()
    if def_op is None:
        return None
    mnemonic = getattr(def_op, "getMnemonic", lambda: None)()
    if mnemonic == "INT_MULT" and int(getattr(def_op, "getNumInputs", lambda: 0)() or 0) >= 2:
        left = self._follow_passthrough_varnode(def_op.getInput(0))
        right = self._follow_passthrough_varnode(def_op.getInput(1))
        right_elem = self._varnode_unsigned_constant_value(right)
        if right_elem == int(element_size):
            delta = self._counter_plus_constant_delta(left, counter_vn)
            if delta is not None:
                return int(delta) * int(element_size)
        left_elem = self._varnode_unsigned_constant_value(left)
        if left_elem == int(element_size):
            delta = self._counter_plus_constant_delta(right, counter_vn)
            if delta is not None:
                return int(delta) * int(element_size)
        return None
    if mnemonic == "INT_LEFT" and int(getattr(def_op, "getNumInputs", lambda: 0)() or 0) >= 2:
        shifted = self._follow_passthrough_varnode(def_op.getInput(0))
        shift_bits = self._varnode_unsigned_constant_value(self._follow_passthrough_varnode(def_op.getInput(1)))
        if shift_bits is None or (1 << int(shift_bits)) != int(element_size):
            return None
        delta = self._counter_plus_constant_delta(shifted, counter_vn)
        if delta is not None:
            return int(delta) * int(element_size)
    return None


def _impl__scaled_parameter_varnode(
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
        if self._varnode_matches_parameter(left, count_param) and self._varnode_unsigned_constant_value(right) == int(element_size):
            return left
        if self._varnode_matches_parameter(right, count_param) and self._varnode_unsigned_constant_value(left) == int(element_size):
            return right
    if mnemonic == "INT_LEFT" and int(getattr(def_op, "getNumInputs", lambda: 0)() or 0) >= 2:
        shifted = self._follow_passthrough_varnode(def_op.getInput(0))
        shift_bits = self._varnode_unsigned_constant_value(self._follow_passthrough_varnode(def_op.getInput(1)))
        if (
            shift_bits is not None
            and (1 << int(shift_bits)) == int(element_size)
            and self._varnode_matches_parameter(shifted, count_param)
        ):
            return shifted
    return None


def _impl__varnode_is_scaled_counter(
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


def _impl__low_mask_width_bytes(
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


def _impl__varnode_is_int_to_float_parameter(self, varnode, parameter: Optional[dict]) -> bool:
    if not isinstance(parameter, dict):
        return False
    varnode = self._follow_readonly_load_addend_passthrough(varnode)
    def_op = getattr(varnode, "getDef", lambda: None)()
    if def_op is None or getattr(def_op, "getMnemonic", lambda: None)() != "INT2FLOAT":
        return False
    if int(getattr(def_op, "getNumInputs", lambda: 0)() or 0) < 1:
        return False
    return self._varnode_matches_parameter(def_op.getInput(0), parameter)


def _impl__low_mask_width_bytes_from_value(self, mask: int) -> Optional[int]:
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


def _impl__follow_passthrough_varnode(self, varnode):
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


def _impl__varnode_matches_parameter(
    self,
    varnode,
    parameter: dict,
) -> bool:
    if not isinstance(parameter, dict):
        return False
    varnode = self._follow_passthrough_varnode(varnode)
    parameter_identities = self._parameter_identity_keys_from_descriptor(parameter)
    if not parameter_identities:
        return False

    varnode_storage = self._storage_info_from_varnode(varnode)
    storage_key = self._summary_storage_identity_key(varnode_storage)
    if storage_key is not None and ("parameter_storage", storage_key) in parameter_identities:
        return True

    high = getattr(varnode, "getHigh", lambda: None)()
    symbol_getter = getattr(high, "getSymbol", lambda: None)
    if callable(symbol_getter):
        try:
            symbol = symbol_getter()
            symbol_index = self._parameter_index_from_symbol(symbol)
            if symbol_index is not None and ("parameter_index", symbol_index) in parameter_identities:
                return True
        except Exception:
            pass
    expr = self._trace_varnode_expression(varnode)
    expr_identity = (
        parameter_identity_key_from_expression(expr)
        if getattr(expr, "expr_type", None) == ExpressionType.PARAMETER
        else None
    )
    return bool(expr_identity is not None and expr_identity in parameter_identities)


def _impl__storage_info_from_varnode(self, varnode) -> Optional[StorageInfo]:
    getter = getattr(self.tracer, "_get_storage_info_from_varnode", None)
    if callable(getter):
        try:
            storage = getter(varnode)
            if isinstance(storage, StorageInfo):
                return storage
            if isinstance(storage, dict):
                return StorageInfo(**storage)
        except Exception:
            return None
    return None


def _impl__varnode_constant_value(
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


def _impl__varnode_unsigned_constant_value(self, varnode) -> Optional[int]:
    value = self._varnode_constant_value(varnode)
    if value is None:
        return None
    return int(value)


def _impl__signed_varnode_constant_value(self, varnode) -> Optional[int]:
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


def _impl__float_add_has_zero_other_operand(self, op, current_varnode) -> bool:
    if int(getattr(op, "getNumInputs", lambda: 0)() or 0) < 2:
        return False
    left = self._follow_passthrough_varnode(op.getInput(0))
    right = self._follow_passthrough_varnode(op.getInput(1))
    if self._same_varnode_value(left, current_varnode):
        return self._varnode_constant_value(right) == 0
    if self._same_varnode_value(right, current_varnode):
        return self._varnode_constant_value(left) == 0
    return False


def _impl__float_div_is_average_projection(self, op, current_varnode, count_param: dict) -> bool:
    if int(getattr(op, "getNumInputs", lambda: 0)() or 0) < 2:
        return False
    numerator = self._follow_passthrough_varnode(op.getInput(0))
    if not self._same_varnode_value(numerator, current_varnode):
        return False
    denominator = self._follow_passthrough_varnode(op.getInput(1))
    denominator_def = getattr(denominator, "getDef", lambda: None)()
    if denominator_def is None or getattr(denominator_def, "getMnemonic", lambda: None)() != "INT2FLOAT":
        return False
    if int(getattr(denominator_def, "getNumInputs", lambda: 0)() or 0) < 1:
        return False
    return self._varnode_matches_parameter(denominator_def.getInput(0), count_param)

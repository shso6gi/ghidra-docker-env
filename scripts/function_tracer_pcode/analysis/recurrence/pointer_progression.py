"""Stateless method implementations extracted from ``scripts.function_tracer_pcode.analysis.recurrence_summary``."""

from __future__ import annotations

from typing import Any
from ._shared import (
    Condition,
    Expression,
    ExpressionType,
    LocationBaseRef,
    PcodeOpRef,
    canonicalize_location,
    is_pointer_data_type,
)

def invoke(_service_name: str, *args: Any, **kwargs: Any) -> Any:
    implementation_function = globals().get(f"_impl_{_service_name}")
    if implementation_function is None:
        raise AttributeError(_service_name)
    return implementation_function(*args, **kwargs)


def implementation(_service_name: str):
    return globals().get(f"_impl_{_service_name}")

def _impl__store_address_space_ref_for_op(self, op):
    if op is None or self._safe_pcode_input_count(op) < 1:
        return None
    space_varnode = op.getInput(0)

    try:
        address = getattr(space_varnode, "getAddress", lambda: None)()
    except Exception:
        address = None
    address_space = getattr(address, "getAddressSpace", lambda: None)() if address is not None else None
    input_space_ref = self._address_space_ref(address_space)
    try:
        offset = getattr(space_varnode, "getOffset", lambda: None)()
    except Exception:
        offset = None
    try:
        size = getattr(space_varnode, "getSize", lambda: None)()
    except Exception:
        size = None
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

def _impl__resolve_store_target_address_space_ref(self, space_id: Optional[int]) -> Optional[Dict[str, Any]]:
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

def _impl__address_space_ref(self, address_space) -> Optional[Dict[str, Any]]:
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

def _impl__location_base_ref_from_parameter(self, param: dict, *, default_name: str) -> LocationBaseRef:
    name = param.get("name", default_name) if isinstance(param, dict) else default_name
    try:
        index = int(param.get("index")) if isinstance(param, dict) and param.get("index") is not None else None
    except (TypeError, ValueError):
        index = None
    if index is not None and index >= 0:
        return LocationBaseRef.parameter(
            name,
            index=index,
            owner_program_id=param.get("owner_program_id") if isinstance(param, dict) else None,
            owner_entry_offset=param.get("owner_entry_offset") if isinstance(param, dict) else None,
        )
    storage_info = self._summary_storage_info_from_parameter(param if isinstance(param, dict) else {})
    storage_key = self._summary_storage_identity_key(storage_info)
    if storage_info is not None and storage_key is not None:
        offset = (
            int(getattr(storage_info, "base_register_offset", 0) or 0)
            if bool(getattr(storage_info, "is_register", False))
            else int(getattr(storage_info, "offset", 0) or 0)
        )
        size = max(1, int(getattr(storage_info, "size", 0) or 0))
        return LocationBaseRef.storage(
            space_id=getattr(storage_info, "space_id", None),
            space_name=getattr(storage_info, "space_name", None),
            offset=offset,
            size=size,
            storage_identity_key=storage_key,
            display_hint=name,
        )
    return LocationBaseRef.parameter(name, index=None)

def _impl__induction_init_index(
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

def _impl__accumulator_init_index(
    self,
    accumulator: CountedLoopAccumulator,
    induction: CountedLoopInduction,
) -> int:
    init_index = getattr(accumulator, "init_index", None)
    if isinstance(init_index, int):
        return init_index
    return self._induction_init_index(induction)

def _impl__expression_contains_executable_address_constant(
    self,
    expr: Optional[Expression],
    *,
    function_body_ranges: Sequence[Tuple[int, int]] = (),
) -> bool:
    program = getattr(self.tracer, "program", None)
    if program is None and not function_body_ranges:
        return False
    if expr is None:
        return False
    for node in self._iter_expression_nodes(expr):
        if getattr(node, "expr_type", None) != ExpressionType.CONSTANT:
            continue
        value = self._raw_constant_value(node)
        if value is None:
            continue
        if self._constant_resolves_to_function_body_address(value, function_body_ranges):
            return True
        if self._constant_resolves_to_executable_address(value):
            return True
    return False

def _impl__constant_resolves_to_function_body_address(
    self,
    value: int,
    function_body_ranges: Sequence[Tuple[int, int]],
) -> bool:
    try:
        value = int(value)
    except (TypeError, ValueError):
        return False
    for start, end in function_body_ranges or ():
        try:
            start_int = int(start)
            end_int = int(end)
        except (TypeError, ValueError):
            continue
        if start_int <= value <= end_int:
            return True
    return False

def _impl__constant_resolves_to_executable_address(self, value: int) -> bool:
    try:
        value = int(value)
    except (TypeError, ValueError):
        return False
    if value < 0:
        return False
    program = getattr(self.tracer, "program", None)
    if program is None:
        return False
    try:
        memory = program.getMemory()
    except Exception:
        memory = None
    if memory is None:
        return False
    address = None
    try:
        address_factory = program.getAddressFactory()
        default_space = address_factory.getDefaultAddressSpace()
        address = default_space.getAddress(value)
    except Exception:
        address = None
    if address is None:
        return False
    try:
        block = memory.getBlock(address)
    except Exception:
        block = None
    if block is None:
        return False
    try:
        return bool(block.isExecute())
    except Exception:
        return False

def _impl__function_body_address_ranges(self, high_function, analysis, *, function=None) -> Tuple[Tuple[int, int], ...]:
    ranges: List[Tuple[int, int]] = []

    def add_range(start, end) -> None:
        try:
            start_int = int(start)
            end_int = int(end)
        except (TypeError, ValueError):
            return
        if start_int < 0 or end_int < 0:
            return
        if end_int < start_int:
            start_int, end_int = end_int, start_int
        ranges.append((start_int, end_int))

    if function is None:
        getter = getattr(high_function, "getFunction", None)
    else:
        getter = None
    if function is None and callable(getter):
        try:
            function = getter()
        except Exception:
            function = None
    body = None
    body_getter = getattr(function, "getBody", None)
    if callable(body_getter):
        try:
            body = body_getter()
        except Exception:
            body = None
    if body is not None:
        try:
            min_address = body.getMinAddress()
            max_address = body.getMaxAddress()
            add_range(min_address.getOffset(), max_address.getOffset())
        except Exception:
            pass

    entry_value = None
    entry_getter = getattr(function, "getEntryPoint", None)
    if callable(entry_getter):
        try:
            entry_point = entry_getter()
            entry_value = int(entry_point.getOffset())
        except Exception:
            entry_value = None
    function_ref = getattr(analysis, "function_ref", None)
    if entry_value is None and function_ref is not None:
        entry_value = getattr(function_ref, "entry_offset", None)
    if entry_value is None:
        entry_point = getattr(analysis, "entry_point", None)
        if entry_point is not None:
            try:
                entry_value = int(str(entry_point), 16)
            except (TypeError, ValueError):
                entry_value = None
    if entry_value is not None:
        max_seen = int(entry_value)
        for ret in getattr(analysis, "returns", None) or ():
            address = getattr(ret, "address", None)
            if address is None:
                continue
            try:
                max_seen = max(max_seen, int(str(address), 16))
            except (TypeError, ValueError):
                continue
        if max_seen > int(entry_value):
            add_range(int(entry_value), max(max_seen + 0x100, int(entry_value) + 0x1000))
        else:
            add_range(int(entry_value), int(entry_value) + 0x1000)

    return tuple(dict.fromkeys(ranges))

def _impl__expression_contains_address_literal_access(
    self,
    expr: Optional[Expression],
    *,
    function_body_ranges: Sequence[Tuple[int, int]] = (),
) -> bool:
    for node in self._iter_expression_nodes(expr):
        if getattr(node, "expr_type", None) != ExpressionType.BINARY_OP:
            continue
        if getattr(node, "operator", None) not in {
            "SUBPIECE",
            "PIECE",
            "INT_RIGHT",
            "INT_SRIGHT",
            "INT_LEFT",
            "LOAD",
            "PTRADD",
            "PTRSUB",
        }:
            continue
        operands = tuple(getattr(node, "operands", ()) or ())
        for operand in operands:
            if self._expression_contains_address_constant(
                operand,
                function_body_ranges=function_body_ranges,
            ):
                return True
    return False

def _impl__expression_contains_address_constant(
    self,
    expr: Optional[Expression],
    *,
    function_body_ranges: Sequence[Tuple[int, int]] = (),
) -> bool:
    for node in self._iter_expression_nodes(expr):
        if getattr(node, "expr_type", None) != ExpressionType.CONSTANT:
            continue
        value = self._raw_constant_value(node)
        if value is None:
            continue
        try:
            integer_value = int(value)
        except (TypeError, ValueError):
            continue
        if self._constant_resolves_to_function_body_address(integer_value, function_body_ranges):
            return True
        if self._constant_resolves_to_executable_address(integer_value):
            return True
    return False

def _impl__bounded_prefix_exact_insert_index(
    self,
    existing_returns: Sequence[ReturnInfo],
    bounded_region_anchors: Sequence[Tuple[ReturnInfo, Sequence[Condition]]],
) -> int:
    for index, existing in enumerate(existing_returns or []):
        if any(existing is bounded_anchor for bounded_anchor, _ in bounded_region_anchors or []):
            return index
    for index, existing in enumerate(existing_returns or []):
        if any(
            self._conditions_equivalent_object_centric(existing.conditions or [], bounded_conditions)
            for _bounded_anchor, bounded_conditions in bounded_region_anchors or []
        ):
            return index
    return len(existing_returns or [])

def _impl__parameter_has_pointer_progression(
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

def _impl__parameter_has_pointer_guards(
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

def _impl__return_info_address_matches_pcode_ref(
    self,
    ret: ReturnInfo,
    ref: PcodeOpRef,
) -> bool:
    if ref.address_offset is None:
        return True
    address = self._return_info_address_offset(ret)
    return address is not None and int(address) == int(ref.address_offset)

def _impl__return_info_address_offset(self, ret: ReturnInfo) -> Optional[int]:
    ret_ref = getattr(ret, "pcode_op_ref", None)
    if isinstance(ret_ref, PcodeOpRef) and ret_ref.address_offset is not None:
        return int(ret_ref.address_offset)
    candidates = [getattr(ret, "address", None), getattr(ret, "pcode_identity", None)]
    for candidate in candidates:
        if not isinstance(candidate, str) or not candidate:
            continue
        address_offset, _time, _order = self._parse_pcode_site_text(candidate)
        if address_offset is not None:
            return address_offset
    return None

def _impl__parse_pcode_address_offset(self, text: str) -> Optional[int]:
    if not isinstance(text, str):
        return None
    token = text.strip()
    if not token:
        return None
    token = token.rsplit(":", 1)[-1].strip()
    if not token:
        return None
    try:
        return int(token, 16)
    except Exception:
        try:
            return int(token, 0)
        except Exception:
            return None

def _impl__pointer_phi_seed_offsets(
    self,
    phi_op,
    pointer_param: dict,
) -> Tuple[int, ...]:
    offsets: List[int] = []
    input_count = int(getattr(phi_op, "getNumInputs", lambda: 0)() or 0)
    for index in range(input_count):
        try:
            value = self._follow_passthrough_varnode(phi_op.getInput(index))
        except Exception:
            continue
        offset = self._byte_offset_from_parameter_pointer(value, pointer_param)
        if offset is not None:
            offsets.append(int(offset))
    return tuple(dict.fromkeys(offsets))

def _impl__byte_offset_from_parameter_pointer(
    self,
    candidate_vn,
    pointer_param: dict,
) -> Optional[int]:
    candidate_vn = self._follow_passthrough_varnode(candidate_vn)
    def_op = getattr(candidate_vn, "getDef", lambda: None)()
    if def_op is not None:
        mnemonic = getattr(def_op, "getMnemonic", lambda: None)()
        if mnemonic in {"INT_ADD", "PTRSUB"} and int(getattr(def_op, "getNumInputs", lambda: 0)() or 0) >= 2:
            left = self._follow_passthrough_varnode(def_op.getInput(0))
            right = self._follow_passthrough_varnode(def_op.getInput(1))
            right_const = self._signed_varnode_constant_value(right)
            if right_const is not None:
                left_offset = self._byte_offset_from_parameter_pointer(left, pointer_param)
                if left_offset is not None:
                    return int(left_offset) + int(right_const)
            if mnemonic == "INT_ADD":
                left_const = self._signed_varnode_constant_value(left)
                if left_const is not None:
                    right_offset = self._byte_offset_from_parameter_pointer(right, pointer_param)
                    if right_offset is not None:
                        return int(right_offset) + int(left_const)
            return None
        if mnemonic == "PTRADD" and int(getattr(def_op, "getNumInputs", lambda: 0)() or 0) >= 3:
            base = self._follow_passthrough_varnode(def_op.getInput(0))
            index = self._signed_varnode_constant_value(self._follow_passthrough_varnode(def_op.getInput(1)))
            elem = self._varnode_unsigned_constant_value(self._follow_passthrough_varnode(def_op.getInput(2)))
            if index is None or elem is None:
                return None
            base_offset = self._byte_offset_from_parameter_pointer(base, pointer_param)
            if base_offset is None:
                return None
            return int(base_offset) + int(index) * int(elem)
    if self._varnode_matches_parameter(candidate_vn, pointer_param):
        return 0
    return None

def _impl__phi_has_pointer_step(
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

def _impl__has_pointer_base_plus_constant(
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
                self._varnode_matches_parameter(left, pointer_param)
                and self._signed_varnode_constant_value(right) == int(byte_offset)
            ):
                return True
            if (
                mnemonic == "INT_ADD"
                and self._varnode_matches_parameter(right, pointer_param)
                and self._signed_varnode_constant_value(left) == int(byte_offset)
            ):
                return True
        if mnemonic == "PTRADD" and int(getattr(op, "getNumInputs", lambda: 0)() or 0) >= 3:
            base = self._follow_passthrough_varnode(op.getInput(0))
            index = self._signed_varnode_constant_value(self._follow_passthrough_varnode(op.getInput(1)))
            elem = self._varnode_unsigned_constant_value(self._follow_passthrough_varnode(op.getInput(2)))
            if (
                self._varnode_matches_parameter(base, pointer_param)
                and index is not None
                and elem is not None
                and int(index) * int(elem) == int(byte_offset)
            ):
                return True
    return False

def _impl__load_byte_offsets_from_pointer(
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

def _impl__byte_offset_from_pointer(self, address_varnode, pointer_phi) -> Optional[int]:
    def_op = getattr(address_varnode, "getDef", lambda: None)()
    if def_op is not None and getattr(def_op, "getMnemonic", lambda: None)() == "PTRADD":
        if int(getattr(def_op, "getNumInputs", lambda: 0)() or 0) >= 3:
            base = self._follow_passthrough_varnode(def_op.getInput(0))
            if self._same_varnode_value(base, pointer_phi):
                index = self._signed_varnode_constant_value(self._follow_passthrough_varnode(def_op.getInput(1)))
                elem = self._varnode_unsigned_constant_value(self._follow_passthrough_varnode(def_op.getInput(2)))
                if index is not None and elem is not None:
                    return int(index) * int(elem)
    if self._same_varnode_value(address_varnode, pointer_phi):
        return 0
    return None

def _impl__index_phi_has_step(
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

def _impl__byte_offset_from_pointer_like(self, candidate_vn, base_vn) -> Optional[int]:
    candidate_vn = self._follow_passthrough_varnode(candidate_vn)
    offset = self._byte_offset_from_pointer(candidate_vn, base_vn)
    if offset is not None:
        return int(offset)
    def_op = getattr(candidate_vn, "getDef", lambda: None)()
    if def_op is not None:
        mnemonic = getattr(def_op, "getMnemonic", lambda: None)()
        if mnemonic in {"INT_ADD", "PTRSUB"} and int(getattr(def_op, "getNumInputs", lambda: 0)() or 0) >= 2:
            left = self._follow_passthrough_varnode(def_op.getInput(0))
            right = self._follow_passthrough_varnode(def_op.getInput(1))
            if self._same_varnode_value(left, base_vn):
                return self._signed_varnode_constant_value(right)
            if mnemonic == "INT_ADD" and self._same_varnode_value(right, base_vn):
                return self._signed_varnode_constant_value(left)
    if self._same_varnode_value(candidate_vn, base_vn):
        return 0
    return None

def _impl__match_pointer_progression_phi(
    self,
    phi_op,
    pointer_param: dict,
) -> Optional[Dict[str, object]]:
    output = getattr(phi_op, "getOutput", lambda: None)()
    if output is None:
        return None

    input_count = int(getattr(phi_op, "getNumInputs", lambda: 0)() or 0)
    for init_index in range(input_count):
        init_varnode = self._follow_passthrough_varnode(
            self._phi_input_value_varnode(phi_op, init_index)
        )
        init_offset = self._byte_offset_from_parameter_pointer(init_varnode, pointer_param)
        if init_offset is None or int(init_offset) < 0:
            continue
        for back_index in range(input_count):
            if back_index == init_index:
                continue
            back_varnode = self._follow_passthrough_varnode(
                self._phi_input_value_varnode(phi_op, back_index)
            )
            step = self._extract_pointer_step(back_varnode, output)
            if step is None or step <= 0:
                back_varnode = self._phi_incoming_same_storage_definition(
                    phi_op,
                    back_index,
                    output,
                )
                step = self._extract_pointer_step(back_varnode, output)
            if step is None or step <= 0:
                continue
            start_index = 0
            if int(init_offset) > 0 and int(init_offset) % int(step) == 0:
                start_index = int(init_offset) // int(step)
            return {
                "phi_op": phi_op,
                "phi_output": output,
                "stride": int(step),
                "start_offset": int(init_offset),
                "start_index": int(start_index),
                "index_step": 1,
                "index_scale": int(step),
            }
    return None

def _impl__match_index_progression_phi(
    self,
    phi_op,
) -> Optional[Dict[str, object]]:
    output = getattr(phi_op, "getOutput", lambda: None)()
    if output is None:
        return None

    input_count = int(getattr(phi_op, "getNumInputs", lambda: 0)() or 0)
    for init_index in range(input_count):
        init_varnode = self._follow_passthrough_varnode(
            self._phi_input_value_varnode(phi_op, init_index)
        )
        init_value = self._varnode_constant_value(init_varnode)
        if init_value is None:
            continue
        for back_index in range(input_count):
            if back_index == init_index:
                continue
            back_varnode = self._follow_passthrough_varnode(
                self._phi_input_value_varnode(phi_op, back_index)
            )
            step = self._extract_index_step(back_varnode, output)
            if step is not None and step > 0:
                return {
                    "phi_op": phi_op,
                    "phi_output": output,
                    "start": int(init_value),
                    "step": int(step),
                }
    return None

def _impl__match_pointer_progression_phi_by_storage(
    self,
    phi_op,
    pointer_param: dict,
) -> Optional[Dict[str, object]]:
    phi_output = getattr(phi_op, "getOutput", lambda: None)()
    if phi_output is None:
        return None
    input_count = int(getattr(phi_op, "getNumInputs", lambda: 0)() or 0)
    saw_seed = False
    steps: List[int] = []
    for input_index in range(input_count):
        raw_input = None
        try:
            raw_input = phi_op.getInput(input_index)
        except Exception:
            raw_input = None
        resolved_input = self._phi_input_value_varnode(phi_op, input_index)
        if self._byte_offset_from_parameter_pointer(raw_input, pointer_param) == 0 or self._byte_offset_from_parameter_pointer(
            resolved_input,
            pointer_param,
        ) == 0:
            saw_seed = True
            continue
        update_vn = resolved_input
        step = self._extract_pointer_step(update_vn, phi_output)
        if step is None or int(step) <= 0:
            update_vn = self._phi_incoming_same_storage_definition(phi_op, input_index, phi_output)
            step = self._extract_pointer_step(update_vn, phi_output)
        if step is not None and int(step) > 0:
            steps.append(int(step))
    unique_steps = sorted(set(steps))
    if not saw_seed or len(unique_steps) != 1:
        return None
    step = unique_steps[0]
    return {
        "phi_op": phi_op,
        "phi_output": phi_output,
        "stride": int(step),
        "start_offset": 0,
        "start_index": 0,
        "index_step": 1,
        "index_scale": int(step),
    }

def _impl__pointer_phis_for_load_context(
    self,
    pointer_phis: Sequence[Dict[str, object]],
    load_op,
    address_def,
) -> List[Dict[str, object]]:
    if not pointer_phis:
        return []
    context_blocks = {
        self._pcode_block_group_key(getattr(load_op, "getParent", lambda: None)()),
        self._pcode_block_group_key(getattr(address_def, "getParent", lambda: None)()),
    }
    context_blocks.discard(None)

    def rank(pointer_info: Dict[str, object]) -> Tuple[int, str]:
        phi_block = self._pcode_block_group_key(
            getattr(pointer_info.get("phi_op"), "getParent", lambda: None)()
        )
        same_context = phi_block in context_blocks if phi_block is not None else False
        phi_ref = self._make_pcode_op_ref(pointer_info.get("phi_op"))
        return (0 if same_context else 1, repr(phi_ref.stable_key()) if phi_ref is not None else "")

    return sorted(list(pointer_phis), key=rank)

def _impl__index_phis_for_load_context(
    self,
    index_phis: Sequence[Dict[str, object]],
    load_op,
    address_def,
) -> List[Dict[str, object]]:
    if not index_phis:
        return []
    context_blocks = {
        self._pcode_block_group_key(getattr(load_op, "getParent", lambda: None)()),
        self._pcode_block_group_key(getattr(address_def, "getParent", lambda: None)()),
    }
    context_blocks.discard(None)

    def rank(index_info: Dict[str, object]) -> Tuple[int, str]:
        phi_block = self._pcode_block_group_key(
            getattr(index_info.get("phi_op"), "getParent", lambda: None)()
        )
        same_context = phi_block in context_blocks if phi_block is not None else False
        phi_ref = self._make_pcode_op_ref(index_info.get("phi_op"))
        return (0 if same_context else 1, repr(phi_ref.stable_key()) if phi_ref is not None else "")

    return sorted(list(index_phis), key=rank)

def _impl__load_progression_from_pointer_phi(
    self,
    load_op,
    pointer_info: Dict[str, object],
    *,
    load_size: int,
    extra_byte_offset: int = 0,
) -> Optional[Dict[str, object]]:
    """Build a load progression from a pointer-induction PHI.

    The induction PHI describes the cursor value at loop entry.  A load may
    add a constant element offset on top of that cursor, for example a peeled
    prefix loop whose body loads ``base[i + 1]`` while the cursor PHI starts
    at ``base``.  Keep both the byte offset and the logical element index in
    sync so seed compensation can prove that the materialized prefix covers
    the omitted loop iterations.
    """

    index_scale = int(pointer_info.get("index_scale", pointer_info["stride"]) or pointer_info["stride"])
    if index_scale <= 0:
        return None
    extra_byte_offset = int(extra_byte_offset or 0)
    if extra_byte_offset < 0 or extra_byte_offset % index_scale != 0:
        return None
    return {
        "load_op_ref": self._make_pcode_op_ref(load_op),
        "induction_phi_ref": self._make_pcode_op_ref(pointer_info.get("phi_op")),
        "stride": int(pointer_info["stride"]),
        "element_size": max(1, int(load_size or 0)),
        "start_offset": int(pointer_info.get("start_offset", 0) or 0) + extra_byte_offset,
        "start_index": int(pointer_info.get("start_index", 0) or 0) + (extra_byte_offset // index_scale),
        "index_step": int(pointer_info.get("index_step", 1) or 1),
        "index_scale": index_scale,
    }

def _impl__matched_index_progression(
    self,
    varnode,
    index_phis: Sequence[Dict[str, object]],
) -> Optional[Dict[str, object]]:
    varnode = self._follow_passthrough_varnode(varnode)
    for info in index_phis:
        if self._same_varnode_value(varnode, info["phi_output"]):
            return info
    return None

def _impl__induction_info_from_scaled_index(
    self,
    varnode,
    index_phis: Sequence[Dict[str, object]],
) -> Optional[Dict[str, object]]:
    varnode = self._follow_passthrough_varnode(varnode)
    direct = self._matched_index_progression(varnode, index_phis)
    if direct is not None:
        return direct
    def_op = getattr(varnode, "getDef", lambda: None)()
    if def_op is None:
        return None
    mnemonic = getattr(def_op, "getMnemonic", lambda: None)()
    if mnemonic in {"INT_MULT", "INT_LEFT"} and int(getattr(def_op, "getNumInputs", lambda: 0)() or 0) >= 2:
        left = self._induction_info_from_scaled_index(def_op.getInput(0), index_phis)
        if left is not None:
            return left
        return self._induction_info_from_scaled_index(def_op.getInput(1), index_phis)
    return None

def _impl__matches_index_progression(
    self,
    varnode,
    index_phis: Sequence[Dict[str, object]],
) -> bool:
    return self._matched_index_progression(varnode, index_phis) is not None

def _impl__scaled_index_stride(
    self,
    varnode,
    index_phis: Sequence[Dict[str, object]],
) -> Optional[int]:
    scaled = self._scaled_index_stride_and_start(varnode, index_phis)
    if scaled is None:
        return None
    return int(scaled[0])

def _impl__scaled_index_stride_and_start(
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

def _impl__extract_pointer_step(
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

def _impl__extract_index_step(
    self,
    varnode,
    phi_output,
) -> Optional[int]:
    step_expr = self._extract_index_step_expression(varnode, phi_output)
    if step_expr is None:
        return None
    bit_width = int(getattr(step_expr, "size", 0) or getattr(varnode, "getSize", lambda: 0)() or 4) * 8
    return self._signed_constant_value(step_expr, bit_width_hint=bit_width)

def _impl__extract_index_step_expression(
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

def _impl__parameter_index_from_symbol(self, symbol) -> Optional[int]:
    for method_name in ("getCategoryIndex", "getCategory"):
        getter = getattr(symbol, method_name, None)
        if not callable(getter):
            continue
        try:
            index = int(getter())
        except Exception:
            continue
        if index >= 0:
            return index
    return None

def _impl__infer_pointer_parameter_name(self, analysis) -> Optional[str]:
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

def _impl__find_pointer_null_case(
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

def _impl__extract_linear_location_coefficients(
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

def _impl__address_expr_for_location(
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

def _impl__condition_is_pointer_null(self, condition: Condition, pointer_name: str) -> bool:
    return self._match_pointer_equality(condition, pointer_name, expect_zero=True)

def _impl__condition_is_pointer_nonnull(self, condition: Condition, pointer_name: str) -> bool:
    return self._match_pointer_equality(condition, pointer_name, expect_zero=False)

def _impl__pointer_nonnull_condition(self, pointer_name: str, analysis) -> Condition:
    ptr_expr = self._param_expr(analysis, pointer_name)
    return Condition(
        Expression.binary_op(
            "INT_NOTEQUAL",
            ptr_expr,
            Expression.constant(0, size=ptr_expr.size or 8),
        ),
        False,
    )

def _impl__match_pointer_equality(self, condition: Condition, pointer_name: str, expect_zero: bool) -> bool:
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

"""Basic-block / natural-loop discovery, PHI incoming edges and P-code refs."""

from __future__ import annotations

from typing import Any, Dict, Iterable, List, Optional, Sequence, Tuple
import re
from scripts.function_tracer_pcode.core import PcodeBlockRef, PcodeOpRef
from scripts.function_tracer_pcode.analysis.recurrence._shared import (
    CountedLoopGuard,
)


def _impl__phi_input_predecessor_block(self, phi_op, input_index: int):
    if phi_op is None:
        return None
    parent = getattr(phi_op, "getParent", lambda: None)()
    if parent is None:
        return None
    try:
        index = int(input_index)
        in_size = int(getattr(parent, "getInSize", lambda: 0)() or 0)
        if index < 0 or index >= in_size:
            return None
        return parent.getIn(index)
    except Exception:
        return None


def _impl__iter_basic_blocks(self, high_function) -> Iterable:
    try:
        for block in high_function.getBasicBlocks():
            yield block
    except Exception:
        return


def _impl__iter_block_ops(self, block) -> Iterable:
    iterator = getattr(block, "getIterator", lambda: None)()
    if iterator is None:
        return
    while iterator.hasNext():
        yield iterator.next()


def _impl__find_cbranch_op(self, block):
    for op in self._iter_block_ops(block):
        if getattr(op, "getMnemonic", lambda: None)() == "CBRANCH":
            return op
    return None


def _impl__make_pcode_op_ref(self, pcode_op) -> Optional[PcodeOpRef]:
    return PcodeOpRef.from_pcode_op(
        pcode_op,
        binary_id=getattr(self.tracer, "_function_binary_id", None),
        program_uid=getattr(self.tracer, "_function_program_id", None),
        function_entry_space=getattr(self.tracer, "_function_entry_space", None),
        function_entry_offset=getattr(self.tracer, "_function_entry_offset", None),
    )


def _impl__make_pcode_block_ref(self, block) -> Optional[PcodeBlockRef]:
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
        binary_id=(
            getattr(self.tracer, "_function_binary_id", None)
            or getattr(self.tracer, "_function_program_id", None)
        ),
        function_entry_space=getattr(self.tracer, "_function_entry_space", None),
        function_entry_offset=getattr(self.tracer, "_function_entry_offset", None),
    )


def _impl__collect_block_successors(self, block) -> List[object]:
    successors = []
    out_size = int(getattr(block, "getOutSize", lambda: 0)() or 0)
    for index in range(out_size):
        successor = getattr(block, "getOut", lambda _idx: None)(index)
        if successor is not None:
            successors.append(successor)
    return successors


def _impl__collect_block_predecessors(self, block) -> List[object]:
    predecessors = []
    in_size = int(getattr(block, "getInSize", lambda: 0)() or 0)
    for index in range(in_size):
        predecessor = getattr(block, "getIn", lambda _idx: None)(index)
        if predecessor is not None:
            predecessors.append(predecessor)
    return predecessors


def _impl__collect_loop_body_blocks(
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


def _impl__collect_natural_loop_blocks(
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


def _impl__collect_reachable_loop_body_blocks(
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


def _impl__can_reach_block(self, start_block, target_block) -> bool:
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


def _impl__pick_body_and_exit_blocks(self, header_block) -> Optional[Tuple[object, object, bool]]:
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


def _impl__state_loop_phi_indices(self, header_block, phi_op) -> Optional[Tuple[int, Tuple[int, ...]]]:
    input_count = self._safe_pcode_input_count(phi_op)
    if input_count < 2:
        return None
    init_indices: List[int] = []
    backedge_indices: List[int] = []
    in_size = int(getattr(header_block, "getInSize", lambda: 0)() or 0)
    for index in range(input_count):
        predecessor = header_block.getIn(index) if index < in_size else None
        if predecessor is not None and self._can_reach_block(header_block, predecessor):
            backedge_indices.append(index)
        else:
            init_indices.append(index)
    if len(init_indices) != 1 or not backedge_indices:
        return None
    return init_indices[0], tuple(backedge_indices)


def _impl__parse_pcode_site_text(
    self,
    text: str,
) -> Tuple[Optional[int], Optional[int], Optional[int]]:
    remainder = str(text or "").strip()
    seq_time: Optional[int] = None
    seq_order: Optional[int] = None
    while remainder:
        suffix = re.search(r":([to])([+-]?(?:0[xX][0-9a-fA-F]+|[0-9]+))$", remainder)
        if suffix is None:
            break
        value = self._coerce_pcode_site_int(suffix.group(2))
        if suffix.group(1) == "t" and seq_time is None:
            seq_time = value
        elif suffix.group(1) == "o" and seq_order is None:
            seq_order = value
        remainder = remainder[: suffix.start()]
    return self._parse_pcode_address_offset(remainder), seq_time, seq_order


def _impl__coerce_pcode_site_int(self, value: object) -> Optional[int]:
    if value is None or isinstance(value, bool):
        return None
    if isinstance(value, int):
        return int(value)
    if not isinstance(value, str):
        try:
            return int(value)
        except Exception:
            return None
    text = value.strip()
    if not text:
        return None
    try:
        return int(text, 0)
    except Exception:
        try:
            return int(text, 10)
        except Exception:
            return None


def _impl__dedupe_pcode_refs(
    self,
    refs: Sequence[PcodeOpRef],
) -> Tuple[PcodeOpRef, ...]:
    unique: Dict[Tuple[Any, ...], PcodeOpRef] = {}
    for ref in refs or ():
        if ref is None:
            continue
        unique[ref.stable_key()] = ref
    return tuple(sorted(unique.values(), key=lambda ref: repr(ref.stable_key())))


def _impl__phi_input_is_cfg_entry_seed(
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


def _impl__cfg_block_reachable_without_reentering_header(
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


def _impl__program_is_big_endian(self) -> bool:
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


def _impl__phi_input_value_varnode(self, phi_op, input_index: int):
    """Resolve the concrete value feeding a MULTIEQUAL input edge.

    Ghidra can represent a PHI input with the same register/storage varnode
    as the PHI output.  For object-level loop reasoning, the relevant value
    is the definition that reaches the PHI along that specific incoming
    edge.  Use the PHI parent's incoming block and pick the last p-code op
    in that predecessor that defines the same storage object.
    """

    try:
        raw_input = phi_op.getInput(int(input_index))
    except Exception:
        return None
    parent = getattr(phi_op, "getParent", lambda: None)()
    if parent is None:
        return raw_input
    incoming_block = self._phi_incoming_block(parent, int(input_index))
    if incoming_block is None:
        return raw_input

    fallback_output = None
    phi_output = getattr(phi_op, "getOutput", lambda: None)()
    block_ops = list(self._iter_block_ops(incoming_block))
    for candidate_op in reversed(block_ops):
        output = getattr(candidate_op, "getOutput", lambda: None)()
        if output is None:
            continue
        if self._same_storage_varnode(output, raw_input):
            if self._same_high_variable(output, raw_input) or self._same_high_variable(output, phi_output):
                return output
            if fallback_output is None:
                fallback_output = output
    if fallback_output is not None:
        if (
            self._same_high_variable(raw_input, phi_output)
            and not self._same_storage_varnode(raw_input, phi_output)
            and not self._same_high_variable(fallback_output, raw_input)
            and not self._same_high_variable(fallback_output, phi_output)
        ):
            return raw_input
        return fallback_output
    return raw_input


def _impl__phi_incoming_block(self, phi_parent, input_index: int):
    try:
        input_index = int(input_index)
        if input_index < 0 or input_index >= int(phi_parent.getInSize()):
            return None
        incoming_block = phi_parent.getIn(input_index)
    except Exception:
        return None
    if incoming_block is None:
        return None
    try:
        reverse_index = int(phi_parent.getInRevIndex(input_index))
        if reverse_index < 0 or reverse_index >= int(incoming_block.getOutSize()):
            return None
        if not self._same_pcode_block(incoming_block.getOut(reverse_index), phi_parent):
            return None
    except Exception:
        return None
    return incoming_block


def _impl__high_varnode_instances(self, varnode) -> Tuple[object, ...]:
    instances = [varnode]
    high = getattr(varnode, "getHigh", lambda: None)()
    if high is None:
        return tuple(instances)
    representative = getattr(high, "getRepresentative", lambda: None)()
    if representative is not None:
        instances.append(representative)
    high_instances = getattr(high, "getInstances", lambda: None)()
    if high_instances is not None:
        try:
            iterator = iter(high_instances)
        except TypeError:
            iterator = None
        if iterator is not None:
            instances.extend(instance for instance in iterator if instance is not None)
        else:
            try:
                count = int(getattr(high_instances, "length", 0) or 0)
            except Exception:
                count = 0
            for index in range(count):
                try:
                    instance = high_instances[index]
                except Exception:
                    continue
                if instance is not None:
                    instances.append(instance)
    deduped: List[object] = []
    seen = set()
    for instance in instances:
        instance_id = id(instance)
        if instance_id in seen:
            continue
        seen.add(instance_id)
        deduped.append(instance)
    return tuple(deduped)

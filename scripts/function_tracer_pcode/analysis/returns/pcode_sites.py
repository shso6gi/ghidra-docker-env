"""P-code op identity, site description and varnode storage helpers."""

from __future__ import annotations

from typing import Any, Dict, List, Optional, Sequence, Set, Tuple
from scripts.function_tracer_pcode.analysis.returns._shared import (
    AnalysisFailure,
    CallTargetRef,
    Condition,
    ConditionNormalizer,
    ConditionSMTOracle,
    ConditionSimplifier,
    EffectSummary,
    Expression,
    ExpressionType,
    FunctionReturnAnalysis,
    Mapping,
    PcodeOpRef,
    PcodeTracer,
    ReturnInfo,
    StructuralKey,
    _expressions_equivalent,
    _iter_expression_nodes,
    cast,
    expression_key_safe,
)
from scripts.function_tracer_pcode.analysis.returns._api import StructuralRecurrenceSummarizer
from typing import Any, Dict, List, Mapping, Optional, Sequence, Set, Tuple
from scripts.function_tracer_pcode.analysis.returns._shared import (
    Condition,
    Expression,
    ExpressionType,
    FunctionReturnAnalysis,
    StorageInfo,
    _PCODE_OPCODE_BY_MNEMONIC,
    cast,
    eval_constant_raw,
)
from scripts.function_tracer_pcode.analysis.returns._api import PcodeTracer
from typing import Any, Optional, Set, Tuple


def _impl__coerce_optional_int(self, value: object) -> Optional[int]:
    if value is None or isinstance(value, bool):
        return None
    if isinstance(value, int):
        return value
    try:
        return int(cast(Any, value))
    except Exception:
        return None


def _impl__describe_pcode_site(
    self,
    pcode_op,
    fallback_address: Optional[str] = None,
    *,
    identity_prefix: Optional[str] = None,
) -> Dict[str, Optional[object]]:
    address = fallback_address or "unknown"
    pcode_identity: Optional[str] = None
    pcode_order: Optional[int] = None
    pcode_time: Optional[int] = None

    seq = getattr(pcode_op, "getSeqnum", lambda: None)() if pcode_op is not None else None
    if seq is not None:
        try:
            target = seq.getTarget()
            if target is not None:
                address = str(target)
        except Exception:
            target = None
        pcode_order = self._coerce_optional_int(getattr(seq, "getOrder", lambda: None)())
        pcode_time = self._coerce_optional_int(getattr(seq, "getTime", lambda: None)())

        if pcode_time is not None:
            pcode_identity = f"{address}:t{pcode_time}"
        elif pcode_order is not None:
            pcode_identity = f"{address}:o{pcode_order}"
        elif address:
            pcode_identity = address
    elif identity_prefix:
        pcode_identity = f"{identity_prefix}:{address}"

    return {
        "address": address,
        "pcode_identity": pcode_identity,
        "pcode_order": pcode_order,
        "pcode_time": pcode_time,
        "pcode_op_ref": PcodeOpRef.from_pcode_op(
            pcode_op,
            binary_id=self._binary_id,
            program_uid=self._program_identity(),
            function_entry=self._current_function_entry_address(),
        ),
    }


def _impl__pcode_op_identity_key(self, pcode_op) -> Optional[Tuple[Any, ...]]:
    if pcode_op is None:
        return None

    site = self._describe_pcode_site(pcode_op)
    output = getattr(pcode_op, "getOutput", lambda: None)()
    output_key = self._varnode_location_key(output)
    if output_key is None and output is not None:
        output_key = ("id", id(output))

    mnemonic = None
    try:
        mnemonic = str(pcode_op.getMnemonic())
    except Exception:
        mnemonic = None

    identity = (
        site.get("address"),
        site.get("pcode_time"),
        site.get("pcode_order"),
        mnemonic,
        output_key,
    )
    if identity[0] is None and identity[1] is None and identity[2] is None and identity[3] is None:
        return None
    return identity


def _impl__pcode_ops_match(self, lhs, rhs) -> bool:
    if lhs is rhs:
        return True
    lhs_key = self._pcode_op_identity_key(lhs)
    rhs_key = self._pcode_op_identity_key(rhs)
    if lhs_key is None or rhs_key is None:
        return False
    return lhs_key == rhs_key


def _impl__address_like_keys(
    self,
    value,
    *,
    default_space: Optional[str] = None,
) -> Set[Tuple[str, int]]:
    if value is None:
        return set()
    keys: Set[Tuple[str, int]] = set()
    try:
        is_constant = getattr(value, "isConstant", lambda: False)
        if callable(is_constant) and is_constant():
            address = getattr(value, "getAddress", lambda: None)()
            offset = None
            if address is not None:
                offset = getattr(address, "getOffset", lambda: None)()
            if offset is None:
                try:
                    offset = int(value)
                except Exception:
                    offset = None
            if default_space and offset is not None:
                keys.add((str(default_space), int(offset)))
            return keys
    except Exception:
        return set()
    try:
        offset = getattr(value, "getOffset", lambda: None)()
        if offset is not None:
            space_name = self._address_space_name(value)
            if space_name:
                keys.add((space_name, int(offset)))
    except Exception:
        pass
    try:
        address = getattr(value, "getAddress", lambda: None)()
        if address is not None and address is not value:
            keys.update(self._address_like_keys(address, default_space=default_space))
    except Exception:
        pass
    return keys


def _impl__address_space_name(self, address) -> Optional[str]:
    try:
        space = getattr(address, "getAddressSpace", lambda: None)()
        name = getattr(space, "getName", lambda: None)()
        if name is None:
            return None
        return str(name)
    except Exception:
        return None


def _impl__varnodes_same_storage(self, left, right) -> bool:
    if left is None or right is None:
        return False
    try:
        left_addr = left.getAddress()
        right_addr = right.getAddress()
        left_space = left_addr.getAddressSpace().getName()
        right_space = right_addr.getAddressSpace().getName()
        return (
            left_space == right_space
            and int(left_addr.getOffset()) == int(right_addr.getOffset())
            and int(left.getSize()) == int(right.getSize())
        )
    except Exception:
        return False


def _impl__pcode_op_input_def_reaches_phi(
    self,
    op,
    target_phi_key: Tuple[Any, ...],
    *,
    max_depth: int,
) -> bool:
    seen: Set[int] = set()

    def visit_varnode(varnode, depth: int) -> bool:
        if varnode is None or depth > int(max_depth):
            return False
        marker = id(varnode)
        if marker in seen:
            return False
        seen.add(marker)
        try:
            def_op = varnode.getDef()
        except Exception:
            def_op = None
        if def_op is None:
            return False
        if self._pcode_op_stable_key(def_op) == target_phi_key:
            return True
        try:
            input_count = int(def_op.getNumInputs())
        except Exception:
            input_count = 0
        for index in range(input_count):
            try:
                if visit_varnode(def_op.getInput(index), depth + 1):
                    return True
            except Exception:
                continue
        return False

    try:
        input_count = int(op.getNumInputs())
    except Exception:
        input_count = 0
    for index in range(input_count):
        try:
            if visit_varnode(op.getInput(index), 0):
                return True
        except Exception:
            continue
    return False


def _impl__pcode_op_stable_key(self, op) -> Optional[Tuple[Any, ...]]:
    op_ref = PcodeOpRef.from_pcode_op(
        op,
        binary_id=self._binary_id,
        program_uid=self._program_identity(),
        function_entry=self._current_function_entry_address(),
    )
    if op_ref is None:
        return None
    try:
        return op_ref.stable_key()
    except Exception:
        return None


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

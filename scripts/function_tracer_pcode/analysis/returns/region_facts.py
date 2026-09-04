"""Region-level facts: live-in keys, code addresses, non-data operands."""

from __future__ import annotations

from typing import Any, Dict, List, Mapping, Optional, Sequence, Set, Tuple, cast
from scripts.function_tracer_pcode.core.analysis import FunctionReturnAnalysis, ReturnInfo
from scripts.function_tracer_pcode.core.call_target import CallTargetRef
from scripts.function_tracer_pcode.core.expression import Condition, Expression, ExpressionType
from scripts.function_tracer_pcode.core.structural import StructuralKey, expression_key_safe
from scripts.function_tracer_pcode.analysis.returns._shared import (
    AnalysisFailure,
    ConditionNormalizer,
    ConditionSMTOracle,
    ConditionSimplifier,
    EffectSummary,
    PcodeTracer,
    _expressions_equivalent,
    _iter_expression_nodes,
)
from scripts.function_tracer_pcode.analysis.returns._api import StructuralRecurrenceSummarizer
from typing import Any, Dict, List, Mapping, Optional, Sequence, Set, Tuple
from scripts.function_tracer_pcode.analysis.returns._shared import (
    eval_constant_raw,
)
from typing import Any, Mapping, Optional, Sequence, Tuple


def _impl__region_input_is_nondata_operand(mnemonic: str, input_index: int) -> bool:
    control_inputs = {
        "BRANCH": {0},
        "CBRANCH": {0},
        "BRANCHIND": {0},
        "CALL": {0},
        "CALLIND": {0},
        "CALLOTHER": {0},
        "RETURN": {0},
        "LOAD": {0},
        "STORE": {0},
    }
    return int(input_index) in control_inputs.get(str(mnemonic), set())


def _impl__region_address_is_code(self, address) -> bool:
    if address is None or self.program is None:
        return False
    try:
        manager = self.program.getFunctionManager()
        if manager.getFunctionContaining(address) is not None:
            return True
    except Exception:
        pass
    try:
        listing = self.program.getListing()
        if listing.getInstructionContaining(address) is not None:
            return True
    except Exception:
        pass
    try:
        block = self.program.getMemory().getBlock(address)
        if block is not None and bool(block.isExecute()):
            return True
    except Exception:
        pass
    return False


def _impl__region_parameter_index_for_location(
    location_key: Tuple[str, int, int],
    parameters: Sequence[Dict[str, Any]],
) -> Optional[int]:
    space_name, offset, size = location_key
    for ordinal, parameter in enumerate(parameters or ()):
        storage = parameter.get("storage") if isinstance(parameter, Mapping) else None
        if storage is None:
            continue
        storage_space = (
            storage.get("space_name")
            if isinstance(storage, Mapping)
            else getattr(storage, "space_name", None)
        )
        storage_offset = (
            storage.get("offset")
            if isinstance(storage, Mapping)
            else getattr(storage, "offset", None)
        )
        storage_size = (
            storage.get("size")
            if isinstance(storage, Mapping)
            else getattr(storage, "size", None)
        )
        try:
            if (
                str(storage_space) == str(space_name)
                and int(storage_offset) == int(offset)
                and int(storage_size) == int(size)
            ):
                return int(parameter.get("index", ordinal))
        except (TypeError, ValueError):
            continue
    return None


def _impl__region_live_in_key(
    self,
    varnode,
    *,
    mnemonic: str,
    input_index: int,
    parameters: Sequence[Dict[str, Any]],
) -> Tuple[Optional[Tuple[object, ...]], str]:
    if self._region_input_is_nondata_operand(mnemonic, input_index):
        return None, "excluded_nondata_operand"
    try:
        if bool(varnode.isConstant()) or varnode.getDef() is not None:
            return None, "excluded_not_live_in"
        address = varnode.getAddress()
    except Exception:
        return None, "incomplete"
    location_key = self._varnode_location_key(varnode)
    if location_key is None:
        return None, "incomplete"
    space_name = str(location_key[0]).lower()
    if space_name == "ram" and self._region_address_is_code(address):
        return None, "excluded_artifact_code_address"
    parameter_index = self._region_parameter_index_for_location(
        location_key,
        parameters,
    )
    if parameter_index is not None:
        return (
            "parameter_input",
            parameter_index,
            tuple(location_key),
        ), "included"
    if space_name == "register":
        category = "register_input"
    elif space_name in {"stack", "ram"}:
        category = "memory_input"
    else:
        return None, "incomplete"
    return (category, tuple(location_key)), "included"

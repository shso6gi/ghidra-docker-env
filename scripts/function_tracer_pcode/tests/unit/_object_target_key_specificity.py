# -*- coding: utf-8 -*-
"""Object-target key specificity predicates used by the SAT decisiveness fixtures.

Extracted verbatim from the retired ``validation.phase2_equivalence_blocking_unsafety``
gate module so the fixtures no longer depend on it.
"""

from __future__ import annotations

from typing import Any, Iterable, Mapping, Optional, Sequence, Tuple

def _object_target_key_is_specific(value: Any) -> bool:
    if not isinstance(value, tuple) or not value:
        return False
    kind = value[0]
    if kind == "unsupported_call_effect":
        return _unsupported_call_effect_key_is_specific(value)
    if kind == "deferred_call":
        return _deferred_call_key_is_specific(value)
    if kind == "call_argument_evidence":
        return _call_argument_evidence_key_is_specific(value)
    if kind == "call_target_resolution_evidence":
        return _call_target_resolution_evidence_key_is_specific(value)
    return False

def _unsupported_call_effect_key_is_specific(value: Tuple[Any, ...]) -> bool:
    if len(value) < 7:
        return False
    runtime_ref = value[3]
    callsite_storage = value[4]
    effect_ordinal = value[5]
    return all(
        (
            value[1] in {"function1", "function2"},
            _analysis_key_is_specific(value[2]),
            _runtime_ref_is_specific(runtime_ref),
            _callsite_storage_key_is_specific(callsite_storage),
            _unsupported_call_effect_runtime_and_storage_match(runtime_ref, callsite_storage),
            _effect_ordinal_key_is_specific(effect_ordinal),
            value[6] is not None,
        )
    )

def _unsupported_call_effect_runtime_and_storage_match(runtime_ref: Any, callsite_storage: Any) -> bool:
    if (
        not isinstance(runtime_ref, tuple)
        or len(runtime_ref) < 5
        or not isinstance(callsite_storage, tuple)
        or len(callsite_storage) < 4
    ):
        return False
    return all(
        (
            runtime_ref[2] == callsite_storage[1],
            runtime_ref[3] == callsite_storage[2],
            _tagged_payload(runtime_ref[4], "typed_target_expression")
            == _tagged_payload(callsite_storage[3], "target_expression"),
        )
    )

def _runtime_ref_is_specific(value: Any) -> bool:
    if not isinstance(value, tuple) or len(value) < 5 or value[0] != "runtime_ref":
        return False
    return all(
        (
            value[1] == "unsupported_call_effect",
            _tagged_pcode_ref_is_specific(value[2]),
            _tagged_callee_identity_is_specific(value[3]),
            _tagged_typed_target_expression_is_specific(value[4]),
        )
    )

def _callsite_storage_key_is_specific(value: Any) -> bool:
    if not isinstance(value, tuple) or len(value) < 4 or value[0] != "callsite_storage":
        return False
    return all(
        (
            _tagged_pcode_ref_is_specific(value[1]),
            _tagged_callee_identity_is_specific(value[2]),
            _tagged_target_expression_is_specific(value[3]),
        )
    )

def _effect_ordinal_key_is_specific(value: Any) -> bool:
    return (
        isinstance(value, tuple)
        and len(value) == 2
        and value[0] == "effect_ordinal"
        and _nonnegative_int(value[1])
    )

def _tagged_pcode_ref_is_specific(value: Any) -> bool:
    return (
        isinstance(value, tuple)
        and len(value) == 2
        and value[0] == "pcode_op_ref"
        and _pcode_ref_is_specific(value[1])
    )

def _tagged_callee_identity_is_specific(value: Any) -> bool:
    if not isinstance(value, tuple) or len(value) != 2 or value[0] != "callee_identity":
        return False
    callee = value[1]
    if not isinstance(callee, tuple) or len(callee) < 2:
        return False
    if callee[0] == "unknown":
        return (
            len(callee) == 3
            and _binary_id_is_specific(callee[1])
            and _unknown_callee_target_expression_is_specific(callee[2])
        )
    return (
        len(callee) >= 3
        and callee[0] in {"function", "code_address"}
        and _binary_id_is_specific(callee[1])
        and _nonnegative_int_like(callee[2])
    )

def _unknown_callee_target_expression_is_specific(value: Any) -> bool:
    return (
        isinstance(value, tuple)
        and len(value) == 2
        and value[0] == "target_expression"
        and _typed_target_expression_is_specific(value[1])
    )

def _tagged_typed_target_expression_is_specific(value: Any) -> bool:
    return (
        isinstance(value, tuple)
        and len(value) == 2
        and value[0] == "typed_target_expression"
        and _typed_target_expression_is_specific(value[1])
    )

def _tagged_target_expression_is_specific(value: Any) -> bool:
    return (
        isinstance(value, tuple)
        and len(value) == 2
        and value[0] == "target_expression"
        and _typed_target_expression_is_specific(value[1])
    )

def _tagged_payload(value: Any, expected_tag: str) -> Any:
    if not isinstance(value, tuple) or len(value) != 2 or value[0] != expected_tag:
        return None
    return value[1]

def _deferred_call_key_is_specific(value: Tuple[Any, ...]) -> bool:
    if len(value) < 9:
        return False
    return all(
        (
            value[1] in {"function1", "function2", None},
            _analysis_key_is_specific(value[2]),
            _pcode_ref_is_specific(value[4]),
            _typed_target_expression_is_specific(value[6]),
            _argument_keys_are_specific(value[7]),
        )
    )

def _call_argument_evidence_key_is_specific(value: Tuple[Any, ...]) -> bool:
    if len(value) < 8:
        return False
    return all(
        (
            value[1] in {"function1", "function2", None},
            _analysis_key_is_specific(value[2]),
            _pcode_ref_is_specific(value[3]),
            _call_argument_evidence_target_key_is_specific(value[4]),
            _argument_keys_are_specific(value[5]),
            value[6] is not None,
            value[7] is not None,
        )
    )

def _call_argument_evidence_target_key_is_specific(value: Any) -> bool:
    return _function_ref_key_is_specific(value)

def _call_target_resolution_evidence_key_is_specific(value: Tuple[Any, ...]) -> bool:
    if len(value) < 9:
        return False
    runtime_ref = value[3]
    callsite_storage = value[4]
    resolution_kind = value[5]
    path_conditions = value[6]
    target_conditions = value[7]
    effect_ordinal = value[8]
    return all(
        (
            value[1] in {"function1", "function2", None},
            _analysis_key_is_specific(value[2]),
            _call_target_resolution_runtime_ref_is_specific(runtime_ref),
            _callsite_storage_key_is_specific(callsite_storage),
            _unsupported_call_effect_runtime_and_storage_match(runtime_ref, callsite_storage),
            _resolution_kind_key_is_specific(resolution_kind),
            _condition_set_key_is_specific(path_conditions),
            _condition_set_key_is_specific(target_conditions),
            _effect_ordinal_key_is_specific(effect_ordinal),
        )
    )

def _call_target_resolution_runtime_ref_is_specific(value: Any) -> bool:
    if not isinstance(value, tuple) or len(value) < 5 or value[0] != "runtime_ref":
        return False
    return all(
        (
            value[1] == "call_target_resolution",
            _tagged_pcode_ref_is_specific(value[2]),
            _tagged_callee_identity_is_specific(value[3]),
            _tagged_typed_target_expression_is_specific(value[4]),
        )
    )

def _resolution_kind_key_is_specific(value: Any) -> bool:
    return (
        isinstance(value, tuple)
        and len(value) == 2
        and value[0] == "resolution_kind"
        and value[1] in {"pathless_target_resolution", "pcode_target_ref"}
    )

def _condition_set_key_is_specific(value: Any) -> bool:
    return (
        isinstance(value, tuple)
        and len(value) == 2
        and value[0] in {"path_conditions", "target_conditions"}
        and isinstance(value[1], tuple)
        and all(_condition_key_is_specific(item) for item in value[1])
    )

def _condition_key_is_specific(value: Any) -> bool:
    return (
        isinstance(value, tuple)
        and len(value) == 3
        and value[0] == "condition"
        and isinstance(value[1], bool)
        and _condition_payload_is_specific(value[2])
    )

def _condition_payload_is_specific(value: Any) -> bool:
    if value is None:
        return False
    if isinstance(value, (tuple, list)):
        return bool(value) and all(_condition_payload_is_specific(item) for item in value)
    if isinstance(value, Mapping):
        return bool(value) and all(
            _condition_payload_is_specific(key) and _condition_payload_is_specific(item)
            for key, item in value.items()
        )
    return True

def _analysis_key_is_specific(value: Any) -> bool:
    if not isinstance(value, tuple) or not value:
        return False
    if value[0] == "function_ref":
        return _function_ref_key_is_specific(value[1] if len(value) > 1 else None)
    if value[0] == "entry_point":
        return False
    return False

def _function_ref_key_is_specific(value: Any) -> bool:
    if not isinstance(value, tuple) or len(value) < 3:
        return False
    kind, binary_id, address_offset = value[:3]
    if kind not in {"function", "code_address"}:
        return False
    return _binary_id_is_specific(binary_id) and _nonnegative_int_like(address_offset)

def _pcode_ref_is_specific(value: Any) -> bool:
    if not isinstance(value, tuple) or len(value) != 8 or value[0] != "pcode_op":
        return False
    (
        _kind,
        binary_id,
        function_entry,
        seq_target,
        seq_time,
        seq_order,
        opcode,
        local_op_ordinal,
    ) = value
    return all(
        (
            _binary_id_is_specific(binary_id),
            _pcode_address_ref_is_specific(function_entry, "function_entry"),
            _pcode_address_ref_is_specific(seq_target, "seq_target"),
            _nonnegative_int_like(seq_time),
            _nonnegative_int_like(seq_order),
            opcode is not None,
            _nonnegative_int_like(local_op_ordinal),
        )
    )

def _binary_id_is_specific(value: Any) -> bool:
    return isinstance(value, str) and bool(value.strip()) and not value.strip().isdecimal()

def _pcode_address_ref_is_specific(value: Any, expected_kind: str) -> bool:
    if not isinstance(value, tuple) or len(value) != 3 or value[0] != expected_kind:
        return False
    return isinstance(value[1], str) and bool(value[1]) and _nonnegative_int_like(value[2])

def _nonnegative_int_like(value: Any) -> bool:
    if isinstance(value, bool) or value is None:
        return False
    try:
        return int(value) >= 0
    except (TypeError, ValueError):
        return False

def _nonnegative_int(value: Any) -> bool:
    return isinstance(value, int) and not isinstance(value, bool) and value >= 0

def _typed_target_expression_is_specific(value: Any) -> bool:
    return isinstance(value, tuple) and len(value) >= 2 and value[0] == "typed_target_expression"

def _argument_keys_are_specific(value: Any) -> bool:
    if not isinstance(value, tuple):
        return False
    return all(
        isinstance(item, tuple)
        and len(item) >= 3
        and item[0] == "argument"
        and isinstance(item[1], int)
        for item in value
    )

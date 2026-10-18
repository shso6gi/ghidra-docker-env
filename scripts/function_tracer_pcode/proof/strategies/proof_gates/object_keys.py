"""Stable object keys and digests for solver-timeout targets, analyses, return cases and conditions."""

from __future__ import annotations

from typing import Any, List, Mapping, Optional, Sequence, Set, Tuple
import hashlib
import json
from scripts.function_tracer_pcode.core import FunctionReturnAnalysis, object_target_key
from scripts.function_tracer_pcode.proof.strategies.proof_gates._shared import (
    ParallelResult,
)


def _impl__canonicalize_key_sequence(values: Sequence[Any]) -> Tuple[Any, ...]:
    return tuple(sorted(tuple(values or ()), key=repr))


def _impl__canonical_jsonable_for_digest(cls, value: Any) -> Optional[Any]:
    if value is None or isinstance(value, (str, bool, int, float)):
        return value
    if isinstance(value, Mapping):
        result = {}
        for key in sorted(value.keys(), key=lambda item: str(item)):
            if not isinstance(key, str):
                return None
            normalized = cls._canonical_jsonable_for_digest(value[key])
            if normalized is None and value[key] is not None:
                return None
            result[key] = normalized
        return result
    if isinstance(value, (tuple, list)):
        result = []
        for item in value:
            normalized = cls._canonical_jsonable_for_digest(item)
            if normalized is None and item is not None:
                return None
            result.append(normalized)
        return result
    return None


def _impl__canonical_json_digest(cls, value: Any) -> Optional[str]:
    canonical = cls._canonical_jsonable_for_digest(value)
    if canonical is None and value is not None:
        return None
    try:
        payload = json.dumps(
            canonical,
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=True,
        )
    except (TypeError, ValueError):
        return None
    return hashlib.sha256(payload.encode("utf-8")).hexdigest()


def _impl__tag_payload_is_specific(cls, value: Any, tag: str) -> bool:
    item = cls._normalize_nested_tuple(value)
    return (
        isinstance(item, tuple)
        and len(item) == 2
        and item[0] == tag
        and cls._object_leaf_is_specific(item[1])
    )


def _impl__object_leaf_is_specific(cls, value: Any) -> bool:
    normalized = cls._normalize_nested_tuple(value)
    if normalized is None:
        return False
    if isinstance(normalized, str):
        return cls._proof_text_is_specific(normalized)
    if isinstance(normalized, bool):
        return True
    if isinstance(normalized, int):
        return True
    if isinstance(normalized, tuple):
        return bool(normalized) and not cls._proof_target_contains_missing_or_diagnostic(normalized)
    return False


def _impl__positive_int_like(value: Any) -> bool:
    if isinstance(value, bool):
        return False
    try:
        return int(value) > 0
    except (TypeError, ValueError):
        return False


def _impl__nested_contains_tag(cls, value: Any, tag: str) -> bool:
    if isinstance(value, Mapping):
        return any(cls._nested_contains_tag(item, tag) for item in value.values())
    if isinstance(value, tuple):
        if value and value[0] == tag:
            return True
        return any(cls._nested_contains_tag(item, tag) for item in value)
    if isinstance(value, list):
        return any(cls._nested_contains_tag(item, tag) for item in value)
    return False


def _impl__normalization_policy_digest_from_target(cls, object_target_key: Any) -> Optional[str]:
    if isinstance(object_target_key, tuple):
        if (
            len(object_target_key) == 2
            and object_target_key[0] == "normalization_policy_digest"
            and isinstance(object_target_key[1], str)
        ):
            return object_target_key[1]
        for item in object_target_key:
            found = cls._normalization_policy_digest_from_target(item)
            if found is not None:
                return found
    return None


def _impl__normalize_nested_tuple(cls, value: Any):
    if value is None:
        return None
    if isinstance(value, (tuple, list)):
        return tuple(cls._normalize_nested_tuple(item) for item in value)
    return value


def _impl__return_value_extension_ops_object_key(self, return_info: Any) -> Tuple[Any, ...]:
    profiles: List[Tuple[Any, ...]] = []
    seen: Set[Tuple[Any, ...]] = set()
    for ref in (getattr(return_info, "return_value_pcode_op_refs", None) or ()):
        mnemonic = getattr(ref, "mnemonic", None)
        if mnemonic not in {"INT_SEXT", "INT_ZEXT"}:
            continue
        input_size = None
        try:
            input_size = ref.input_size(0)
        except Exception:
            input_size = None
        output_size = getattr(ref, "output_size", None)
        input_bits = int(input_size) * 8 if input_size else None
        output_bits = int(output_size) * 8 if output_size else None
        policy = "sign_extend" if mnemonic == "INT_SEXT" else "zero_extend"
        profile = (
            "extension_op",
            mnemonic,
            ("op_ref", self._stable_key_or_none(ref)),
            ("input_bits", input_bits),
            ("output_bits", output_bits),
            ("policy", policy),
        )
        if profile in seen:
            continue
        seen.add(profile)
        profiles.append(profile)
    return ("return_value_extension_ops", tuple(profiles))


def _impl__solver_timeout_object_target_key(
    self,
    *,
    analysis1: Optional[FunctionReturnAnalysis],
    analysis2: Optional[FunctionReturnAnalysis],
    stage: str,
    query: Optional[str],
    timeout_seconds: Any = None,
    pair_id: Optional[str] = None,
    solver_name: Optional[str] = None,
    parallel_result: Optional[ParallelResult] = None,
) -> Optional[Tuple[Any, ...]]:
    """Stable target for a timed-out solver query.

    The query hash identifies the generated SMT artifact while both side
    records keep the target anchored to Ghidra-derived function, return, and
    guard objects.  Program ids are normalized through binary ids.
    """

    query_text = query or ""
    query_hash = hashlib.sha256(query_text.encode("utf-8")).hexdigest() if query_text else None
    resolved_pair_id = pair_id or self._binary_pair_id_from_analyses(analysis1, analysis2)
    solver_options_key = self._solver_timeout_options_object_key(
        parallel_result=parallel_result,
        timeout_seconds=timeout_seconds,
        fallback_solver_name=solver_name,
    )
    if solver_options_key is None:
        return None
    return (
        "solver_timeout",
        ("pair", resolved_pair_id),
        ("stage", str(stage or "unknown")),
        ("query_hash", query_hash),
        ("timeout_budget_seconds", self._coerce_timeout_seconds(timeout_seconds)),
        solver_options_key,
        self._solver_timeout_side_object_key("left", analysis1),
        self._solver_timeout_side_object_key("right", analysis2),
    )


def _impl__solver_timeout_options_object_key(
    self,
    *,
    parallel_result: Optional[ParallelResult],
    timeout_seconds: Any,
    fallback_solver_name: Optional[str] = None,
) -> Optional[Tuple[Any, ...]]:
    timeout_key = ("timeout_seconds", self._coerce_timeout_seconds(timeout_seconds))
    solver_names = self._solver_names_from_parallel_result(parallel_result)
    if len(solver_names) == 1:
        return ("solver_options", ("solver", solver_names[0]), timeout_key)
    if solver_names:
        return ("solver_options", ("solvers", solver_names), timeout_key)
    if parallel_result is not None:
        return None
    fallback = str(fallback_solver_name).strip() if fallback_solver_name is not None else ""
    if not fallback:
        return None
    return ("solver_options", ("solver", fallback), timeout_key)


def _impl__solver_names_from_parallel_result(parallel_result: Optional[ParallelResult]) -> Tuple[str, ...]:
    results = getattr(parallel_result, "results", None)
    if not results:
        return ()
    names = {
        str(name).strip()
        for result in results
        for name in (getattr(result, "solver_name", None),)
        if name is not None and str(name).strip()
    }
    return tuple(sorted(names))


def _impl__coerce_timeout_seconds(value: Any) -> Optional[int]:
    try:
        seconds = int(value)
    except (TypeError, ValueError):
        return None
    return seconds if seconds >= 0 else None


def _impl__solver_timeout_side_object_key(
    self,
    side_label: str,
    analysis: Optional[FunctionReturnAnalysis],
) -> Tuple[Any, ...]:
    target = (
        "solver_timeout_side",
        side_label,
        self._analysis_entry_key(analysis) if analysis is not None else None,
        self._return_storage_object_key(analysis) if analysis is not None else None,
        self._return_partition_object_key(analysis) if analysis is not None else None,
        self._return_guard_disjunction_object_key(analysis) if analysis is not None else None,
    )
    if analysis is not None:
        return self._artifact_stable_key_for_analysis(target, analysis)
    return target


def _impl__binary_pair_id_from_analyses(
    cls,
    analysis1: Optional[FunctionReturnAnalysis],
    analysis2: Optional[FunctionReturnAnalysis],
) -> Optional[str]:
    left = cls._analysis_binary_id(analysis1)
    right = cls._analysis_binary_id(analysis2)
    if not left or not right:
        return None
    return "_".join(sorted((left, right)))


def _impl__analysis_binary_id(analysis: Optional[FunctionReturnAnalysis]) -> Optional[str]:
    if analysis is None:
        return None
    binary_id = getattr(analysis, "binary_id", None)
    if isinstance(binary_id, str) and binary_id.strip():
        return binary_id.strip()
    return None


def _impl__return_storage_object_key(self, analysis: FunctionReturnAnalysis) -> Tuple[Any, ...]:
    surface = None
    surface_getter = getattr(analysis, "get_comparison_surface", None)
    if callable(surface_getter):
        try:
            surface = surface_getter()
        except (AttributeError, TypeError, ValueError, RecursionError):
            surface = None
    return (
        "return_storage",
        getattr(surface, "kind", None),
        getattr(surface, "explicit_bit_width", None),
        getattr(surface, "use_sign_extension", None),
        getattr(analysis, "return_type", None),
    )


def _impl__return_case_object_key(self, index: int, return_info: Any) -> Tuple[Any, ...]:
    pcode_op_ref = getattr(return_info, "pcode_op_ref", None)
    pcode_key = self._stable_key_or_none(pcode_op_ref)
    value = getattr(return_info, "value", None)
    return (
        "return_case",
        int(index),
        getattr(return_info, "address", None),
        pcode_key,
        getattr(return_info, "pcode_identity", None),
        getattr(return_info, "pcode_order", None),
        self._expression_runtime_object_key(value),
        tuple(
            self._return_condition_object_key(condition)
            for condition in (getattr(return_info, "conditions", None) or ())
        ),
    )


def _impl__return_guard_disjunction_object_key(self, analysis: FunctionReturnAnalysis) -> Tuple[Any, ...]:
    return (
        "guard_disjunction",
        tuple(
            (
                int(index),
                tuple(
                    self._return_condition_object_key(condition)
                    for condition in (getattr(return_info, "conditions", None) or ())
                ),
            )
            for index, return_info in enumerate(getattr(analysis, "returns", ()) or ())
        ),
    )


def _impl__return_condition_object_key(self, condition: Any) -> Tuple[Any, ...]:
    expression = getattr(condition, "expression", None)
    structural_key = None
    key_fn = getattr(condition, "structural_key", None)
    if callable(key_fn):
        try:
            structural_key = key_fn(budget=256)
        except TypeError:
            try:
                structural_key = key_fn()
            except (AttributeError, TypeError, ValueError, RecursionError):
                structural_key = None
        except (AttributeError, ValueError, RecursionError):
            structural_key = None
    return (
        "return_guard",
        bool(getattr(condition, "negated", False)),
        structural_key,
        self._expression_runtime_object_key(expression),
    )


def _impl__conditions_runtime_object_key(self, conditions: Any) -> Tuple[Any, ...]:
    return (
        "conditions",
        tuple(
            self._return_condition_object_key(condition)
            for condition in (conditions or ())
        ),
    )


def _impl__artifact_stable_key_for_analysis(
    cls,
    value: Any,
    analysis: Optional[FunctionReturnAnalysis],
) -> Any:
    binary_id = getattr(analysis, "binary_id", None) if analysis is not None else None
    if binary_id is None:
        return value
    return cls._rewrite_program_identity_keys(value, str(binary_id))


def _impl__rewrite_program_identity_keys(cls, value: Any, binary_id: str) -> Any:
    if isinstance(value, list):
        value = tuple(value)
    if not isinstance(value, tuple):
        return value
    rewritten = tuple(cls._rewrite_program_identity_keys(item, binary_id) for item in value)
    if not rewritten:
        return rewritten
    tag = rewritten[0]
    atom_rewritten = cls._rewrite_atom_encoded_program_identity_key(rewritten, binary_id)
    if atom_rewritten is not None:
        return atom_rewritten
    if tag in {"function", "code_address"} and len(rewritten) >= 3 and cls._program_id_like(rewritten[1]):
        return (tag, binary_id, rewritten[2], *rewritten[3:])
    if tag == "parameter" and len(rewritten) >= 4 and cls._program_id_like(rewritten[1]):
        return (tag, binary_id, rewritten[2], *rewritten[3:])
    if tag == "deferred_call_site" and len(rewritten) == 6 and cls._program_id_like(rewritten[1]):
        caller_entry = rewritten[2]
        caller_key: Any = None
        try:
            caller_key = ("function_ref", ("function", binary_id, int(caller_entry)))
        except (TypeError, ValueError):
            caller_key = ("function_ref", ("function", binary_id, caller_entry))
        return (
            "deferred_call_site",
            caller_key,
            rewritten[3],
            rewritten[4],
            ("argument",),
            rewritten[5],
        )
    return rewritten


def _impl__rewrite_atom_encoded_program_identity_key(
    cls,
    rewritten: Tuple[Any, ...],
    binary_id: str,
) -> Optional[Tuple[Any, ...]]:
    """Normalize program ids inside structural._atom_key encoded tuples.

    object_target_key() preserves runtime_ref.stable_key() through
    _atom_key(), so CallTargetRef / DeferredCallRef identities can appear as
    ("tuple", (("str", "function"), ("int", program_id), ...)) rather than
    raw ("function", program_id, ...).  These ids are Ghidra session-local
    and must not become proof target identity.
    """

    if len(rewritten) != 2 or rewritten[0] != "tuple" or not isinstance(rewritten[1], tuple):
        return None
    items = rewritten[1]
    if not items or not cls._atom_str_is(items[0], None):
        return None
    atom_tag = items[0][1]
    if atom_tag in {"function", "code_address"} and len(items) >= 3 and cls._atom_program_id_like(items[1]):
        return ("tuple", (items[0], ("str", binary_id), items[2], *items[3:]))
    if atom_tag == "parameter" and len(items) >= 4 and cls._atom_program_id_like(items[1]):
        return ("tuple", (items[0], ("str", binary_id), items[2], *items[3:]))
    if atom_tag == "unknown" and len(items) >= 2 and cls._atom_program_id_like(items[1]):
        return ("tuple", (items[0], ("str", binary_id), *items[2:]))
    if atom_tag == "deferred_call_site" and len(items) == 6 and cls._atom_program_id_like(items[1]):
        return ("tuple", (items[0], ("str", binary_id), items[2], items[3], items[4], items[5]))
    return None


def _impl__program_id_like(value: Any) -> bool:
    return isinstance(value, int) and not isinstance(value, bool)


def _impl__atom_program_id_like(cls, value: Any) -> bool:
    return (
        isinstance(value, tuple)
        and len(value) == 2
        and value[0] == "int"
        and cls._program_id_like(value[1])
    )


def _impl__atom_str_is(value: Any, expected: Optional[str]) -> bool:
    return (
        isinstance(value, tuple)
        and len(value) == 2
        and value[0] == "str"
        and (expected is None or value[1] == expected)
    )


def _impl__typed_target_expression_key(cls, expr: Any) -> Optional[Tuple[Any, ...]]:
    if expr is None:
        return None
    return ("typed_target_expression", cls._expression_runtime_object_key(expr))


def _impl__analysis_entry_key(analysis: FunctionReturnAnalysis) -> Tuple[Any, ...]:
    binary_id = getattr(analysis, "binary_id", None)
    function_ref = getattr(analysis, "function_ref", None)
    if binary_id and function_ref is not None:
        entry_offset = getattr(function_ref, "entry_offset", None)
        if entry_offset is None:
            entry_offset = getattr(function_ref, "address_offset", None)
        if entry_offset is not None:
            try:
                return ("function_ref", ("function", str(binary_id), int(entry_offset)))
            except (TypeError, ValueError):
                pass
    stable_key = getattr(function_ref, "stable_key", None)
    if callable(stable_key):
        try:
            key = stable_key()
            if key is not None:
                return ("function_ref", key)
        except (AttributeError, TypeError, ValueError, RecursionError):
            pass
    return ("entry_point", getattr(analysis, "entry_point", None))


def _impl__stable_key_or_none(value: Any):
    stable_key = getattr(value, "stable_key", None)
    if callable(stable_key):
        try:
            return stable_key()
        except (AttributeError, TypeError, ValueError, RecursionError):
            return None
    return None


def _impl__expression_runtime_object_key(cls, expr: Any) -> Tuple[Any, ...]:
    return object_target_key(expr)

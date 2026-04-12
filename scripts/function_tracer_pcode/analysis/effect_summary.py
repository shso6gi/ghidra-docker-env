# -*- coding: utf-8 -*-
"""Simple parameter-derived memory effect summaries."""

from __future__ import annotations

import binascii
from dataclasses import dataclass
import re
from typing import Callable, Dict, FrozenSet, Iterable, List, Optional, Sequence, Set, Tuple

from ..model import Condition, Expression, ExpressionType, StorageInfo
from .condition import ConditionSimplifier
from .condition.normalizer import ConditionNormalizer
from .memory_resolver import concretize_readonly_loads, _extract_address_suffix


@dataclass(frozen=True)
class CanonicalLocation:
    base_param: str
    offset: int
    size: int
    steps: Tuple["LocationStep", ...] = ()


@dataclass(frozen=True)
class LocationStep:
    kind: str
    value: int

    def __post_init__(self) -> None:
        if self.kind not in {"offset", "deref"}:
            raise ValueError(f"Unsupported location step kind: {self.kind}")


@dataclass
class StoreEffect:
    location: CanonicalLocation
    value: Expression
    conditions: List[Condition]
    order_key: int


@dataclass
class EffectSummary:
    parameter_names: List[str]
    effects: List[StoreEffect]
    synthetic_expr: Optional[Expression] = None
    has_unsupported_call: bool = False


_SYNTHETIC_LOCATION_BASE_PREFIX = "__locbase__"
_SYNTHETIC_LOCATION_READ_PREFIX = "__locread__"
_STACK_FRAME_LOCATION_BASE = f"{_SYNTHETIC_LOCATION_BASE_PREFIX}stackframe"


def _encode_signed_token(value: int) -> str:
    try:
        numeric = int(value)
    except Exception:
        numeric = 0
    if numeric < 0:
        return f"n{abs(numeric)}"
    return f"p{numeric}"


def _decode_signed_token(token: str) -> Optional[int]:
    if not token:
        return None
    prefix = token[0]
    digits = token[1:]
    if prefix not in {"n", "p"} or not digits.isdigit():
        return None
    value = int(digits)
    return -value if prefix == "n" else value


def _collect_named_parameter_names(parameters: Sequence[Dict]) -> List[str]:
    return [
        str(name)
        for param in parameters
        for name in [param.get("name")]
        if isinstance(name, str) and name
    ]


def _all_non_none_expressions(
    operands: Sequence[Optional[Expression]],
) -> Optional[List[Expression]]:
    normalized: List[Expression] = []
    for operand in operands:
        if operand is None:
            return None
        normalized.append(operand)
    return normalized


def _clone_expression_with_operands(
    expr: Expression,
    operands: Sequence[Expression],
) -> Expression:
    return Expression(
        expr_type=expr.expr_type,
        value=expr.value,
        operator=expr.operator,
        operands=list(operands),
        size=expr.size,
        name=expr.name,
        data_type=expr.data_type,
        storage_info=expr.storage_info,
        read_order_key=expr.read_order_key,
    )


def _rebuild_expression_from_optional_operands(
    expr: Expression,
    rewritten_operands: Sequence[Optional[Expression]],
    *,
    fallback: Optional[Expression] = None,
) -> Optional[Expression]:
    if all(new is old for new, old in zip(rewritten_operands, expr.operands)):
        return expr
    new_operands = _all_non_none_expressions(rewritten_operands)
    if new_operands is None:
        return fallback
    return _clone_expression_with_operands(expr, new_operands)


def _synthetic_storage_base_name(storage: Optional[StorageInfo]) -> Optional[str]:
    storage = _coerce_storage_info(storage)
    if storage is None or storage.is_register:
        return None
    space_name = re.sub(r"[^0-9A-Za-z_]", "_", str(storage.space_name or "mem"))
    return (
        f"{_SYNTHETIC_LOCATION_BASE_PREFIX}"
        f"{space_name}_{_encode_signed_token(storage.offset)}_{max(1, int(storage.size or 0))}"
    )


def _synthetic_location_read_name(location: CanonicalLocation) -> str:
    payload = _serialize_location(location)
    encoded = binascii.hexlify(payload.encode("utf-8")).decode("ascii")
    return f"{_SYNTHETIC_LOCATION_READ_PREFIX}{encoded}"


def _parse_synthetic_location_read_name(name: Optional[str]) -> Optional[CanonicalLocation]:
    if not name or not name.startswith(_SYNTHETIC_LOCATION_READ_PREFIX):
        return None
    try:
        payload = binascii.unhexlify(
            name[len(_SYNTHETIC_LOCATION_READ_PREFIX):].encode("ascii")
        ).decode("utf-8")
    except Exception:
        payload = None

    if payload:
        parsed = _deserialize_location(payload)
        if parsed is not None:
            return parsed

    payload = name[len(_SYNTHETIC_LOCATION_READ_PREFIX):]
    parts = payload.rsplit("_", 2)
    if len(parts) != 3:
        return None

    encoded_base, offset_token, size_token = parts
    try:
        base_name = binascii.unhexlify(encoded_base.encode("ascii")).decode("utf-8")
        offset = _decode_signed_token(offset_token)
        size = int(size_token)
    except Exception:
        return None
    if offset is None:
        return None
    return CanonicalLocation(base_param=base_name, offset=offset, size=max(1, size))


def _serialize_location(location: CanonicalLocation) -> str:
    normalized = _normalize_canonical_location(location)
    step_tokens = []
    for step in normalized.steps:
        prefix = "o" if step.kind == "offset" else "d"
        token = _encode_signed_token(step.value) if step.kind == "offset" else str(int(step.value))
        step_tokens.append(f"{prefix}:{token}")
    return "|".join(
        [
            normalized.base_param,
            ";".join(step_tokens),
            _encode_signed_token(normalized.offset),
            str(max(1, int(normalized.size or 0))),
        ]
    )


def _deserialize_location(payload: str) -> Optional[CanonicalLocation]:
    parts = payload.split("|")
    if len(parts) != 4:
        return None

    base_name, steps_part, offset_token, size_token = parts
    offset = _decode_signed_token(offset_token)
    if offset is None:
        return None

    try:
        size = max(1, int(size_token))
    except Exception:
        return None

    steps: List[LocationStep] = []
    if steps_part:
        for token in steps_part.split(";"):
            if ":" not in token:
                return None
            kind_token, value_token = token.split(":", 1)
            if kind_token == "o":
                value = _decode_signed_token(value_token)
                if value is None:
                    return None
                steps.append(LocationStep("offset", value))
                continue
            if kind_token == "d":
                try:
                    value = int(value_token)
                except Exception:
                    return None
                steps.append(LocationStep("deref", value))
                continue
            return None

    return _normalize_canonical_location(
        CanonicalLocation(base_param=base_name, offset=offset, size=size, steps=tuple(steps))
    )


def expression_contains_synthetic_location_reads(expr: Optional[Expression]) -> bool:
    if expr is None:
        return False
    if _parse_synthetic_location_read_name(getattr(expr, "name", None)) is not None:
        return True
    if expr.expr_type == ExpressionType.PHI and expr.value:
        for cond, value in expr.value:
            if cond is not None and expression_contains_synthetic_location_reads(cond.expression):
                return True
            if expression_contains_synthetic_location_reads(value):
                return True
        return False
    for operand in getattr(expr, "operands", []) or []:
        if expression_contains_synthetic_location_reads(operand):
            return True
    return False


def expression_contains_complex_location_reads(
    expr: Optional[Expression],
    parameters: Sequence[Dict],
) -> bool:
    if expr is None:
        return False
    synthetic_location = _parse_synthetic_location_read_name(getattr(expr, "name", None))
    if synthetic_location is not None:
        return True
    if expr.expr_type == ExpressionType.MEMORY and expr.operands:
        location = canonicalize_location(expr.operands[0], parameters, size=expr.size)
        if location is not None and getattr(location, "steps", ()):
            return True
    if expr.expr_type == ExpressionType.PHI and expr.value:
        for cond, value in expr.value:
            if cond is not None and expression_contains_complex_location_reads(cond.expression, parameters):
                return True
            if expression_contains_complex_location_reads(value, parameters):
                return True
        return False
    for operand in getattr(expr, "operands", []) or []:
        if expression_contains_complex_location_reads(operand, parameters):
            return True
    return False


def summarize_store_effects(
    block_infos: Iterable,
    tracer,
    condition_tracker,
    parameters: Sequence[Dict],
    direct_call_summary: Optional[Callable[[str, Sequence[Expression]], Optional["EffectSummary"]]] = None,
    direct_call_expander: Optional[Callable[[str, Sequence[Expression]], Optional[Sequence[object]]]] = None,
    resolve_callee_parameters: Optional[Callable[[str], Sequence[Dict]]] = None,
    debug: bool = False,
) -> EffectSummary:
    parameter_names = _collect_named_parameter_names(parameters)
    effects: List[StoreEffect] = []
    has_unsupported_call = False

    for block_info in block_infos:
        path_sets = condition_tracker.get_all_valid_paths_to_block(block_info)
        if not path_sets:
            path_sets = [[]]

        for op in block_info.pcode_ops:
            mnemonic = op.getMnemonic()

            if mnemonic == "STORE" and op.getNumInputs() >= 3:
                addr_expr = tracer.trace_varnode(op.getInput(1), use_cache=False)
                location = canonicalize_param_location(addr_expr, parameters, size=op.getInput(2).getSize())
                if location is None:
                    continue
                value_effects = _resolve_store_value_effects(
                    op,
                    tracer,
                    parameters,
                    direct_call_expander=direct_call_expander,
                    resolve_callee_parameters=resolve_callee_parameters,
                )
                for path_conditions in path_sets:
                    for value_expr, value_conditions in value_effects:
                        simplified = ConditionSimplifier.simplify_conditions(
                            list(path_conditions) + list(value_conditions)
                        )
                        effects.append(
                            StoreEffect(
                                location=location,
                                value=value_expr,
                                conditions=simplified,
                                order_key=_get_order_key(op),
                            )
                        )
                continue

            if mnemonic not in {"CALL", "CALLIND"} or direct_call_summary is None or op.getNumInputs() < 1:
                continue

            target_name = _resolve_call_target_name(tracer, op)
            if not target_name:
                has_unsupported_call = True
                continue
            explicit_args = [
                _normalize_call_argument_expression(
                    _resolve_call_argument_expression(op.getInput(i), tracer, parameters),
                    i - 1,
                    parameters,
                )
                for i in range(1, op.getNumInputs())
            ]
            callee_parameters = list(resolve_callee_parameters(target_name) or []) if resolve_callee_parameters else []
            args = _recover_call_argument_expressions(
                op,
                tracer,
                parameters,
                callee_parameters,
                explicit_args,
            )
            if debug:
                explicit_dump = ", ".join(arg.to_string() for arg in explicit_args)
                recovered_dump = ", ".join(arg.to_string() for arg in args)
                print(
                    "[EffectSummary] call arguments: "
                    f"target={target_name} explicit=[{explicit_dump}] recovered=[{recovered_dump}]"
                )
            callee_summary = direct_call_summary(target_name, args)
            if callee_summary is None:
                has_unsupported_call = True
                continue
            if not callee_summary.effects:
                if callee_summary.has_unsupported_call:
                    has_unsupported_call = True
                elif debug:
                    print(
                        "[EffectSummary] effect-free callee summary: "
                        f"target={target_name}"
                    )
                continue
            if not is_call_effect_summary_allowed(callee_summary):
                has_unsupported_call = True
                continue

            for effect in callee_summary.effects:
                substitution_args = _choose_effect_substitution_args(
                    effect.location,
                    callee_summary.parameter_names,
                    args,
                    parameters,
                )
                substituted_location = substitute_location(
                    effect.location,
                    callee_summary.parameter_names,
                    substitution_args,
                    parameters,
                )
                if substituted_location is None:
                    if debug:
                        arg_dump = ", ".join(arg.to_string() for arg in substitution_args)
                        print(
                            "[EffectSummary] skip substituted effect: "
                            f"callee_loc={effect.location} args=[{arg_dump}]"
                        )
                    continue
                substitutions = dict(zip(callee_summary.parameter_names, substitution_args))
                substituted_value = substitute_expression(effect.value, substitutions, parameters)
                substituted_conditions = [
                    substitute_condition(cond, substitutions, parameters)
                    for cond in effect.conditions
                ]
                if debug:
                    cond_dump = ", ".join(cond.to_string() for cond in substituted_conditions)
                    print(
                        "[EffectSummary] substituted effect: "
                        f"callee_loc={effect.location} caller_loc={substituted_location} "
                        f"value={substituted_value.to_string()} conditions=[{cond_dump}]"
                    )
                for path_conditions in path_sets:
                    merged_conditions = ConditionSimplifier.simplify_conditions(
                        list(path_conditions) + substituted_conditions
                    )
                    effects.append(
                        StoreEffect(
                            location=substituted_location,
                            value=substituted_value,
                            conditions=merged_conditions,
                            order_key=_get_order_key(op),
                        )
                    )

    synthetic_expr = build_void_effect_summary_expr(effects)
    if debug:
        print(
            f"[EffectSummary] collected {len(effects)} effects "
            f"for params={parameter_names}"
        )
    return EffectSummary(
        parameter_names=parameter_names,
        effects=effects,
        synthetic_expr=synthetic_expr,
        has_unsupported_call=has_unsupported_call,
    )


def _resolve_store_value_effects(
    store_op,
    tracer,
    parameters: Sequence[Dict],
    *,
    direct_call_expander: Optional[Callable[[str, Sequence[Expression]], Optional[Sequence[object]]]] = None,
    resolve_callee_parameters: Optional[Callable[[str], Sequence[Dict]]] = None,
) -> List[Tuple[Expression, List[Condition]]]:
    value_varnode = store_op.getInput(2)
    resolved = _resolve_direct_call_value_effects(
        value_varnode,
        tracer,
        parameters,
        direct_call_expander=direct_call_expander,
        resolve_callee_parameters=resolve_callee_parameters,
    )
    if resolved:
        return resolved
    return [(tracer.trace_varnode(value_varnode, use_cache=False), [])]


def _resolve_direct_call_value_effects(
    value_varnode,
    tracer,
    parameters: Sequence[Dict],
    *,
    direct_call_expander: Optional[Callable[[str, Sequence[Expression]], Optional[Sequence[object]]]] = None,
    resolve_callee_parameters: Optional[Callable[[str], Sequence[Dict]]] = None,
) -> List[Tuple[Expression, List[Condition]]]:
    if direct_call_expander is None or value_varnode is None:
        return []

    try:
        def_op = value_varnode.getDef()
    except Exception:
        def_op = None
    if def_op is None or def_op.getMnemonic() not in {"CALL", "CALLIND"}:
        return []

    target_name = _resolve_call_target_name(tracer, def_op)
    if not target_name:
        return []

    explicit_args = [
        _normalize_call_argument_expression(
            _resolve_call_argument_expression(def_op.getInput(i), tracer, parameters),
            i - 1,
            parameters,
        )
        for i in range(1, def_op.getNumInputs())
    ]
    callee_parameters = (
        list(resolve_callee_parameters(target_name) or [])
        if resolve_callee_parameters is not None
        else []
    )
    args = _recover_call_argument_expressions(
        def_op,
        tracer,
        parameters,
        callee_parameters,
        explicit_args,
    )

    expanded = direct_call_expander(target_name, args)
    if not expanded:
        return []

    resolved: List[Tuple[Expression, List[Condition]]] = []
    for item in expanded:
        value = getattr(item, "value", None)
        conditions = getattr(item, "conditions", None)
        if not isinstance(value, Expression):
            continue
        if not _expression_is_call_scope_safe(value):
            continue
        normalized_conditions = ConditionSimplifier.simplify_conditions(list(conditions or []))
        if ConditionSimplifier.is_contradiction(normalized_conditions):
            continue
        resolved.append((value, normalized_conditions))
    return resolved


def _recover_call_argument_expressions(
    call_op,
    tracer,
    caller_parameters: Sequence[Dict],
    callee_parameters: Sequence[Dict],
    explicit_args: Sequence[Expression],
) -> List[Expression]:
    if not callee_parameters:
        return list(explicit_args)

    explicit_args = _select_aligned_explicit_call_arguments(
        call_op,
        tracer,
        caller_parameters,
        callee_parameters,
        explicit_args,
    )
    recovered_args: List[Expression] = []
    for index, callee_param in enumerate(callee_parameters):
        explicit = explicit_args[index] if index < len(explicit_args) else None
        if explicit is not None and _should_preserve_explicit_indirect_target_argument(explicit, callee_param):
            recovered_args.append(explicit)
            continue
        if explicit is not None and _expression_maps_to_parameter(explicit, caller_parameters):
            recovered_args.append(explicit)
            continue
        explicit_size = (
            explicit.size
            if explicit is not None and getattr(explicit, "size", 0)
            else callee_param.get("size")
        )
        if explicit is not None and _should_prefer_explicit_call_argument(
            explicit,
            caller_parameters,
            size=explicit_size,
        ):
            recovered_args.append(explicit)
            continue

        recovered = _recover_call_argument_from_storage(
            call_op,
            tracer,
            caller_parameters,
            callee_param,
        )
        if recovered is None:
            recovered = _parameter_expression_from_matching_storage(
                callee_param,
                caller_parameters,
                size=(explicit.size if explicit is not None else None),
            )
        if recovered is None and index < len(caller_parameters):
            recovered = _parameter_expression_from_descriptor(
                caller_parameters[index],
                size=(explicit.size if explicit is not None else callee_param.get("size")),
            )

        if recovered is not None:
            recovered_args.append(
                _normalize_call_argument_expression(recovered, index, caller_parameters)
            )
        elif explicit is not None:
            recovered_args.append(explicit)
    return recovered_args


def _select_aligned_explicit_call_arguments(
    call_op,
    tracer,
    caller_parameters: Sequence[Dict],
    callee_parameters: Sequence[Dict],
    explicit_args: Sequence[Expression],
) -> List[Expression]:
    explicit = list(explicit_args)
    if len(explicit) <= len(callee_parameters):
        return explicit

    preferred_args = [
        _recover_preferred_call_argument_expression(
            call_op,
            tracer,
            caller_parameters,
            callee_param,
            index,
        )
        for index, callee_param in enumerate(callee_parameters)
    ]

    total_explicit = len(explicit)
    total_params = len(callee_parameters)
    best_scores: Dict[Tuple[int, int], int] = {}
    best_paths: Dict[Tuple[int, int], Tuple[int, ...]] = {}

    def solve(explicit_index: int, param_index: int) -> int:
        key = (explicit_index, param_index)
        if key in best_scores:
            return best_scores[key]

        remaining_explicit = total_explicit - explicit_index
        remaining_params = total_params - param_index
        if remaining_explicit < remaining_params:
            best_scores[key] = -10**9
            best_paths[key] = ()
            return best_scores[key]
        if param_index >= total_params:
            skip_score = -2 * remaining_explicit
            best_scores[key] = skip_score
            best_paths[key] = ()
            return skip_score
        if explicit_index >= total_explicit:
            best_scores[key] = -10**9
            best_paths[key] = ()
            return best_scores[key]

        skip_penalty = -1 if param_index == 0 else -6
        skip_score = skip_penalty + solve(explicit_index + 1, param_index)
        take_tail_score = solve(explicit_index + 1, param_index + 1)
        if take_tail_score <= -10**8:
            take_score = take_tail_score
        else:
            take_score = _score_call_argument_alignment(
                explicit[explicit_index],
                caller_parameters,
                callee_parameters[param_index],
                preferred_args[param_index],
                explicit_index,
                param_index,
                total_explicit,
                total_params,
            ) + take_tail_score

        if take_score > skip_score:
            best_scores[key] = take_score
            best_paths[key] = (explicit_index,) + best_paths.get(
                (explicit_index + 1, param_index + 1),
                (),
            )
        else:
            best_scores[key] = skip_score
            best_paths[key] = best_paths.get((explicit_index + 1, param_index), ())
        return best_scores[key]

    solve(0, 0)
    selected_indices = list(best_paths.get((0, 0), ()))
    if len(selected_indices) != total_params:
        return explicit[:total_params]
    return [explicit[index] for index in selected_indices]


def _recover_preferred_call_argument_expression(
    call_op,
    tracer,
    caller_parameters: Sequence[Dict],
    callee_param: Dict,
    index: int,
) -> Optional[Expression]:
    preferred = _recover_call_argument_from_storage(
        call_op,
        tracer,
        caller_parameters,
        callee_param,
    )
    if preferred is None:
        preferred = _parameter_expression_from_matching_storage(
            callee_param,
            caller_parameters,
            size=callee_param.get("size"),
        )
    if preferred is None and index < len(caller_parameters):
        caller_param = caller_parameters[index]
        caller_storage = _coerce_storage_info(caller_param.get("storage"))
        callee_storage = _coerce_storage_info(callee_param.get("storage"))
        if (
            caller_storage is not None
            and callee_storage is not None
            and _storage_infos_match(caller_storage, callee_storage)
        ):
            preferred = _parameter_expression_from_descriptor(
                caller_param,
                size=callee_param.get("size"),
            )
    if preferred is None:
        return None
    return _normalize_call_argument_expression(preferred, index, caller_parameters)


def _score_call_argument_alignment(
    expr: Optional[Expression],
    caller_parameters: Sequence[Dict],
    callee_param: Optional[Dict],
    preferred: Optional[Expression],
    explicit_index: int,
    param_index: int,
    total_explicit: int,
    total_params: int,
) -> int:
    if expr is None:
        return -10**6

    score = _call_argument_semantic_rank(expr, caller_parameters, callee_param) * 5
    score += _call_argument_position_bias(
        explicit_index,
        param_index,
        total_explicit,
        total_params,
    )
    expr_name = _resolve_parameter_name(expr, caller_parameters)
    preferred_name = _resolve_parameter_name(preferred, caller_parameters) if preferred is not None else None

    if preferred is not None:
        if _expressions_equivalent(expr, preferred):
            score += 100
        elif expr_name is not None and expr_name == preferred_name:
            score += 85
        else:
            expr_size = max(1, int(expr.size or (callee_param or {}).get("size") or 8))
            preferred_size = max(1, int(preferred.size or (callee_param or {}).get("size") or 8))
            expr_location = canonicalize_location(expr, caller_parameters, size=expr_size)
            preferred_location = canonicalize_location(preferred, caller_parameters, size=preferred_size)
            if expr_location is not None and expr_location == preferred_location:
                score += 70

    if expr_name is not None:
        score += 15
        caller_param = next(
            (param for param in caller_parameters if param.get("name") == expr_name),
            None,
        )
        if caller_param is not None and callee_param is not None:
            caller_storage = _coerce_storage_info(caller_param.get("storage"))
            callee_storage = _coerce_storage_info(callee_param.get("storage"))
            if (
                caller_storage is not None
                and callee_storage is not None
                and _storage_infos_match(caller_storage, callee_storage)
            ):
                score += 45
            try:
                if int(caller_param.get("index", -1)) == int(callee_param.get("index", -2)):
                    score += 10
            except Exception:
                pass
    elif expr.expr_type == ExpressionType.CONSTANT:
        if _parameter_descriptor_looks_pointer(callee_param):
            try:
                score += 10 if int(expr.value) == 0 else -5
            except Exception:
                score += 0
        else:
            score += 12
    elif expr.expr_type == ExpressionType.PHI:
        score += 16
    elif expr.expr_type == ExpressionType.CALL:
        score += 12
    elif expr.expr_type in {ExpressionType.BINARY_OP, ExpressionType.UNARY_OP, ExpressionType.MEMORY}:
        score += 5

    try:
        callee_size = int((callee_param or {}).get("size") or 0)
    except Exception:
        callee_size = 0
    try:
        expr_size = int(expr.size or 0)
    except Exception:
        expr_size = 0
    if callee_size > 0 and expr_size == callee_size:
        score += 2

    return score


def _call_argument_position_bias(
    explicit_index: int,
    param_index: int,
    total_explicit: int,
    total_params: int,
) -> int:
    extra_prefix = total_explicit - total_params
    if extra_prefix <= 0:
        return 0

    expected_index = extra_prefix + param_index
    delta = explicit_index - expected_index
    if delta == 0:
        return 90
    if delta < 0:
        return -35 * abs(delta)
    return -18 * delta


def _should_preserve_explicit_indirect_target_argument(
    expr: Optional[Expression],
    callee_param: Optional[Dict],
) -> bool:
    if expr is None or not _parameter_descriptor_looks_pointer(callee_param):
        return False
    if expr.expr_type == ExpressionType.PHI:
        return True
    return bool(_enumerate_constant_expression_branches(expr))


def _should_prefer_explicit_call_argument(
    expr: Optional[Expression],
    caller_parameters: Sequence[Dict],
    size: Optional[int] = None,
) -> bool:
    if expr is None:
        return False
    if expr.expr_type == ExpressionType.PHI:
        return True
    if expr.expr_type in {ExpressionType.CONSTANT, ExpressionType.MEMORY, ExpressionType.CALL}:
        return True
    if expr.expr_type in {ExpressionType.BINARY_OP, ExpressionType.UNARY_OP}:
        return True

    try:
        effective_size = int(size or expr.size or 0)
    except Exception:
        effective_size = 0
    if effective_size <= 0:
        effective_size = 8
    return canonicalize_location(expr, caller_parameters, size=effective_size) is not None


def _parameter_descriptor_looks_pointer(param: Optional[Dict]) -> bool:
    if not param:
        return False
    data_type = str(param.get("data_type") or param.get("type") or "")
    normalized = data_type.replace(" ", "").lower()
    return "*" in normalized or normalized.endswith("ptr")


def _call_argument_semantic_rank(
    expr: Optional[Expression],
    caller_parameters: Sequence[Dict],
    callee_param: Optional[Dict],
) -> int:
    if expr is None:
        return -1

    callee_expects_pointer = _parameter_descriptor_looks_pointer(callee_param)
    try:
        effective_size = int((callee_param or {}).get("size") or expr.size or 0)
    except Exception:
        effective_size = 0
    if effective_size <= 0:
        effective_size = max(1, int(expr.size or 8))

    caller_param_name = _resolve_parameter_name(expr, caller_parameters)
    caller_param = next(
        (param for param in caller_parameters if param.get("name") == caller_param_name),
        None,
    )
    caller_param_is_pointer = _parameter_descriptor_looks_pointer(caller_param)

    if expr.expr_type == ExpressionType.CONSTANT and int(getattr(expr, "value", 1)) == 0:
        return 3 if callee_expects_pointer else 1

    location = canonicalize_location(expr, caller_parameters, size=effective_size)
    if callee_expects_pointer:
        if location is not None:
            if location.base_param == _STACK_FRAME_LOCATION_BASE:
                return 8
            if location.base_param.startswith(_SYNTHETIC_LOCATION_BASE_PREFIX):
                return 7
            if caller_param_name is not None:
                return 6 if caller_param_is_pointer else 1
            return 5
        if caller_param_name is not None:
            return 6 if caller_param_is_pointer else 1
        return 0

    return 0


def _resolve_call_target_name(tracer, op) -> Optional[str]:
    if op.getNumInputs() < 1:
        return None

    target_varnode = op.getInput(0)
    mnemonic = op.getMnemonic()
    if mnemonic not in {"CALL", "CALLIND"}:
        return None

    target_name = tracer._get_function_name(target_varnode)
    if target_name != "UNKNOWN_FUNC" and not _is_synthetic_function_name(target_name):
        return target_name

    traced_target = tracer.trace_varnode(target_varnode, use_cache=False)
    if traced_target.expr_type != ExpressionType.CONSTANT or not isinstance(traced_target.value, int):
        return target_name if target_name != "UNKNOWN_FUNC" else None

    resolved = _lookup_function_name_by_value(tracer, traced_target.value)
    if resolved is not None:
        return resolved
    return target_name if target_name != "UNKNOWN_FUNC" else None


def resolve_call_targets(
    tracer,
    op,
    conditions: Optional[Sequence[Condition]] = None,
    parameters: Optional[Sequence[Dict]] = None,
    read_memory_value: Optional[Callable[[int, int], Optional[int]]] = None,
    image_base: Optional[int] = None,
    debug: bool = False,
) -> List[Tuple[str, List[Condition]]]:
    """Resolve CALL/CALLIND targets into finite (callee_name, branch_conditions) pairs."""
    direct_name = _resolve_call_target_name(tracer, op)
    if direct_name and direct_name != "UNKNOWN_FUNC" and not _is_synthetic_function_name(direct_name):
        return [(direct_name, [])]

    if op is None or op.getNumInputs() < 1:
        return []

    target_varnode = op.getInput(0)
    target_expr = tracer.trace_varnode(target_varnode, use_cache=False)
    if debug:
        print(f"[CallTargetResolver] traced target expr: {target_expr.to_string()}")

    if read_memory_value is not None:
        try:
            target_expr = concretize_readonly_loads(
                target_expr,
                list(conditions or []),
                list(parameters or []),
                read_memory_value,
                image_base=image_base,
                debug=debug,
            )
        except Exception:
            if debug:
                print("[CallTargetResolver] readonly target concretization failed")
    if debug:
        print(f"[CallTargetResolver] rewritten target expr: {target_expr.to_string()}")

    resolved: List[Tuple[str, List[Condition]]] = []
    for branch_conditions, address_value in _enumerate_constant_expression_branches(target_expr):
        target_name = _lookup_exact_function_name_by_value(tracer, address_value)
        if not target_name or target_name == "UNKNOWN_FUNC":
            raw_target_name = _lookup_raw_code_target_name(tracer, address_value)
            if raw_target_name is not None:
                simplified = ConditionSimplifier.simplify_conditions(branch_conditions)
                resolved.append((raw_target_name, simplified))
                if debug:
                    cond_strs = [cond.to_string() for cond in simplified]
                    print(
                        "[CallTargetResolver] resolved raw code target "
                        f"0x{address_value:x} -> {raw_target_name} under {cond_strs}"
                    )
                continue
            if debug:
                print(
                    "[CallTargetResolver] enumerated indirect target "
                    f"0x{address_value:x} has no exact function entry"
                )
            continue
        simplified = ConditionSimplifier.simplify_conditions(branch_conditions)
        resolved.append((target_name, simplified))
        if debug:
            cond_strs = [cond.to_string() for cond in simplified]
            print(
                "[CallTargetResolver] resolved indirect target "
                f"0x{address_value:x} -> {target_name} under {cond_strs}"
            )

    if resolved:
        return _deduplicate_resolved_call_targets(resolved)

    if direct_name and direct_name != "UNKNOWN_FUNC":
        return [(direct_name, [])]
    return []


def _deduplicate_resolved_call_targets(
    targets: Sequence[Tuple[str, List[Condition]]],
) -> List[Tuple[str, List[Condition]]]:
    deduped: List[Tuple[str, List[Condition]]] = []
    seen = set()
    for target_name, conditions in targets:
        key = (
            target_name,
            tuple(cond.to_string() for cond in conditions),
        )
        if key in seen:
            continue
        seen.add(key)
        deduped.append((target_name, list(conditions)))
    return deduped


def _enumerate_constant_expression_branches(
    expr: Optional[Expression],
) -> List[Tuple[List[Condition], int]]:
    if expr is None:
        return []

    if expr.expr_type == ExpressionType.PHI and expr.value:
        resolved: List[Tuple[List[Condition], int]] = []
        for cond, value in expr.value:
            for branch_conditions, branch_value in _enumerate_constant_expression_branches(value):
                merged = list(branch_conditions)
                if cond is not None:
                    merged.insert(0, cond)
                resolved.append((merged, branch_value))
        return resolved

    if expr.expr_type == ExpressionType.UNARY_OP and expr.operands:
        operand_branches = _enumerate_constant_expression_branches(expr.operands[0])
        if operand_branches:
            resolved: List[Tuple[List[Condition], int]] = []
            for branch_conditions, operand_value in operand_branches:
                applied = _apply_unary_constant_op(expr, operand_value)
                if applied is None:
                    continue
                resolved.append((list(branch_conditions), applied))
            if resolved:
                return resolved

    if expr.expr_type == ExpressionType.BINARY_OP and len(expr.operands) == 2:
        left_branches = _enumerate_constant_expression_branches(expr.operands[0])
        right_branches = _enumerate_constant_expression_branches(expr.operands[1])
        if left_branches and right_branches:
            resolved: List[Tuple[List[Condition], int]] = []
            for left_conditions, left_value in left_branches:
                for right_conditions, right_value in right_branches:
                    applied = _apply_binary_constant_op(expr, left_value, right_value)
                    if applied is None:
                        continue
                    resolved.append((list(left_conditions) + list(right_conditions), applied))
            if resolved:
                return resolved

    const_value = _evaluate_constant_expression(expr)
    if const_value is None:
        return []
    return [([], const_value)]


def _evaluate_constant_expression(expr: Optional[Expression]) -> Optional[int]:
    if expr is None:
        return None

    if expr.expr_type == ExpressionType.CONSTANT and isinstance(expr.value, int):
        return int(expr.value)

    if expr.expr_type == ExpressionType.VARIABLE and expr.name:
        return _extract_address_suffix(expr.name, ("PTR_", "DAT_", "LAB_", "FUN_"))

    if expr.expr_type == ExpressionType.UNARY_OP and expr.operands:
        operand_value = _evaluate_constant_expression(expr.operands[0])
        if operand_value is None:
            return None
        target_bits = max(8, (expr.size or expr.operands[0].size or 8) * 8)
        if expr.operator in {"CAST", "COPY", "INT_ZEXT"}:
            return operand_value & ((1 << target_bits) - 1)
        if expr.operator == "INT_SEXT":
            return _sign_extend_value(operand_value, expr.operands[0].get_bit_width(), target_bits)
        if expr.operator == "SUBPIECE" and len(expr.operands) >= 2:
            offset_value = _evaluate_constant_expression(expr.operands[1])
            if offset_value is None:
                return None
            shifted = operand_value >> (int(offset_value) * 8)
            return shifted & ((1 << target_bits) - 1)
        return None

    if expr.expr_type == ExpressionType.BINARY_OP and len(expr.operands) == 2:
        left_value = _evaluate_constant_expression(expr.operands[0])
        right_value = _evaluate_constant_expression(expr.operands[1])
        if left_value is None or right_value is None:
            return None

        if expr.operator == "INT_ADD":
            return _mask_to_expr_width(expr, left_value + right_value)
        if expr.operator == "INT_SUB":
            return _mask_to_expr_width(expr, left_value - right_value)
        if expr.operator == "INT_MULT":
            return _mask_to_expr_width(expr, left_value * right_value)
        if expr.operator == "INT_AND":
            return _mask_to_expr_width(expr, left_value & right_value)
        if expr.operator == "INT_OR":
            return _mask_to_expr_width(expr, left_value | right_value)
        if expr.operator == "INT_XOR":
            return _mask_to_expr_width(expr, left_value ^ right_value)
        if expr.operator == "PIECE":
            low_bits = expr.operands[1].get_bit_width()
            return _mask_to_expr_width(
                expr,
                (left_value << low_bits) | (right_value & ((1 << low_bits) - 1)),
            )
        return None

    return None


def _apply_unary_constant_op(expr: Expression, operand_value: int) -> Optional[int]:
    target_bits = max(8, (expr.size or expr.operands[0].size or 8) * 8)
    if expr.operator in {"CAST", "COPY", "INT_ZEXT"}:
        return operand_value & ((1 << target_bits) - 1)
    if expr.operator == "INT_SEXT":
        return _sign_extend_value(operand_value, expr.operands[0].get_bit_width(), target_bits)
    return None


def _apply_binary_constant_op(expr: Expression, left_value: int, right_value: int) -> Optional[int]:
    if expr.operator == "INT_ADD":
        return _mask_to_expr_width(expr, left_value + right_value)
    if expr.operator == "INT_SUB":
        return _mask_to_expr_width(expr, left_value - right_value)
    if expr.operator == "INT_MULT":
        return _mask_to_expr_width(expr, left_value * right_value)
    if expr.operator == "INT_AND":
        return _mask_to_expr_width(expr, left_value & right_value)
    if expr.operator == "INT_OR":
        return _mask_to_expr_width(expr, left_value | right_value)
    if expr.operator == "INT_XOR":
        return _mask_to_expr_width(expr, left_value ^ right_value)
    if expr.operator == "PIECE":
        low_bits = expr.operands[1].get_bit_width()
        return _mask_to_expr_width(
            expr,
            (left_value << low_bits) | (right_value & ((1 << low_bits) - 1)),
        )
    return None


def _sign_extend_value(value: int, source_bits: int, target_bits: int) -> int:
    source_bits = max(1, int(source_bits))
    target_bits = max(source_bits, int(target_bits))
    mask = (1 << source_bits) - 1
    value &= mask
    sign_bit = 1 << (source_bits - 1)
    if value & sign_bit:
        value -= 1 << source_bits
    return value & ((1 << target_bits) - 1)


def _mask_to_expr_width(expr: Expression, value: int) -> int:
    bit_width = max(1, expr.get_bit_width())
    return value & ((1 << bit_width) - 1)


def _is_synthetic_function_name(name: Optional[str]) -> bool:
    if not name:
        return False
    return bool(re.fullmatch(r"(?:thunk_)?FUN_[0-9a-fA-F]+", name))


def _lookup_function_name_by_value(tracer, address_value: int) -> Optional[str]:
    try:
        default_space = tracer.program.getAddressFactory().getDefaultAddressSpace()
        addr = default_space.getAddress(address_value)
        func_manager = tracer.program.getFunctionManager()
        func = func_manager.getFunctionAt(addr)
        if func is None:
            func = func_manager.getFunctionContaining(addr)
        if func:
            return func.getName()
        return f"FUN_{address_value:x}"
    except Exception:
        return None


def _lookup_exact_function_name_by_value(tracer, address_value: int) -> Optional[str]:
    try:
        default_space = tracer.program.getAddressFactory().getDefaultAddressSpace()
        addr = default_space.getAddress(address_value)
        func_manager = tracer.program.getFunctionManager()
        func = func_manager.getFunctionAt(addr)
        if func:
            return func.getName()
        return None
    except Exception:
        return None


def _lookup_raw_code_target_name(tracer, address_value: int) -> Optional[str]:
    try:
        if not isinstance(address_value, int) or address_value < 0:
            return None
        return f"ADDR_{address_value:x}"
    except Exception:
        return None


def _resolve_call_argument_expression(
    varnode,
    tracer,
    parameters: Sequence[Dict],
    depth: int = 0,
    seen: Optional[Set[int]] = None,
) -> Expression:
    try:
        def_op = varnode.getDef()
    except Exception:
        def_op = None

    expr = tracer.trace_varnode(varnode, use_cache=False)
    if expr.expr_type == ExpressionType.PARAMETER:
        return expr
    if (
        def_op is None
        and canonicalize_param_location(
            expr,
            parameters,
            size=max(1, getattr(varnode, "getSize", lambda: 0)()),
        )
        is not None
    ):
        return expr

    recovered = _recover_parameter_expression_from_varnode(
        varnode,
        tracer,
        parameters,
        depth=depth,
        seen=seen,
    )
    if recovered is not None:
        return recovered
    return expr


def _recover_call_argument_from_storage(
    call_op,
    tracer,
    caller_parameters: Sequence[Dict],
    callee_param: Dict,
) -> Optional[Expression]:
    target_storage = _coerce_storage_info(callee_param.get("storage"))
    if target_storage is None:
        return None

    call_order = _get_order_key(call_op)
    best_candidate = None
    best_order = None
    best_rank = -1
    best_semantic_rank = -1

    for op in tracer.get_all_pcode_ops():
        op_order = _get_order_key(op)
        if op_order >= call_order:
            continue

        output = op.getOutput()
        output_rank = _varnode_storage_match_rank(output, target_storage, tracer)
        if output is not None and output_rank > 0:
            candidate_expr = _resolve_call_argument_expression(output, tracer, caller_parameters)
            semantic_rank = _call_argument_semantic_rank(
                candidate_expr,
                caller_parameters,
                callee_param,
            )
            if (
                semantic_rank > best_semantic_rank
                or (
                    semantic_rank == best_semantic_rank
                    and (
                        output_rank > best_rank
                        or (output_rank == best_rank and (best_order is None or op_order > best_order))
                    )
                )
            ):
                best_candidate = candidate_expr
                best_order = op_order
                best_rank = output_rank
                best_semantic_rank = semantic_rank

        if not target_storage.is_register and op.getMnemonic() == "STORE" and op.getNumInputs() >= 3:
            if _stack_varnode_matches_storage(op.getInput(1), target_storage):
                candidate_expr = _resolve_call_argument_expression(op.getInput(2), tracer, caller_parameters)
                semantic_rank = _call_argument_semantic_rank(
                    candidate_expr,
                    caller_parameters,
                    callee_param,
                )
                if (
                    semantic_rank > best_semantic_rank
                    or (
                        semantic_rank == best_semantic_rank
                        and (3 > best_rank or (3 == best_rank and (best_order is None or op_order > best_order)))
                    )
                ):
                    best_candidate = candidate_expr
                    best_order = op_order
                    best_rank = 3
                    best_semantic_rank = semantic_rank

    if best_candidate is None:
        return None

    return best_candidate


def _parameter_expression_from_matching_storage(
    callee_param: Dict,
    caller_parameters: Sequence[Dict],
    size: Optional[int] = None,
) -> Optional[Expression]:
    callee_storage = _coerce_storage_info(callee_param.get("storage"))
    if callee_storage is None:
        return None

    matches: List[Dict] = []
    for caller_param in caller_parameters:
        caller_storage = _coerce_storage_info(caller_param.get("storage"))
        if caller_storage is None:
            continue
        if _storage_infos_match(caller_storage, callee_storage):
            matches.append(caller_param)

    if len(matches) != 1:
        return None
    return _parameter_expression_from_descriptor(matches[0], size=size or callee_param.get("size"))


def _varnode_matches_storage(varnode, target_storage: StorageInfo, tracer) -> bool:
    return _varnode_storage_match_rank(varnode, target_storage, tracer) > 0


def _varnode_storage_match_rank(varnode, target_storage: StorageInfo, tracer) -> int:
    varnode_storage = tracer._get_storage_info_from_varnode(varnode)
    if varnode_storage is not None:
        return _storage_match_rank(varnode_storage, target_storage)
    if target_storage.is_register:
        return 0
    return 3 if _stack_varnode_matches_storage(varnode, target_storage) else 0


def _stack_varnode_matches_storage(varnode, target_storage: StorageInfo) -> bool:
    if varnode is None:
        return False
    try:
        addr = varnode.getAddress()
        space = addr.getAddressSpace()
        if space is None:
            return False
        return (
            space.getName() == target_storage.space_name
            and int(varnode.getOffset()) == target_storage.offset
            and int(varnode.getSize()) == target_storage.size
        )
    except Exception:
        return False


def _storage_infos_match(left: StorageInfo, right: StorageInfo) -> bool:
    return _storage_match_rank(left, right) > 0


def _storage_match_rank(left: StorageInfo, right: StorageInfo) -> int:
    if left.is_register or right.is_register:
        if not (left.is_register and right.is_register):
            return 0
        if left.shares_base_register_with(right):
            if (
                left.bit_offset_in_base == right.bit_offset_in_base
                and left.size_bits == right.size_bits
                and left.size == right.size
            ):
                return 3
            if (
                StorageInfo._normalize_reg_name(left.register_name or "")
                == StorageInfo._normalize_reg_name(right.register_name or "")
            ):
                return 2
            if left.bit_range_overlaps_with(right):
                return 1
            return 0
        return (
            2
            if StorageInfo._normalize_reg_name(left.register_name or "")
            == StorageInfo._normalize_reg_name(right.register_name or "")
            else 0
        )
    return 3 if (
        left.space_name == right.space_name
        and left.offset == right.offset
        and left.size == right.size
    ) else 0


def _normalize_call_argument_expression(
    expr: Expression,
    arg_index: int,
    parameters: Sequence[Dict],
) -> Expression:
    if expr is None:
        return expr

    if _expression_maps_to_parameter(expr, parameters):
        return expr

    if expr.expr_type not in (ExpressionType.PARAMETER, ExpressionType.VARIABLE, ExpressionType.UNKNOWN):
        return expr
    if getattr(expr, "operands", None):
        return expr
    if arg_index < 0 or arg_index >= len(parameters):
        return expr

    fallback = _parameter_expression_from_descriptor(parameters[arg_index], size=expr.size or None)
    return fallback or expr


def _choose_effect_substitution_args(
    location: CanonicalLocation,
    callee_parameter_names: Sequence[str],
    args: Sequence[Expression],
    caller_parameters: Sequence[Dict],
) -> Sequence[Expression]:
    direct_location = substitute_location(location, callee_parameter_names, args, caller_parameters)
    if direct_location is not None:
        return args

    positional_args = _build_positional_parameter_args(args, caller_parameters)
    if positional_args is None:
        return args

    positional_location = substitute_location(
        location,
        callee_parameter_names,
        positional_args,
        caller_parameters,
    )
    if positional_location is not None:
        return positional_args
    return args


def _build_positional_parameter_args(
    args: Sequence[Expression],
    parameters: Sequence[Dict],
) -> Optional[List[Expression]]:
    if not args:
        return None
    positional_args: List[Expression] = []
    changed = False
    for index, expr in enumerate(args):
        fallback = _parameter_expression_from_descriptor(
            parameters[index],
            size=(expr.size if expr is not None else None),
        ) if index < len(parameters) else None
        if fallback is None:
            positional_args.append(expr)
            continue
        positional_args.append(fallback)
        changed = changed or not _expressions_equivalent(expr, fallback)
    if not changed:
        return None
    return positional_args


def _expression_maps_to_parameter(expr: Optional[Expression], parameters: Sequence[Dict]) -> bool:
    if expr is None:
        return False
    if _resolve_parameter_name(expr, parameters) is not None:
        return True
    size = expr.size or 0
    try:
        size = int(size)
    except Exception:
        size = 0
    if size <= 0:
        size = 8
    return canonicalize_param_location(expr, parameters, size=size) is not None


def _parameter_expression_from_descriptor(param: Dict, size: Optional[int] = None) -> Optional[Expression]:
    name = param.get("name")
    if not name:
        return None
    try:
        param_index = int(param.get("index", -1))
    except Exception:
        param_index = -1
    try:
        param_size = int(size or param.get("size", 8))
    except Exception:
        param_size = 8
    param_size = max(1, param_size)
    return Expression.parameter(
        name,
        param_index,
        param.get("data_type"),
        param_size,
        storage_info=_coerce_storage_info(param.get("storage")),
    )


def _recover_parameter_expression_from_varnode(
    varnode,
    tracer,
    parameters: Sequence[Dict],
    depth: int = 0,
    seen: Optional[Set[int]] = None,
) -> Optional[Expression]:
    if varnode is None or depth > 12:
        return None

    if seen is None:
        seen = set()
    varnode_id = id(varnode)
    if varnode_id in seen:
        return None
    seen.add(varnode_id)

    direct = _parameter_expression_from_varnode(varnode, tracer, parameters)
    if direct is not None:
        return direct

    def_op = varnode.getDef()
    if def_op is None:
        return None

    mnemonic = def_op.getMnemonic()
    if mnemonic in {"COPY", "CAST", "INT_ZEXT", "INT_SEXT"} and def_op.getNumInputs() >= 1:
        return _recover_parameter_expression_from_varnode(
            def_op.getInput(0),
            tracer,
            parameters,
            depth=depth + 1,
            seen=seen,
        )

    if mnemonic == "SUBPIECE" and def_op.getNumInputs() >= 2:
        offset_expr = tracer.trace_varnode(def_op.getInput(1), use_cache=False)
        if offset_expr.expr_type == ExpressionType.CONSTANT and int(offset_expr.value) == 0:
            return _recover_parameter_expression_from_varnode(
                def_op.getInput(0),
                tracer,
                parameters,
                depth=depth + 1,
                seen=seen,
            )

    if mnemonic == "PIECE" and def_op.getNumInputs() >= 2:
        for index in range(def_op.getNumInputs()):
            recovered = _recover_parameter_expression_from_varnode(
                def_op.getInput(index),
                tracer,
                parameters,
                depth=depth + 1,
                seen=seen,
            )
            if recovered is not None:
                return recovered

    if mnemonic == "LOAD" and def_op.getNumInputs() >= 2:
        recovered = _recover_parameter_from_stack_load(
            def_op,
            tracer,
            parameters,
            depth=depth + 1,
            seen=seen,
        )
        if recovered is not None:
            return recovered

    return None


def _parameter_expression_from_varnode(varnode, tracer, parameters: Sequence[Dict]) -> Optional[Expression]:
    try:
        high_var = varnode.getHigh()
    except Exception:
        high_var = None
    try:
        def_op = varnode.getDef()
    except Exception:
        def_op = None

    storage_info = tracer._get_storage_info_from_varnode(varnode)

    # Defined varnodes can reuse a parameter-like HighSymbol after register allocation.
    # Recovering passthrough parameters is handled by the recursive caller, so avoid
    # directly relabeling call-defined temporaries as live-in parameters here.
    if def_op is not None:
        return None

    if high_var is not None:
        symbol = high_var.getSymbol()
        if symbol is not None:
            symbol_name = symbol.getName()
            for param in parameters:
                if param.get("name") != symbol_name:
                    continue
                try:
                    param_index = int(param.get("index", -1))
                except Exception:
                    param_index = -1
                return Expression.parameter(
                    symbol_name,
                    param_index,
                    param.get("data_type"),
                    varnode.getSize(),
                    storage_info=storage_info,
                )

    probe = Expression.variable(
        getattr(high_var, "getName", lambda: None)() or f"var_{id(varnode):x}",
        size=varnode.getSize(),
        storage_info=storage_info,
    )
    resolved_name = _resolve_parameter_name(probe, parameters)
    if resolved_name is None:
        return None

    param = next((item for item in parameters if item.get("name") == resolved_name), None)
    if param is None:
        return None

    try:
        param_index = int(param.get("index", -1))
    except Exception:
        param_index = -1
    return Expression.parameter(
        resolved_name,
        param_index,
        param.get("data_type"),
        varnode.getSize(),
        storage_info=storage_info,
    )


def _recover_parameter_from_stack_load(
    load_op,
    tracer,
    parameters: Sequence[Dict],
    depth: int,
    seen: Set[int],
) -> Optional[Expression]:
    location = _stack_location_key(load_op.getInput(1), size=load_op.getOutput().getSize() if load_op.getOutput() else 0)
    if location is None:
        return None

    load_order = _get_order_key(load_op)
    best_candidate = None
    best_order = None
    for op in tracer.get_all_pcode_ops():
        op_order = _get_order_key(op)
        if op_order >= load_order:
            continue

        output = op.getOutput()
        if output is not None:
            output_location = _stack_location_key(output, size=output.getSize())
            if output_location == location:
                if best_order is None or op_order > best_order:
                    best_candidate = ("output", op)
                    best_order = op_order

        if op.getMnemonic() == "STORE" and op.getNumInputs() >= 3:
            store_location = _stack_location_key(op.getInput(1), size=op.getInput(2).getSize())
            if store_location == location:
                if best_order is None or op_order > best_order:
                    best_candidate = ("store", op)
                    best_order = op_order

    if best_candidate is None:
        return None

    kind, op = best_candidate
    if kind == "output" and op.getNumInputs() >= 1:
        return _recover_parameter_expression_from_varnode(
            op.getInput(0),
            tracer,
            parameters,
            depth=depth,
            seen=seen,
        )

    if kind == "store" and op.getNumInputs() >= 3:
        return _recover_parameter_expression_from_varnode(
            op.getInput(2),
            tracer,
            parameters,
            depth=depth,
            seen=seen,
        )

    return None


def _stack_location_key(varnode, size: int = 0) -> Optional[Tuple[str, int, int]]:
    if varnode is None:
        return None
    try:
        addr = varnode.getAddress()
        space = addr.getAddressSpace()
        if space is None or space.getName() != "stack":
            return None
        return ("stack", int(varnode.getOffset()), int(size or varnode.getSize()))
    except Exception:
        return None


def is_call_effect_summary_allowed(summary: EffectSummary) -> bool:
    if summary is None:
        return False
    if summary.has_unsupported_call:
        return False
    if not summary.effects:
        return False

    for effect in summary.effects:
        if not _expression_is_call_scope_safe(effect.value):
            return False
        for condition in effect.conditions:
            if not _expression_is_call_scope_safe(condition.expression):
                return False

    if summary.synthetic_expr is not None and not _expression_is_call_scope_safe(summary.synthetic_expr):
        return False

    return True


def _expression_is_call_scope_safe(expr: Optional[Expression]) -> bool:
    if expr is None:
        return True

    expr_type = expr.expr_type
    expr_kind = expr_type.__class__

    if expr_type in (expr_kind.CALL, expr_kind.UNKNOWN):
        return False

    if expr_type == expr_kind.PHI and expr.value:
        for cond, value in expr.value:
            if cond is not None and not _expression_is_call_scope_safe(cond.expression):
                return False
            if not _expression_is_call_scope_safe(value):
                return False
        return True

    for operand in getattr(expr, "operands", []) or []:
        if not _expression_is_call_scope_safe(operand):
            return False

    return True


def _summary_has_interdependent_writes(summary: EffectSummary) -> bool:
    if summary is None or len(summary.effects) <= 1:
        return False

    params = [{"name": name} for name in summary.parameter_names]
    for index, effect in enumerate(summary.effects):
        for other_index, other in enumerate(summary.effects):
            if index == other_index:
                continue
            if effect.location == other.location:
                continue
            if _expression_reads_location(effect.value, other.location, effect.conditions, params):
                return True
    return False


def canonicalize_param_location(
    addr_expr: Expression,
    parameters: Sequence[Dict],
    size: int = 4,
) -> Optional[CanonicalLocation]:
    canonical = _canonicalize_address_expression(addr_expr, parameters, size=size)
    if canonical is None:
        return None
    if not any(param.get("name") == canonical.base_param for param in parameters):
        return None
    return canonical


def canonicalize_location(
    addr_expr: Expression,
    parameters: Sequence[Dict],
    size: int = 4,
) -> Optional[CanonicalLocation]:
    return _canonicalize_address_expression(addr_expr, parameters, size=size)


def substitute_location(
    location: CanonicalLocation,
    callee_params: Sequence[str],
    call_args: Sequence[Expression],
    caller_params: Sequence[Dict],
) -> Optional[CanonicalLocation]:
    arg_map = dict(zip(callee_params, call_args))
    actual_addr = arg_map.get(location.base_param)
    if actual_addr is None:
        return None
    caller_location = canonicalize_location(actual_addr, caller_params, size=location.size)
    if caller_location is None:
        return None
    composed_steps = _location_step_sequence(caller_location) + list(location.steps)
    return _normalize_canonical_location(
        CanonicalLocation(
            base_param=caller_location.base_param,
            offset=location.offset,
            size=location.size,
            steps=tuple(composed_steps),
        )
    )


def rewrite_loads_from_effects(
    expr: Expression,
    return_conditions: Sequence[Condition],
    effects: Sequence[StoreEffect],
    parameters: Sequence[Dict],
    max_order_key: Optional[int] = None,
    blocked_locations: Optional[Sequence[CanonicalLocation]] = None,
    cycle_components: Optional[Dict[CanonicalLocation, FrozenSet[CanonicalLocation]]] = None,
) -> Expression:
    if expr is None:
        return expr

    active_blocked_locations = list(blocked_locations or [])
    active_cycle_components = cycle_components
    if active_cycle_components is None:
        active_cycle_components = _compute_effect_cycle_components(effects, parameters)

    synthetic_location = _parse_synthetic_location_read_name(getattr(expr, "name", None))
    if expr.expr_type == ExpressionType.VARIABLE and synthetic_location is not None:
        fallback_expr = post_state_read_expression_for_location(
            synthetic_location,
            parameters,
            symbolic=False,
        )
        if fallback_expr is None:
            fallback_expr = expr
        return _rewrite_canonical_location_read(
            fallback_expr,
            fallback_expr,
            synthetic_location,
            return_conditions,
            effects,
            parameters,
            max_order_key=max_order_key,
            blocked_locations=active_blocked_locations,
            cycle_components=active_cycle_components,
            definite_post_state=True,
        )

    if expr.expr_type == ExpressionType.MEMORY and expr.operands:
        rewritten_addr = rewrite_loads_from_effects(
            expr.operands[0],
            return_conditions,
            effects,
            parameters,
            max_order_key=max_order_key,
            blocked_locations=active_blocked_locations,
            cycle_components=active_cycle_components,
        )
        location = canonicalize_location(rewritten_addr, parameters, size=expr.size)
        candidate = Expression.memory(rewritten_addr, expr.size)
        if location is None:
            return candidate
        return _rewrite_canonical_location_read(
            candidate,
            candidate,
            location,
            return_conditions,
            effects,
            parameters,
            max_order_key=max_order_key,
            blocked_locations=active_blocked_locations,
            cycle_components=active_cycle_components,
        )

    if expr.expr_type in (ExpressionType.BINARY_OP, ExpressionType.UNARY_OP, ExpressionType.CALL):
        expr_location = canonicalize_expr_read_location(expr, parameters)
        if expr_location is not None and _matches_existing_effect_value(
            expr,
            expr_location,
            return_conditions,
            effects,
            parameters,
            max_order_key=max_order_key,
        ):
            return expr
        new_operands = [
            rewrite_loads_from_effects(
                op,
                return_conditions,
                effects,
                parameters,
                max_order_key=max_order_key,
                blocked_locations=active_blocked_locations,
                cycle_components=active_cycle_components,
            )
            for op in expr.operands
        ]
        return _clone_expression_with_operands(expr, new_operands) if not all(
            new is old for new, old in zip(new_operands, expr.operands)
        ) else expr

    if expr.expr_type == ExpressionType.PHI and expr.value:
        branches = []
        changed = False
        for cond, value in expr.value:
            combined_conditions = list(return_conditions)
            if cond is not None:
                combined_conditions.append(cond)
            new_value = rewrite_loads_from_effects(
                value,
                combined_conditions,
                effects,
                parameters,
                max_order_key=max_order_key,
                blocked_locations=active_blocked_locations,
                cycle_components=active_cycle_components,
            )
            branches.append((cond, new_value))
            changed = changed or (new_value is not value)
        if not changed:
            return expr
        rebuilt = Expression.phi(branches)
        rebuilt.size = expr.size
        return rebuilt

    return expr


def rewrite_location_read_from_effects(
    location: CanonicalLocation,
    fallback_expr: Expression,
    return_conditions: Sequence[Condition],
    effects: Sequence[StoreEffect],
    parameters: Sequence[Dict],
    max_order_key: Optional[int] = None,
    blocked_locations: Optional[Sequence[CanonicalLocation]] = None,
    cycle_components: Optional[Dict[CanonicalLocation, FrozenSet[CanonicalLocation]]] = None,
    definite_post_state: bool = False,
) -> Expression:
    candidate = memory_expression_for_location(location, parameters)
    if candidate is None:
        return fallback_expr
    return _rewrite_canonical_location_read(
        candidate,
        fallback_expr,
        location,
        return_conditions,
        effects,
        parameters,
        max_order_key=max_order_key,
        blocked_locations=blocked_locations,
        cycle_components=cycle_components,
        definite_post_state=definite_post_state,
    )


def _rewrite_canonical_location_read(
    candidate_expr: Expression,
    fallback_expr: Expression,
    location: CanonicalLocation,
    return_conditions: Sequence[Condition],
    effects: Sequence[StoreEffect],
    parameters: Sequence[Dict],
    max_order_key: Optional[int] = None,
    blocked_locations: Optional[Sequence[CanonicalLocation]] = None,
    cycle_components: Optional[Dict[CanonicalLocation, FrozenSet[CanonicalLocation]]] = None,
    definite_post_state: bool = False,
) -> Expression:
    normalized_return_conditions = ConditionSimplifier.simplify_conditions(list(return_conditions))
    active_blocked_locations = list(blocked_locations or [])
    active_cycle_components = cycle_components
    if active_cycle_components is None:
        active_cycle_components = _compute_effect_cycle_components(effects, parameters)

    if _matches_existing_effect_value(
        candidate_expr,
        location,
        normalized_return_conditions,
        effects,
        parameters,
        max_order_key=max_order_key,
    ):
        return candidate_expr

    for blocked_location in active_blocked_locations:
        if blocked_location.size != location.size:
            continue
        if locations_match(location, blocked_location, normalized_return_conditions):
            return fallback_expr

    matched = []
    for effect in effects:
        normalized_effect_conditions = ConditionSimplifier.simplify_conditions(list(effect.conditions))
        if max_order_key is not None and effect.order_key >= max_order_key:
            continue
        if effect.location.size != location.size:
            continue
        if ConditionSimplifier.is_contradiction(normalized_return_conditions + normalized_effect_conditions):
            continue
        if not locations_match(location, effect.location, normalized_return_conditions + normalized_effect_conditions):
            continue
        residual = subtract_implied_conditions(normalized_effect_conditions, normalized_return_conditions)
        matched.append((effect.order_key, residual, effect.value))

    if not matched:
        return fallback_expr

    if definite_post_state and _all_residual_guards_empty(matched):
        replayed_state = _replay_definite_active_effects_for_location(
            location,
            normalized_return_conditions,
            effects,
            parameters,
        )
        if replayed_state is not None:
            return replayed_state

    if _has_overlapping_guards(matched):
        return fallback_expr

    matched.sort(key=lambda item: item[0], reverse=True)
    branches = []
    for effect_order, residual, value in matched:
        preserved_locations = list(active_cycle_components.get(location, frozenset()))
        if location not in preserved_locations:
            preserved_locations.append(location)
        next_blocked_locations = active_blocked_locations + preserved_locations
        rewritten_value = rewrite_loads_from_effects(
            value,
            normalized_return_conditions,
            effects,
            parameters,
            max_order_key=effect_order,
            blocked_locations=next_blocked_locations,
            cycle_components=active_cycle_components,
        )
        if residual:
            branches.append((Condition.combine_and(residual), rewritten_value))
        else:
            return rewritten_value

    branches.append((None, fallback_expr))
    resolved = Expression.phi(branches)
    resolved.size = max(candidate_expr.size or 0, fallback_expr.size or 0, location.size)
    return resolved


def rewrite_observed_loads_from_effects(
    expr: Optional[Expression],
    return_conditions: Sequence[Condition],
    effects: Sequence[StoreEffect],
    parameters: Sequence[Dict],
) -> Optional[Expression]:
    """
    Rewrite raw observed LOAD expressions into pre-state equivalents.

    This pass is intentionally narrower than rewrite_loads_from_effects():
    it only rewrites MEMORY leaves that still carry a read_order_key from the
    traced LOAD op. Canonical MEMORY expressions synthesized by effect-summary
    logic do not carry that key, so they are left untouched.
    """
    if expr is None:
        return None

    if expr.expr_type == ExpressionType.MEMORY and expr.operands:
        rewritten_addr = rewrite_observed_loads_from_effects(
            expr.operands[0],
            return_conditions,
            effects,
            parameters,
        )
        current = expr
        if rewritten_addr is not expr.operands[0]:
            current = Expression.memory(
                rewritten_addr if rewritten_addr is not None else expr.operands[0],
                expr.size,
                read_order_key=expr.read_order_key,
            )

        if expr.read_order_key is None:
            return current

        rewritten = rewrite_loads_from_effects(
            current,
            return_conditions,
            effects,
            parameters,
            max_order_key=expr.read_order_key,
        )
        return rewritten

    if expr.expr_type in (
        ExpressionType.BINARY_OP,
        ExpressionType.UNARY_OP,
        ExpressionType.CALL,
    ):
        rewritten_operands = [
            rewrite_observed_loads_from_effects(
                op,
                return_conditions,
                effects,
                parameters,
            )
            for op in expr.operands
        ]
        rebuilt = _rebuild_expression_from_optional_operands(
            expr,
            rewritten_operands,
            fallback=expr,
        )
        return rebuilt if rebuilt is not None else expr

    if expr.expr_type == ExpressionType.PHI and expr.value:
        changed = False
        branches = []
        for cond, value in expr.value:
            combined_conditions = list(return_conditions)
            if cond is not None:
                combined_conditions.append(cond)
            new_value = rewrite_observed_loads_from_effects(
                value,
                combined_conditions,
                effects,
                parameters,
            )
            branches.append((cond, new_value))
            changed = changed or (new_value is not value)
        if not changed:
            return expr
        rebuilt = Expression.phi(branches)
        rebuilt.size = expr.size
        return rebuilt

    return expr


def _matches_existing_effect_value(
    expr: Expression,
    location: CanonicalLocation,
    return_conditions: Sequence[Condition],
    effects: Sequence[StoreEffect],
    parameters: Sequence[Dict],
    max_order_key: Optional[int] = None,
) -> bool:
    normalized_return_conditions = ConditionSimplifier.simplify_conditions(list(return_conditions))
    for effect in effects:
        normalized_effect_conditions = ConditionSimplifier.simplify_conditions(list(effect.conditions))
        if max_order_key is not None and effect.order_key >= max_order_key:
            continue
        if ConditionSimplifier.is_contradiction(normalized_return_conditions + normalized_effect_conditions):
            continue
        if not locations_match(location, effect.location, normalized_return_conditions):
            continue
        if not _expression_reads_location(expr, location, normalized_return_conditions, parameters):
            continue
        if _expression_matches_value_under_conditions(
            expr,
            effect.value,
            normalized_return_conditions + normalized_effect_conditions,
        ):
            return True
    return False


def _expression_matches_value_under_conditions(
    expr: Expression,
    value: Expression,
    conditions: Sequence[Condition],
) -> bool:
    reduced_expr = _reduce_expression_under_conditions(expr, conditions)
    reduced_value = _reduce_expression_under_conditions(value, conditions)
    if _expressions_equivalent(reduced_expr, reduced_value):
        return True
    if reduced_value.expr_type != ExpressionType.PHI or not reduced_value.value:
        return False
    for cond, branch_value in reduced_value.value:
        combined = list(conditions)
        if cond is not None:
            combined.append(cond)
        if ConditionSimplifier.is_contradiction(combined):
            continue
        if _expression_matches_value_under_conditions(reduced_expr, branch_value, combined):
            return True
    return False


def canonicalize_expr_read_location(expr: Expression, parameters: Sequence[Dict]) -> Optional[CanonicalLocation]:
    if expr is None:
        return None
    synthetic_location = _parse_synthetic_location_read_name(getattr(expr, "name", None))
    if synthetic_location is not None:
        return synthetic_location
    if expr.expr_type == ExpressionType.MEMORY and expr.operands:
        return canonicalize_location(expr.operands[0], parameters, size=expr.size)
    if expr.expr_type == ExpressionType.BINARY_OP and len(expr.operands) == 2:
        left = canonicalize_expr_read_location(expr.operands[0], parameters)
        right = canonicalize_expr_read_location(expr.operands[1], parameters)
        if left is None:
            return right
        if right is None:
            return left
        if left == right:
            return left
        return None
    if expr.expr_type == ExpressionType.UNARY_OP and expr.operands:
        return canonicalize_expr_read_location(expr.operands[0], parameters)
    return None


def _expression_reads_location(
    expr: Optional[Expression],
    location: CanonicalLocation,
    conditions: Sequence[Condition],
    parameters: Sequence[Dict],
) -> bool:
    if expr is None:
        return False
    synthetic_location = _parse_synthetic_location_read_name(getattr(expr, "name", None))
    if synthetic_location is not None:
        return locations_match(synthetic_location, location, conditions)
    if expr.expr_type == ExpressionType.MEMORY and expr.operands:
        read_location = canonicalize_location(expr.operands[0], parameters, size=expr.size)
        if read_location is None:
            return False
        return locations_match(read_location, location, conditions)
    if expr.expr_type == ExpressionType.PHI and expr.value:
        for cond, value in expr.value:
            combined = list(conditions)
            if cond is not None:
                combined.append(cond)
            if _expression_reads_location(value, location, combined, parameters):
                return True
        return False
    for operand in getattr(expr, "operands", []) or []:
        if _expression_reads_location(operand, location, conditions, parameters):
            return True
    return False


def _compute_effect_cycle_components(
    effects: Sequence[StoreEffect],
    parameters: Sequence[Dict],
) -> Dict[CanonicalLocation, FrozenSet[CanonicalLocation]]:
    locations = sorted({effect.location for effect in effects}, key=_location_sort_key)
    if len(locations) <= 1:
        return {}

    graph: Dict[CanonicalLocation, Set[CanonicalLocation]] = {location: set() for location in locations}
    for effect in effects:
        for candidate in locations:
            if candidate == effect.location:
                continue
            if _expression_reads_location(effect.value, candidate, effect.conditions, parameters):
                graph[effect.location].add(candidate)

    components: Dict[CanonicalLocation, FrozenSet[CanonicalLocation]] = {}
    for component in _strongly_connected_components(graph):
        if len(component) <= 1:
            continue
        frozen_component = frozenset(component)
        for location in component:
            components[location] = frozen_component
    return components


def _strongly_connected_components(
    graph: Dict[CanonicalLocation, Set[CanonicalLocation]]
) -> List[List[CanonicalLocation]]:
    index = 0
    stack: List[CanonicalLocation] = []
    indices: Dict[CanonicalLocation, int] = {}
    lowlinks: Dict[CanonicalLocation, int] = {}
    on_stack: Set[CanonicalLocation] = set()
    components: List[List[CanonicalLocation]] = []

    def strongconnect(node: CanonicalLocation) -> None:
        nonlocal index
        indices[node] = index
        lowlinks[node] = index
        index += 1
        stack.append(node)
        on_stack.add(node)

        for succ in graph.get(node, set()):
            if succ not in indices:
                strongconnect(succ)
                lowlinks[node] = min(lowlinks[node], lowlinks[succ])
            elif succ in on_stack:
                lowlinks[node] = min(lowlinks[node], indices[succ])

        if lowlinks[node] != indices[node]:
            return

        component: List[CanonicalLocation] = []
        while stack:
            member = stack.pop()
            on_stack.discard(member)
            component.append(member)
            if member == node:
                break
        components.append(component)

    for node in graph:
        if node not in indices:
            strongconnect(node)

    return components


def _expressions_equivalent(left: Optional[Expression], right: Optional[Expression]) -> bool:
    if left is right:
        return True
    if left is None or right is None:
        return False
    if left.expr_type != right.expr_type:
        return False
    if left.expr_type == ExpressionType.CONSTANT:
        return left.value == right.value and left.size == right.size
    if left.expr_type in (ExpressionType.PARAMETER, ExpressionType.VARIABLE, ExpressionType.UNKNOWN, ExpressionType.CALL):
        return (
            left.name == right.name
            and left.value == right.value
            and left.size == right.size
        )
    if left.expr_type == ExpressionType.MEMORY:
        return left.size == right.size and _expressions_equivalent(left.operands[0], right.operands[0])
    if left.expr_type == ExpressionType.UNARY_OP:
        return (
            left.operator == right.operator
            and left.size == right.size
            and len(left.operands) == len(right.operands)
            and all(_expressions_equivalent(lop, rop) for lop, rop in zip(left.operands, right.operands))
        )
    if left.expr_type == ExpressionType.BINARY_OP:
        if left.operator != right.operator or left.size != right.size:
            return False
        if len(left.operands) != 2 or len(right.operands) != 2:
            return False
        left_pair = (left.operands[0], left.operands[1])
        right_pair = (right.operands[0], right.operands[1])
        if all(_expressions_equivalent(lop, rop) for lop, rop in zip(left_pair, right_pair)):
            return True
        if left.operator in {
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
        }:
            return _expressions_equivalent(left.operands[0], right.operands[1]) and _expressions_equivalent(
                left.operands[1], right.operands[0]
            )
        return False
    if left.expr_type == ExpressionType.PHI:
        if left.size != right.size or not left.value or not right.value or len(left.value) != len(right.value):
            return False
        for (left_cond, left_value), (right_cond, right_value) in zip(left.value, right.value):
            if left_cond is None or right_cond is None:
                if left_cond is not right_cond:
                    return False
            else:
                if left_cond.negated != right_cond.negated:
                    return False
                if not _expressions_equivalent(left_cond.expression, right_cond.expression):
                    return False
            if not _expressions_equivalent(left_value, right_value):
                return False
        return True
    return (
        left.operator == right.operator
        and left.name == right.name
        and left.value == right.value
        and left.size == right.size
        and len(left.operands) == len(right.operands)
        and all(_expressions_equivalent(lop, rop) for lop, rop in zip(left.operands, right.operands))
    )


def build_void_effect_summary_expr(effects: Sequence[StoreEffect]) -> Optional[Expression]:
    groups: Dict[CanonicalLocation, List[StoreEffect]] = {}
    for effect in effects:
        groups.setdefault(effect.location, []).append(effect)

    if not groups:
        return None

    summary_parts: List[Expression] = []
    for location in sorted(groups.keys(), key=_location_sort_key):
        loc_effects = sorted(groups[location], key=lambda effect: effect.order_key, reverse=True)
        value_branches = []
        flag_branches = []
        for effect in loc_effects:
            cond = Condition.combine_and(effect.conditions)
            value_branches.append((cond, effect.value))
            flag_branches.append((cond, Expression.constant(1, 1)))
        value_branches.append((None, Expression.constant(0, max(1, location.size))))
        flag_branches.append((None, Expression.constant(0, 1)))
        value_expr = Expression.phi(value_branches)
        value_expr.size = max(1, location.size)
        flag_expr = Expression.phi(flag_branches)
        flag_expr.size = 1
        summary_parts.append(_concat(flag_expr, value_expr))

    result = summary_parts[0]
    for part in summary_parts[1:]:
        result = _concat(result, part)
    return result


def collapse_post_state_expr_to_canonical_memory(
    expr: Optional[Expression],
    effects: Sequence[StoreEffect],
    parameters: Sequence[Dict],
    return_conditions: Optional[Sequence[Condition]] = None,
) -> Optional[Expression]:
    return collapse_post_state_expr_to_canonical_read(
        expr,
        effects,
        parameters,
        return_conditions=return_conditions,
        symbolic_post_state=False,
    )


def collapse_post_state_expr_to_canonical_read(
    expr: Optional[Expression],
    effects: Sequence[StoreEffect],
    parameters: Sequence[Dict],
    return_conditions: Optional[Sequence[Condition]] = None,
    *,
    symbolic_post_state: bool = False,
) -> Optional[Expression]:
    if expr is None or not effects or not parameters:
        return None
    if expr.expr_type == ExpressionType.MEMORY:
        return None

    active_conditions = list(return_conditions or [])
    normalized_expr = _reduce_expression_under_conditions(expr, active_conditions)
    locations = sorted(
        {effect.location for effect in effects},
        key=_location_sort_key,
    )
    for location in locations:
        candidate = post_state_read_expression_for_location(
            location,
            parameters,
            symbolic=symbolic_post_state,
        )
        if candidate is None:
            continue
        rewritten = rewrite_loads_from_effects(
            candidate,
            active_conditions,
            effects,
            parameters,
        )
        normalized_rewritten = _reduce_expression_under_conditions(rewritten, active_conditions)
        if _expressions_equivalent(normalized_expr, normalized_rewritten):
            return candidate
        replayed = _replay_definite_active_effects_for_location(
            location,
            active_conditions,
            effects,
            parameters,
        )
        if replayed is None:
            continue
        normalized_replayed = _reduce_expression_under_conditions(replayed, active_conditions)
        if _expressions_equivalent(normalized_expr, normalized_replayed):
            return candidate
def collapse_pruned_post_state_memory_leaf_to_canonical_memory(
    expr: Optional[Expression],
    effects: Sequence[StoreEffect],
    parameters: Sequence[Dict],
    return_conditions: Optional[Sequence[Condition]] = None,
) -> Optional[Expression]:
    """
    Resolve a bare MEMORY leaf back to the canonical post-state location.

    This is only sound when the leaf is known to come from a pruned post-state
    PHI/MULTIEQUAL, such as a nested MULTIEQUAL that a prior simplifier already
    reduced to one surviving branch.
    """
    if expr is None or not effects or not parameters:
        return None
    if expr.expr_type != ExpressionType.MEMORY:
        return None

    active_conditions = list(return_conditions or [])
    normalized_expr = _reduce_expression_under_conditions(expr, active_conditions)
    locations = sorted(
        {effect.location for effect in effects},
        key=_location_sort_key,
    )
    for location in locations:
        candidate = memory_expression_for_location(location, parameters)
        if candidate is None:
            continue
        rewritten = rewrite_loads_from_effects(
            candidate,
            active_conditions,
            effects,
            parameters,
        )
        normalized_rewritten = _reduce_expression_under_conditions(rewritten, active_conditions)
        if _expressions_equivalent(normalized_expr, normalized_rewritten):
            return candidate
        replayed = _replay_definite_active_effects_for_location(
            location,
            active_conditions,
            effects,
            parameters,
        )
        if replayed is None:
            continue
        normalized_replayed = _reduce_expression_under_conditions(replayed, active_conditions)
        if _expressions_equivalent(normalized_expr, normalized_replayed):
            return candidate

    return None


def canonicalize_post_state_subexpressions(
    expr: Optional[Expression],
    return_conditions: Sequence[Condition],
    effects: Sequence[StoreEffect],
    parameters: Sequence[Dict],
    *,
    symbolic_post_state: bool = False,
) -> Optional[Expression]:
    if expr is None:
        return None

    collapsed = collapse_post_state_expr_to_canonical_read(
        expr,
        effects,
        parameters,
        return_conditions=return_conditions,
        symbolic_post_state=symbolic_post_state,
    )
    if collapsed is not None:
        return collapsed

    if expr.expr_type in (ExpressionType.BINARY_OP, ExpressionType.UNARY_OP, ExpressionType.CALL, ExpressionType.MEMORY):
        rewritten_operands = [
            canonicalize_post_state_subexpressions(
                op,
                return_conditions,
                effects,
                parameters,
                symbolic_post_state=symbolic_post_state,
            )
            for op in expr.operands
        ]
        rebuilt = _rebuild_expression_from_optional_operands(
            expr,
            rewritten_operands,
            fallback=expr,
        )
        return rebuilt if rebuilt is not None else expr

    if expr.expr_type == ExpressionType.PHI and expr.value:
        changed = False
        branches = []
        for cond, value in expr.value:
            combined_conditions = list(return_conditions)
            if cond is not None:
                combined_conditions.append(cond)
            new_value = canonicalize_post_state_subexpressions(
                value,
                combined_conditions,
                effects,
                parameters,
                symbolic_post_state=symbolic_post_state,
            )
            branches.append((cond, new_value))
            changed = changed or (new_value is not value)
        if not changed:
            return expr
        rebuilt = Expression.phi(branches)
        rebuilt.size = expr.size
        return rebuilt

    return expr


def normalize_post_state_expression(
    expr: Optional[Expression],
    return_conditions: Sequence[Condition],
    effects: Sequence[StoreEffect],
    parameters: Sequence[Dict],
    *,
    prefer_canonical_post_state: bool = True,
    symbolic_post_state: bool = False,
) -> Optional[Expression]:
    """
    Normalize equivalent post-state expressions to a stable canonical form.

    The pipeline may derive semantically equivalent results in two shapes:
    1. canonical post-state memory (e.g. MEM[param])
    2. pre-state expressions reconstructed from guarded store effects

    Converting both shapes through the same canonicalization step keeps
    equivalent branches comparable across architectures and optimization levels.
    """
    if expr is None:
        return None

    normalized = expr

    if prefer_canonical_post_state:
        canonicalized = canonicalize_post_state_subexpressions(
            normalized,
            return_conditions,
            effects,
            parameters,
            symbolic_post_state=symbolic_post_state,
        )
        if canonicalized is not None:
            normalized = canonicalized

    if not prefer_canonical_post_state or _expressions_equivalent(normalized, expr):
        rewritten_definite = _rewrite_definite_post_state_subexpressions(
            normalized,
            return_conditions,
            effects,
            parameters,
        )
        if rewritten_definite is not None:
            normalized = rewritten_definite

    if (
        expression_contains_complex_location_reads(normalized, parameters)
        and not (symbolic_post_state and expression_contains_synthetic_location_reads(normalized))
    ):
        rewritten_post_state = rewrite_loads_from_effects(
            normalized,
            return_conditions,
            effects,
            parameters,
        )
        if rewritten_post_state is not None:
            normalized = rewritten_post_state

    reduced = _reduce_expression_under_conditions(normalized, return_conditions)
    return reduced if reduced is not None else normalized


def lower_post_state_expression_for_smt(
    expr: Optional[Expression],
    return_conditions: Sequence[Condition],
    effects: Sequence[StoreEffect],
    parameters: Sequence[Dict],
) -> Optional[Expression]:
    """
    Materialize symbolic post-state reads into guarded pre-state expressions.

    The analysis pipeline may keep post-state reads in a symbolic canonical form
    so architecture-specific expansion differences can still be merged safely.
    Before SMT lowering, we replay the relevant effect summary under the active
    return conditions to recover a path-sensitive expression.
    """
    if expr is None:
        return None

    lowered = rewrite_loads_from_effects(
        expr,
        return_conditions,
        effects,
        parameters,
    )
    reduced = _reduce_expression_under_conditions(lowered, return_conditions)
    return reduced if reduced is not None else lowered


def _rewrite_definite_post_state_subexpressions(
    expr: Optional[Expression],
    return_conditions: Sequence[Condition],
    effects: Sequence[StoreEffect],
    parameters: Sequence[Dict],
    rewrite_memory_leaf: bool = False,
) -> Optional[Expression]:
    """
    Replay definite active effects into post-state subexpressions.

    This is intentionally conservative: a MEMORY leaf is rewritten only when
    the current path conditions imply the relevant store effects. That keeps
    raw pre-state loads intact while still normalizing pruned post-state loads
    that lost their original read-order metadata during PHI simplification.
    """
    if expr is None:
        return None

    if expr.expr_type == ExpressionType.MEMORY and expr.operands:
        rewritten_addr = _rewrite_definite_post_state_subexpressions(
            expr.operands[0],
            return_conditions,
            effects,
            parameters,
            rewrite_memory_leaf=True,
        )
        current = expr
        if rewritten_addr is not expr.operands[0]:
            current = Expression.memory(
                rewritten_addr if rewritten_addr is not None else expr.operands[0],
                expr.size,
                read_order_key=expr.read_order_key,
            )

        if not rewrite_memory_leaf:
            return current

        location = canonicalize_location(current.operands[0], parameters, size=current.size)
        if location is None:
            return current

        active_effects = _collect_definite_active_effects(return_conditions, effects)
        if len(active_effects) > 1 and _summary_has_interdependent_writes(
            EffectSummary(
                parameter_names=_collect_named_parameter_names(parameters),
                effects=list(active_effects),
            )
        ):
            return current

        replayed = _replay_definite_active_effects_for_location(
            location,
            return_conditions,
            active_effects,
            parameters,
        )
        if replayed is None:
            return current

        reduced_replayed = _reduce_expression_under_conditions(replayed, return_conditions)
        resolved = reduced_replayed if reduced_replayed is not None else replayed
        return current if _expressions_equivalent(current, resolved) else resolved

    if expr.expr_type in (
        ExpressionType.BINARY_OP,
        ExpressionType.UNARY_OP,
        ExpressionType.CALL,
    ):
        expr_location = canonicalize_expr_read_location(expr, parameters)
        if expr_location is not None and _matches_existing_effect_value(
            expr,
            expr_location,
            return_conditions,
            effects,
            parameters,
        ):
            return expr
        rewritten_operands = [
            _rewrite_definite_post_state_subexpressions(
                operand,
                return_conditions,
                effects,
                parameters,
                rewrite_memory_leaf=True,
            )
            for operand in expr.operands
        ]
        rebuilt = _rebuild_expression_from_optional_operands(
            expr,
            rewritten_operands,
            fallback=expr,
        )
        return rebuilt if rebuilt is not None else expr

    if expr.expr_type == ExpressionType.PHI and expr.value:
        changed = False
        branches = []
        for cond, value in expr.value:
            combined_conditions = list(return_conditions)
            if cond is not None:
                combined_conditions.append(cond)
            new_value = _rewrite_definite_post_state_subexpressions(
                value,
                combined_conditions,
                effects,
                parameters,
                rewrite_memory_leaf=True,
            )
            branches.append((cond, new_value))
            changed = changed or (new_value is not value)
        if not changed:
            return expr
        rebuilt = Expression.phi(branches)
        rebuilt.size = expr.size
        return rebuilt

    return expr


def _replay_definite_active_effects_for_location(
    location: CanonicalLocation,
    return_conditions: Sequence[Condition],
    effects: Sequence[StoreEffect],
    parameters: Sequence[Dict],
) -> Optional[Expression]:
    normalized_return_conditions = ConditionSimplifier.simplify_conditions(list(return_conditions))
    tracked_locations = sorted(
        {location, *[effect.location for effect in effects]},
        key=_location_sort_key,
    )
    alias_representatives = _build_alias_representative_map(
        tracked_locations,
        normalized_return_conditions,
    )
    if not alias_representatives:
        return None

    state: Dict[CanonicalLocation, Expression] = {}
    for representative in sorted(set(alias_representatives.values()), key=_location_sort_key):
        base_expr = memory_expression_for_location(representative, parameters)
        if base_expr is None:
            return None
        state[representative] = base_expr

    active_effects = _collect_definite_active_effects(normalized_return_conditions, effects)
    active_effects.sort(key=lambda effect: effect.order_key)
    for effect in active_effects:
        target_rep = _resolve_alias_representative(
            effect.location,
            alias_representatives,
            normalized_return_conditions,
        )
        if target_rep is None:
            continue
        replayed_value = _rewrite_expression_with_replayed_state(
            effect.value,
            normalized_return_conditions,
            state,
            alias_representatives,
            parameters,
        )
        if replayed_value is None:
            continue
        reduced_value = _reduce_expression_under_conditions(replayed_value, normalized_return_conditions)
        state[target_rep] = reduced_value if reduced_value is not None else replayed_value

    target_rep = _resolve_alias_representative(
        location,
        alias_representatives,
        normalized_return_conditions,
    )
    if target_rep is None:
        return None
    return state.get(target_rep)


def _collect_definite_active_effects(
    return_conditions: Sequence[Condition],
    effects: Sequence[StoreEffect],
) -> List[StoreEffect]:
    normalized_return_conditions = ConditionSimplifier.simplify_conditions(list(return_conditions))
    active_effects: List[StoreEffect] = []
    for effect in effects:
        normalized_effect_conditions = ConditionSimplifier.simplify_conditions(list(effect.conditions))
        if ConditionSimplifier.is_contradiction(normalized_return_conditions + normalized_effect_conditions):
            continue
        residual = subtract_implied_conditions(normalized_effect_conditions, normalized_return_conditions)
        if residual:
            continue
        active_effects.append(
            StoreEffect(
                location=effect.location,
                value=effect.value,
                conditions=normalized_effect_conditions,
                order_key=effect.order_key,
            )
        )
    return active_effects


def _rewrite_expression_with_replayed_state(
    expr: Optional[Expression],
    conditions: Sequence[Condition],
    state: Dict[CanonicalLocation, Expression],
    alias_representatives: Dict[CanonicalLocation, CanonicalLocation],
    parameters: Sequence[Dict],
) -> Optional[Expression]:
    if expr is None:
        return None

    synthetic_location = _parse_synthetic_location_read_name(getattr(expr, "name", None))
    if expr.expr_type == ExpressionType.VARIABLE and synthetic_location is not None:
        representative = _resolve_alias_representative(
            synthetic_location,
            alias_representatives,
            conditions,
        )
        if representative is not None and representative in state:
            return state[representative]
        fallback = memory_expression_for_location(synthetic_location, parameters)
        return fallback if fallback is not None else expr

    if expr.expr_type == ExpressionType.MEMORY and expr.operands:
        rewritten_addr = _rewrite_expression_with_replayed_state(
            expr.operands[0],
            conditions,
            state,
            alias_representatives,
            parameters,
        )
        current = Expression.memory(
            rewritten_addr if rewritten_addr is not None else expr.operands[0],
            expr.size,
            read_order_key=expr.read_order_key,
        )
        location = canonicalize_location(current.operands[0], parameters, size=expr.size)
        if location is None:
            return current
        representative = _resolve_alias_representative(
            location,
            alias_representatives,
            conditions,
        )
        if representative is not None and representative in state:
            return state[representative]
        fallback = memory_expression_for_location(location, parameters)
        return fallback if fallback is not None else current

    if expr.expr_type in (
        ExpressionType.BINARY_OP,
        ExpressionType.UNARY_OP,
        ExpressionType.CALL,
    ):
        rewritten_operands = [
            _rewrite_expression_with_replayed_state(
                operand,
                conditions,
                state,
                alias_representatives,
                parameters,
            )
            for operand in expr.operands
        ]
        rebuilt = _rebuild_expression_from_optional_operands(
            expr,
            rewritten_operands,
            fallback=expr,
        )
        return rebuilt if rebuilt is not None else expr

    if expr.expr_type == ExpressionType.PHI and expr.value:
        changed = False
        branches = []
        for cond, value in expr.value:
            combined_conditions = list(conditions)
            if cond is not None:
                combined_conditions.append(cond)
            new_value = _rewrite_expression_with_replayed_state(
                value,
                combined_conditions,
                state,
                alias_representatives,
                parameters,
            )
            branches.append((cond, new_value))
            changed = changed or (new_value is not value)
        if not changed:
            return expr
        rebuilt = Expression.phi(branches)
        rebuilt.size = expr.size
        return rebuilt

    return expr


def _build_alias_representative_map(
    locations: Sequence[CanonicalLocation],
    conditions: Sequence[Condition],
) -> Dict[CanonicalLocation, CanonicalLocation]:
    groups: List[List[CanonicalLocation]] = []
    for location in sorted(set(locations), key=_location_sort_key):
        placed = False
        for group in groups:
            head = group[0]
            if head.size != location.size:
                continue
            if locations_match(location, head, conditions):
                group.append(location)
                placed = True
                break
        if not placed:
            groups.append([location])

    representatives: Dict[CanonicalLocation, CanonicalLocation] = {}
    for group in groups:
        representative = min(group, key=_location_sort_key)
        for member in group:
            representatives[member] = representative
    return representatives


def _resolve_alias_representative(
    location: CanonicalLocation,
    alias_representatives: Dict[CanonicalLocation, CanonicalLocation],
    conditions: Sequence[Condition],
) -> Optional[CanonicalLocation]:
    representative = alias_representatives.get(location)
    if representative is not None:
        return representative
    for candidate, candidate_rep in alias_representatives.items():
        if candidate.size != location.size:
            continue
        if locations_match(location, candidate, conditions):
            return candidate_rep
    return None


def _location_sort_key(location: CanonicalLocation) -> Tuple[str, Tuple[Tuple[str, int], ...], int, int]:
    normalized = _normalize_canonical_location(location)
    step_key = tuple((step.kind, int(step.value)) for step in normalized.steps)
    return (normalized.base_param, step_key, normalized.offset, normalized.size)


def memory_expression_for_location(
    location: CanonicalLocation,
    parameters: Sequence[Dict],
) -> Optional[Expression]:
    location = _normalize_canonical_location(location)
    param = next((item for item in parameters if item.get("name") == location.base_param), None)
    if param is None:
        return Expression.variable(
            _synthetic_location_read_name(location),
            size=max(1, location.size),
        )

    try:
        param_index = int(param.get("index", -1))
    except Exception:
        param_index = -1

    try:
        param_size = int(param.get("size", 8))
    except Exception:
        param_size = 8
    param_size = max(1, param_size)

    base = Expression.parameter(
        location.base_param,
        param_index,
        param.get("data_type"),
        param_size,
        storage_info=_coerce_storage_info(param.get("storage")),
    )
    addr: Expression = base
    for step in location.steps:
        if step.kind == "offset":
            addr = Expression.binary_op(
                "INT_ADD",
                addr,
                Expression.constant(step.value, max(1, addr.size or param_size)),
            )
            addr.size = max(1, addr.size or param_size)
            continue
        addr = Expression.memory(addr, size=max(1, int(step.value)))
    if location.offset != 0:
        addr = Expression.binary_op(
            "INT_ADD",
            addr,
            Expression.constant(location.offset, max(1, addr.size or param_size)),
        )
        addr.size = max(1, addr.size or param_size)

    return Expression.memory(addr, size=location.size)


def post_state_read_expression_for_location(
    location: CanonicalLocation,
    parameters: Sequence[Dict],
    *,
    symbolic: bool = False,
) -> Optional[Expression]:
    location = _normalize_canonical_location(location)
    if symbolic:
        return Expression.variable(
            _synthetic_location_read_name(location),
            size=max(1, location.size),
        )
    return memory_expression_for_location(location, parameters)


def _reduce_expression_under_conditions(
    expr: Expression,
    conditions: Sequence[Condition],
) -> Expression:
    if expr is None:
        return expr

    if expr.expr_type == ExpressionType.PHI and expr.value:
        for cond, value in expr.value:
            if cond is None:
                continue
            combined = list(conditions) + [cond]
            if ConditionSimplifier.is_contradiction(combined):
                continue
            if not subtract_implied_conditions([cond], conditions):
                return _reduce_expression_under_conditions(value, combined)

        surviving = []
        for cond, value in expr.value:
            combined = list(conditions)
            if cond is not None:
                combined.append(cond)
            if ConditionSimplifier.is_contradiction(combined):
                continue
            reduced_value = _reduce_expression_under_conditions(value, combined)
            surviving.append((cond, reduced_value))

        if not surviving:
            return expr
        if len(surviving) == 1:
            return surviving[0][1]

        rebuilt = Expression.phi(surviving)
        rebuilt.size = expr.size
        return rebuilt

    if expr.expr_type in (ExpressionType.BINARY_OP, ExpressionType.UNARY_OP, ExpressionType.CALL, ExpressionType.MEMORY):
        new_operands = [_reduce_expression_under_conditions(op, conditions) for op in expr.operands]
        return _clone_expression_with_operands(expr, new_operands) if not all(
            new is old for new, old in zip(new_operands, expr.operands)
        ) else expr

    return expr


def locations_match(
    left: CanonicalLocation,
    right: CanonicalLocation,
    conditions: Sequence[Condition],
) -> bool:
    left = _normalize_canonical_location(left)
    right = _normalize_canonical_location(right)
    if left.offset != right.offset:
        return False
    if left.steps != right.steps:
        return False
    if left.base_param == right.base_param:
        return True
    equalities = _collect_param_equalities(conditions)
    return frozenset((left.base_param, right.base_param)) in equalities


def subtract_implied_conditions(
    effect_conditions: Sequence[Condition],
    return_conditions: Sequence[Condition],
) -> List[Condition]:
    implied = _collect_implied_condition_norms(return_conditions)
    residual = []
    for cond in effect_conditions:
        if not _condition_is_implied(cond, implied):
            residual.append(cond)
    return residual


def _collect_implied_condition_norms(
    conditions: Sequence[Condition],
):
    implied = set()
    stack = list(conditions or [])
    while stack:
        condition = stack.pop()
        if condition is None:
            continue
        normalized = ConditionNormalizer.normalize_for_contradiction(condition)
        implied.add(normalized)

        expr = condition.expression
        if (
            not condition.negated
            and expr is not None
            and expr.expr_type == ExpressionType.BINARY_OP
            and expr.operator == "BOOL_AND"
        ):
            stack.append(Condition(expr.operands[0], False))
            stack.append(Condition(expr.operands[1], False))

    return implied


def _condition_is_implied(
    condition: Condition,
    implied_conditions,
) -> bool:
    normalized = ConditionNormalizer.normalize_for_contradiction(condition)
    if normalized in implied_conditions:
        return True

    expr = condition.expression
    if (
        not condition.negated
        and expr is not None
        and expr.expr_type == ExpressionType.BINARY_OP
        and expr.operator == "BOOL_AND"
    ):
        stack = [Condition(expr.operands[0], False), Condition(expr.operands[1], False)]
        while stack:
            current = stack.pop()
            current_expr = current.expression
            if (
                not current.negated
                and current_expr is not None
                and current_expr.expr_type == ExpressionType.BINARY_OP
                and current_expr.operator == "BOOL_AND"
            ):
                stack.append(Condition(current_expr.operands[0], False))
                stack.append(Condition(current_expr.operands[1], False))
                continue
            if ConditionNormalizer.normalize_for_contradiction(current) not in implied_conditions:
                return False
        return True

    return False


def substitute_condition(
    condition: Condition,
    replacements: Dict[str, Expression],
    parameters: Optional[Sequence[Dict]] = None,
) -> Condition:
    return Condition(
        substitute_expression(condition.expression, replacements, parameters),
        condition.negated,
    )


def substitute_expression(
    expr: Expression,
    replacements: Dict[str, Expression],
    parameters: Optional[Sequence[Dict]] = None,
) -> Expression:
    if expr.expr_type in (ExpressionType.PARAMETER, ExpressionType.VARIABLE) and expr.name in replacements:
        return _simplify_substituted_expression(replacements[expr.name], parameters)

    if expr.expr_type in (ExpressionType.BINARY_OP, ExpressionType.UNARY_OP, ExpressionType.CALL, ExpressionType.MEMORY):
        new_operands = [substitute_expression(op, replacements, parameters) for op in expr.operands]
        if all(new is old for new, old in zip(new_operands, expr.operands)):
            return _simplify_substituted_expression(expr, parameters)
        rebuilt = _clone_expression_with_operands(expr, new_operands)
        return _simplify_substituted_expression(rebuilt, parameters)

    if expr.expr_type == ExpressionType.PHI and expr.value:
        branches = []
        changed = False
        for cond, value in expr.value:
            new_cond = substitute_condition(cond, replacements, parameters) if cond is not None else None
            new_value = substitute_expression(value, replacements, parameters)
            branches.append((new_cond, new_value))
            changed = changed or (new_cond is not cond or new_value is not value)
        if not changed:
            return _simplify_substituted_expression(expr, parameters)
        rebuilt = Expression.phi(branches)
        rebuilt.size = expr.size
        return _simplify_substituted_expression(rebuilt, parameters)

    return expr


def _simplify_substituted_expression(
    expr: Expression,
    parameters: Optional[Sequence[Dict]] = None,
) -> Expression:
    if expr is None:
        return expr

    if expr.expr_type == ExpressionType.UNARY_OP and expr.operator == "BOOL_NEGATE" and expr.operands:
        truth_value = _expression_truth_value(expr.operands[0])
        if truth_value is not None:
            return Expression.constant(0 if truth_value else 1, size=1)
        return expr

    if expr.expr_type == ExpressionType.BINARY_OP and len(expr.operands) == 2:
        left = expr.operands[0]
        right = expr.operands[1]

        if expr.operator in {"INT_EQUAL", "INT_NOTEQUAL"}:
            known_truth = _known_nonnull_address_comparison_truth(
                expr.operator,
                left,
                right,
                parameters,
            )
            if known_truth is not None:
                return Expression.constant(1 if known_truth else 0, size=1)

        if expr.operator in {"BOOL_AND", "BOOL_OR", "BOOL_XOR"}:
            simplified_bool = _simplify_boolean_binary_expression(expr.operator, left, right)
            if simplified_bool is not None:
                return simplified_bool
        return expr

    if expr.expr_type == ExpressionType.PHI and expr.value:
        simplified_branches = []
        changed = False
        for cond, value in expr.value:
            if cond is None:
                simplified_branches.append((None, value))
                continue
            truth_value = ConditionSimplifier.evaluate_condition_truth(cond)
            if truth_value is False:
                changed = True
                continue
            if truth_value is True:
                return value
            simplified_branches.append((cond, value))

        if not simplified_branches:
            return expr
        if len(simplified_branches) == 1:
            only_cond, only_value = simplified_branches[0]
            if only_cond is None or changed:
                return only_value
        if not changed and len(simplified_branches) == len(expr.value):
            return expr
        rebuilt = Expression.phi(simplified_branches)
        rebuilt.size = expr.size
        return rebuilt

    return expr


def _expression_truth_value(expr: Optional[Expression]) -> Optional[bool]:
    if expr is None:
        return None
    return ConditionSimplifier.evaluate_condition_truth(Condition(expr, False))


def _simplify_boolean_binary_expression(
    operator: str,
    left: Expression,
    right: Expression,
) -> Optional[Expression]:
    left_truth = _expression_truth_value(left)
    right_truth = _expression_truth_value(right)

    if operator == "BOOL_AND":
        if left_truth is False or right_truth is False:
            return Expression.constant(0, size=1)
        if left_truth is True:
            return right
        if right_truth is True:
            return left
        return None

    if operator == "BOOL_OR":
        if left_truth is True or right_truth is True:
            return Expression.constant(1, size=1)
        if left_truth is False:
            return right
        if right_truth is False:
            return left
        return None

    if operator == "BOOL_XOR":
        if left_truth is not None and right_truth is not None:
            return Expression.constant(1 if left_truth ^ right_truth else 0, size=1)
        if left_truth is False:
            return right
        if right_truth is False:
            return left
        if left_truth is True:
            return Expression.unary_op("BOOL_NEGATE", right)
        if right_truth is True:
            return Expression.unary_op("BOOL_NEGATE", left)

    return None


def _known_nonnull_address_comparison_truth(
    operator: str,
    left: Expression,
    right: Expression,
    parameters: Optional[Sequence[Dict]],
) -> Optional[bool]:
    if operator not in {"INT_EQUAL", "INT_NOTEQUAL"}:
        return None
    if not parameters:
        parameters = []

    if _is_zero_constant(left) and _is_known_nonnull_stack_address(right, parameters):
        return operator == "INT_NOTEQUAL"
    if _is_zero_constant(right) and _is_known_nonnull_stack_address(left, parameters):
        return operator == "INT_NOTEQUAL"
    return None


def _is_zero_constant(expr: Optional[Expression]) -> bool:
    return (
        expr is not None
        and expr.expr_type == ExpressionType.CONSTANT
        and isinstance(expr.value, int)
        and int(expr.value) == 0
    )


def _is_known_nonnull_stack_address(
    expr: Optional[Expression],
    parameters: Sequence[Dict],
) -> bool:
    if expr is None:
        return False
    size = max(1, int(getattr(expr, "size", 0) or 0), 1)
    location = canonicalize_location(expr, parameters, size=size)
    if location is None:
        return False
    return location.base_param == _STACK_FRAME_LOCATION_BASE


def _collect_param_equalities(conditions: Sequence[Condition]) -> Set[frozenset]:
    equalities: Set[frozenset] = set()
    for condition in conditions:
        left, op, right, is_positive = ConditionNormalizer.normalize(condition)
        if is_positive and op == "INT_EQUAL" and left and right:
            equalities.add(frozenset((left, right)))
    return equalities


def _normalize_location_steps(steps: Sequence[LocationStep]) -> Tuple[LocationStep, ...]:
    normalized: List[LocationStep] = []
    for step in steps:
        if step.kind == "offset" and int(step.value) == 0:
            continue
        if normalized and normalized[-1].kind == "offset" and step.kind == "offset":
            combined = normalized[-1].value + int(step.value)
            normalized[-1] = LocationStep("offset", combined)
            if normalized[-1].value == 0:
                normalized.pop()
            continue
        normalized.append(LocationStep(step.kind, int(step.value)))
    return tuple(normalized)


def _location_step_sequence(location: CanonicalLocation) -> List[LocationStep]:
    steps: List[LocationStep] = list(getattr(location, "steps", ()) or ())
    if int(getattr(location, "offset", 0) or 0) != 0:
        steps.append(LocationStep("offset", int(location.offset)))
    return list(_normalize_location_steps(steps))


def _normalize_canonical_location(location: CanonicalLocation) -> CanonicalLocation:
    normalized_steps = list(_normalize_location_steps(_location_step_sequence(location)))
    final_offset = 0
    if normalized_steps and normalized_steps[-1].kind == "offset":
        final_offset = int(normalized_steps.pop().value)
    return CanonicalLocation(
        base_param=location.base_param,
        offset=final_offset,
        size=max(1, int(location.size or 0)),
        steps=tuple(normalized_steps),
    )


def _canonicalize_address_expression(
    expr: Expression,
    parameters: Sequence[Dict],
    size: int,
) -> Optional[CanonicalLocation]:
    parsed = _extract_location_root_and_steps(expr, parameters)
    if parsed is None:
        return None
    base_name, steps = parsed
    return _normalize_canonical_location(
        CanonicalLocation(
            base_param=base_name,
            offset=0,
            size=max(1, int(size or 0)),
            steps=tuple(steps),
        )
    )


def _extract_location_root_and_steps(
    expr: Expression,
    parameters: Sequence[Dict],
) -> Optional[Tuple[str, List[LocationStep]]]:
    if expr is None:
        return None

    if expr.expr_type in (ExpressionType.PARAMETER, ExpressionType.VARIABLE):
        resolved_base = _resolve_location_base_with_offset(expr, parameters)
        if resolved_base is None:
            return None
        base_name, base_offset = resolved_base
        steps: List[LocationStep] = []
        if int(base_offset) != 0:
            steps.append(LocationStep("offset", int(base_offset)))
        return base_name, steps

    if expr.expr_type == ExpressionType.UNARY_OP and expr.operator in {"INT_ZEXT", "INT_SEXT"} and expr.operands:
        return _extract_location_root_and_steps(expr.operands[0], parameters)

    if (
        expr.expr_type == ExpressionType.BINARY_OP
        and expr.operator == "SUBPIECE"
        and len(expr.operands) == 2
    ):
        source, offset = expr.operands
        if offset.expr_type == ExpressionType.CONSTANT and offset.value == 0:
            return _extract_location_root_and_steps(source, parameters)

    if expr.expr_type == ExpressionType.MEMORY and expr.operands:
        parsed = _extract_location_root_and_steps(expr.operands[0], parameters)
        if parsed is None:
            return None
        base_name, steps = parsed
        steps = list(steps)
        steps.append(LocationStep("deref", max(1, int(expr.size or 0))))
        return base_name, steps

    if (
        expr.expr_type == ExpressionType.BINARY_OP
        and expr.operator == "INT_ADD"
        and len(expr.operands) == 2
    ):
        left_const = _constant_factor(expr.operands[0])
        right_const = _constant_factor(expr.operands[1])
        if left_const is not None:
            parsed = _extract_location_root_and_steps(expr.operands[1], parameters)
            if parsed is None:
                return None
            base_name, steps = parsed
            steps = list(steps)
            steps.append(LocationStep("offset", int(left_const)))
            return base_name, steps
        if right_const is not None:
            parsed = _extract_location_root_and_steps(expr.operands[0], parameters)
            if parsed is None:
                return None
            base_name, steps = parsed
            steps = list(steps)
            steps.append(LocationStep("offset", int(right_const)))
            return base_name, steps
        return None

    if (
        expr.expr_type == ExpressionType.BINARY_OP
        and expr.operator == "INT_MULT"
        and len(expr.operands) == 2
    ):
        left_const = _constant_factor(expr.operands[0])
        right_const = _constant_factor(expr.operands[1])
        if left_const == 1:
            return _extract_location_root_and_steps(expr.operands[1], parameters)
        if right_const == 1:
            return _extract_location_root_and_steps(expr.operands[0], parameters)

    return None


def _flatten_param_addition(
    expr: Expression,
    parameters: Sequence[Dict],
) -> Tuple[Optional[int], List[str]]:
    const_total, bases = _flatten_location_addition(expr, parameters)
    if const_total is None:
        return None, []
    if not all(any(param.get("name") == base for param in parameters) for base in bases):
        return None, []
    return const_total, bases


def _flatten_location_addition(
    expr: Expression,
    parameters: Sequence[Dict],
) -> Tuple[Optional[int], List[str]]:
    if expr.expr_type in (ExpressionType.PARAMETER, ExpressionType.VARIABLE):
        resolved_base = _resolve_location_base_with_offset(expr, parameters)
        if resolved_base is not None:
            base_name, base_offset = resolved_base
            return base_offset, [base_name]

    if expr.expr_type == ExpressionType.UNARY_OP and expr.operator in {"INT_ZEXT", "INT_SEXT"} and expr.operands:
        return _flatten_location_addition(expr.operands[0], parameters)

    if (
        expr.expr_type == ExpressionType.BINARY_OP
        and expr.operator == "SUBPIECE"
        and len(expr.operands) == 2
    ):
        source, offset = expr.operands
        if offset.expr_type == ExpressionType.CONSTANT and offset.value == 0:
            return _flatten_location_addition(source, parameters)

    if (
        expr.expr_type == ExpressionType.BINARY_OP
        and expr.operator == "INT_ADD"
        and len(expr.operands) == 2
    ):
        left_const, left_bases = _flatten_location_addition(expr.operands[0], parameters)
        right_const, right_bases = _flatten_location_addition(expr.operands[1], parameters)
        if left_const is None or right_const is None:
            return None, []
        return left_const + right_const, left_bases + right_bases

    if (
        expr.expr_type == ExpressionType.BINARY_OP
        and expr.operator == "INT_MULT"
        and len(expr.operands) == 2
    ):
        left_const = _constant_factor(expr.operands[0])
        right_const = _constant_factor(expr.operands[1])
        if left_const == 1:
            return _flatten_location_addition(expr.operands[1], parameters)
        if right_const == 1:
            return _flatten_location_addition(expr.operands[0], parameters)

    if expr.expr_type == ExpressionType.CONSTANT and isinstance(expr.value, int):
        return expr.value, []

    return None, []


def _resolve_location_base_with_offset(
    expr: Expression,
    parameters: Sequence[Dict],
) -> Optional[Tuple[str, int]]:
    param_name = _resolve_parameter_name(expr, parameters)
    if param_name is not None:
        return param_name, 0

    if _is_stack_frame_base_expression(expr):
        return _STACK_FRAME_LOCATION_BASE, 0

    expr_storage = _coerce_storage_info(getattr(expr, "storage_info", None))
    if expr_storage is None:
        return None
    if not expr_storage.is_register and expr_storage.space_name == "stack":
        return _STACK_FRAME_LOCATION_BASE, int(expr_storage.offset)
    base_name = _synthetic_storage_base_name(expr_storage)
    if base_name is None:
        return None
    return base_name, 0


def _is_stack_frame_base_expression(expr: Optional[Expression]) -> bool:
    if expr is None:
        return False

    expr_storage = _coerce_storage_info(getattr(expr, "storage_info", None))
    register_candidates = []
    if expr_storage is not None and expr_storage.is_register:
        register_candidates.extend(
            [
                expr_storage.register_name,
                expr_storage.base_register_name,
            ]
        )

    if expr.expr_type == ExpressionType.VARIABLE and expr.name:
        register_candidates.append(expr.name)

    normalized = {
        StorageInfo._normalize_reg_name(candidate or "")
        for candidate in register_candidates
        if candidate
    }
    return bool(
        normalized.intersection(
            {
                "sp",
                "wsp",
                "rsp",
                "esp",
                "rbp",
                "ebp",
                "bp",
                "fp",
                "s8",
                "x29",
            }
        )
    )


def _resolve_parameter_name(expr: Expression, parameters: Sequence[Dict]) -> Optional[str]:
    if expr is None:
        return None

    if expr.name:
        for param in parameters:
            if param.get("name") == expr.name:
                return expr.name

    expr_storage = _coerce_storage_info(getattr(expr, "storage_info", None))
    if expr_storage is None:
        return None

    matches: List[str] = []
    for param in parameters:
        param_name = param.get("name")
        param_storage = _coerce_storage_info(param.get("storage"))
        if not param_name or param_storage is None:
            continue
        if _storage_matches_parameter(expr_storage, param_storage):
            matches.append(param_name)

    if len(matches) == 1:
        return matches[0]
    return None


def _coerce_storage_info(storage: Optional[object]) -> Optional[StorageInfo]:
    if storage is None:
        return None
    if isinstance(storage, StorageInfo):
        return storage
    if isinstance(storage, dict):
        try:
            return StorageInfo(
                is_register=bool(storage.get("is_register", False)),
                space_name=str(storage.get("space_name", "")),
                offset=int(storage.get("offset", 0)),
                size=int(storage.get("size", 0)),
                size_bits=int(storage.get("size_bits", 0)),
                register_name=storage.get("register_name"),
                base_register_name=storage.get("base_register_name"),
                base_register_offset=int(storage.get("base_register_offset", 0)),
                base_register_size=int(storage.get("base_register_size", 0)),
                base_register_size_bits=int(storage.get("base_register_size_bits", 0)),
                bit_offset_in_base=int(storage.get("bit_offset_in_base", 0)),
            )
        except Exception:
            return None
    return None


def _storage_matches_parameter(expr_storage: StorageInfo, param_storage: StorageInfo) -> bool:
    if expr_storage.is_register and param_storage.is_register:
        if expr_storage.shares_base_register_with(param_storage):
            expr_low = expr_storage.bit_offset_in_base
            expr_high = expr_low + max(0, int(expr_storage.size_bits or 0))
            param_low = param_storage.bit_offset_in_base
            param_high = param_low + max(0, int(param_storage.size_bits or 0))
            if expr_high <= expr_low or param_high <= param_low:
                return (
                    StorageInfo._normalize_reg_name(expr_storage.register_name or "")
                    == StorageInfo._normalize_reg_name(param_storage.register_name or "")
                )
            # Only treat a register-backed value as "the same parameter" when all
            # of the value's bits are contained within the parameter fragment.
            # Mere overlap is too permissive on architectures like MIPS64 where
            # `a0` and `a0_lo` share a base register but mean different things.
            return param_low <= expr_low and expr_high <= param_high
        return (
            StorageInfo._normalize_reg_name(expr_storage.register_name or "")
            == StorageInfo._normalize_reg_name(param_storage.register_name or "")
        )

    return (
        expr_storage.space_name == param_storage.space_name
        and expr_storage.offset == param_storage.offset
        and expr_storage.size == param_storage.size
    )


def _constant_factor(expr: Expression) -> Optional[int]:
    value = _evaluate_constant_expression(expr)
    if value is None:
        return None
    return int(value)


def _concat(left: Expression, right: Expression) -> Expression:
    result = Expression.binary_op("PIECE", left, right)
    result.size = (left.size or 0) + (right.size or 0)
    return result


def _has_overlapping_guards(matched: Sequence[Tuple[int, List[Condition], Expression]]) -> bool:
    for i in range(len(matched)):
        for j in range(i + 1, len(matched)):
            residual_i = list(matched[i][1])
            residual_j = list(matched[j][1])
            if not residual_i or not residual_j:
                return True
            if not ConditionSimplifier.is_contradiction(residual_i + residual_j):
                return True
    return False


def _all_residual_guards_empty(matched: Sequence[Tuple[int, List[Condition], Expression]]) -> bool:
    return all(not list(residual) for _order, residual, _value in matched)


def _get_order_key(op) -> int:
    seq = op.getSeqnum()
    if seq is None:
        return 0
    target = seq.getTarget()
    return (target.getOffset() << 8) | seq.getOrder()

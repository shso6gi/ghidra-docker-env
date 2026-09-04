"""Parameter identity keys, summary parameter references and auxiliary semantic hints."""

from __future__ import annotations

from typing import Any, Dict, List, Mapping, Optional, Sequence, Tuple
from scripts.function_tracer_pcode.core import Expression, ExpressionType, StorageInfo
from scripts.function_tracer_pcode.core.render_smt import expression_smt_bit_width
from scripts.function_tracer_pcode.proof.strategies.pairwise_services._shared import (
    ParameterInfo,
)


def _impl__collect_summary_parameter_refs(self, *expressions: Any) -> Tuple[Any, ...]:
    refs: List[Tuple[Any, ...]] = []
    seen = set()
    for expr in expressions:
        for parameter in self._collect_parameter_expression_nodes(expr):
            name = str(getattr(parameter, "name", "") or "")
            raw_index = getattr(parameter, "value", None)
            try:
                index = int(raw_index)
            except (TypeError, ValueError):
                index = None
            if not (name.startswith("summary_rec_") or (index is not None and index >= 10000)):
                continue
            item = (
                "summary_parameter",
                ("index", index),
                ("name", name or None),
                ("bit_width", int(expression_smt_bit_width(parameter) or 0) or None),
                ("expression", self._expression_runtime_object_key(parameter)),
            )
            if item in seen:
                continue
            seen.add(item)
            refs.append(item)
    return tuple(sorted(refs, key=repr))


def _impl__collect_parameter_expression_nodes(self, expr: Any) -> Tuple[Any, ...]:
    result: List[Any] = []
    self._collect_parameter_expression_nodes_into(expr, result)
    return tuple(result)


def _impl__collect_parameter_expression_nodes_into(self, expr: Any, result: List[Any]) -> None:
    if expr is None or getattr(expr, "expr_type", None) is None:
        return
    if expr.expr_type == ExpressionType.PARAMETER:
        result.append(expr)
        return
    if expr.expr_type == ExpressionType.PHI and expr.value:
        for condition, value in expr.value:
            if condition is not None:
                self._collect_parameter_expression_nodes_into(condition.expression, result)
            self._collect_parameter_expression_nodes_into(value, result)
        return
    for operand in getattr(expr, "operands", []) or []:
        self._collect_parameter_expression_nodes_into(operand, result)


def _impl__auxiliary_semantic_parameter_sources(
    self,
    base_ctx: Optional[Mapping[str, Any]],
) -> Tuple[ParameterInfo, ...]:
    if not isinstance(base_ctx, Mapping):
        return ()
    sources: List[ParameterInfo] = []
    for key in ("params1", "params2"):
        for param in base_ctx.get(key, ()) or ():
            if isinstance(param, ParameterInfo):
                sources.append(param)
    return tuple(sources)


def _impl__auxiliary_semantic_hints_by_index(
    self,
    semantic_parameter_sources: Sequence[ParameterInfo],
) -> Dict[int, Tuple[int, str, int]]:
    hints: Dict[int, Tuple[int, str, int]] = {}
    for source in semantic_parameter_sources or ():
        try:
            index = int(getattr(source, "index"))
            bit_width = int(getattr(source, "bit_width"))
            narrow_bits = getattr(source, "semantic_narrow_bits", None)
            narrow_bits = int(narrow_bits) if narrow_bits is not None else None
        except (TypeError, ValueError):
            continue
        signedness = getattr(source, "semantic_signedness", None)
        if bit_width <= 0 or narrow_bits is None or narrow_bits <= 0:
            continue
        if narrow_bits >= bit_width or signedness not in {"signed", "unsigned"}:
            continue
        current = hints.get(index)
        if current is None or bit_width > current[2]:
            hints[index] = (narrow_bits, signedness, bit_width)
    return hints


def _impl__apply_auxiliary_semantic_hint(
    self,
    candidate: Dict[str, Any],
    *,
    size: int,
    semantic_by_index: Mapping[int, Tuple[int, str, int]],
) -> None:
    try:
        index = int(candidate.get("index"))
        bit_width = max(1, int(size)) * 8
    except (TypeError, ValueError):
        return
    hint = semantic_by_index.get(index)
    if hint is None:
        return
    narrow_bits, signedness, source_bit_width = hint
    if source_bit_width != bit_width or narrow_bits >= bit_width:
        return
    candidate["semantic_narrow_bits"] = int(narrow_bits)
    candidate["semantic_signedness"] = signedness


def _impl__build_auxiliary_parameter_infos(
    self,
    symbol_specs: Sequence[Dict[str, Any]],
) -> List[ParameterInfo]:
    infos: List[ParameterInfo] = []
    for spec in sorted(
        symbol_specs or [],
        key=lambda item: (
            self._auxiliary_identity_sort_key(item.get("identity")),
            int(item.get("size", 0) or 0),
        ),
    ):
        aux_name = str(spec.get("aux_name") or "")
        if not aux_name:
            continue
        infos.append(
            ParameterInfo(
                original_name=aux_name,
                smt_name=aux_name,
                bit_width=max(1, int(spec.get("size", 0) or 4)) * 8,
                index=int(spec.get("aux_index", -1) or -1),
                is_signed=bool(spec.get("is_signed", True)),
                semantic_narrow_bits=(
                    int(spec["semantic_narrow_bits"])
                    if spec.get("semantic_narrow_bits") is not None
                    else None
                ),
                semantic_signedness=spec.get("semantic_signedness"),
            )
        )
    return infos


def _impl__auxiliary_identity_sort_key(self, identity) -> Tuple[int, str]:
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
    return (8, repr(identity))


def _impl__clone_auxiliary_residue_bias_terms(
    self,
    bias_terms: Sequence[Tuple[int, int, Any]],
    identity_to_spec: Dict[Tuple[object, ...], Dict[str, Any]],
) -> Optional[Tuple[Tuple[int, int, Any], ...]]:
    cloned_terms = []
    for modulus, residue, bias_expr in bias_terms:
        cloned_bias_expr = self._clone_auxiliary_expression_for_smt(
            bias_expr,
            identity_to_spec,
        )
        if cloned_bias_expr is None:
            return None
        cloned_terms.append((int(modulus), int(residue), cloned_bias_expr))
    return tuple(cloned_terms)


def _impl__storage_info_from_parameter_descriptor(self, parameter: Dict[str, Any]) -> Optional[StorageInfo]:
    storage = parameter.get("storage_info", parameter.get("storage")) if isinstance(parameter, dict) else None
    if isinstance(storage, StorageInfo):
        return storage
    if isinstance(storage, dict):
        try:
            return StorageInfo(**storage)
        except Exception:
            return None
    return None


def _impl__parameter_descriptor_storage_identity_key(self, parameter: Dict[str, Any]) -> Optional[tuple]:
    storage_info = self._storage_info_from_parameter_descriptor(parameter)
    storage_key_fn = getattr(storage_info, "storage_identity_key", None)
    if not callable(storage_key_fn):
        return None
    try:
        storage_key = storage_key_fn()
    except (AttributeError, TypeError, ValueError):
        return None
    if storage_key is None:
        return None
    return ("parameter_storage", tuple(storage_key))


def _impl__parameter_descriptor_index_identity_key(self, parameter: Dict[str, Any]) -> Optional[tuple]:
    if not isinstance(parameter, dict):
        return None
    try:
        index = parameter.get("index")
        if index is not None and int(index) >= 0:
            return ("parameter", int(index))
    except (TypeError, ValueError):
        return None
    return None


def _impl__parameter_descriptor_identity_keys(self, parameter: Dict[str, Any]) -> set[tuple]:
    identities: set[tuple] = set()
    if not isinstance(parameter, dict):
        return identities
    try:
        index = parameter.get("index")
        if index is not None and int(index) >= 0:
            identities.add(("parameter", int(index)))
    except (TypeError, ValueError):
        pass
    storage_info = self._storage_info_from_parameter_descriptor(parameter)
    storage_key_fn = getattr(storage_info, "storage_identity_key", None)
    if callable(storage_key_fn):
        try:
            storage_key = storage_key_fn()
        except (AttributeError, TypeError, ValueError):
            storage_key = None
        if storage_key is not None:
            identities.add(("parameter_storage", tuple(storage_key)))
    return identities


def _impl__parameter_expression_storage_identity_key(self, expr: Expression) -> Optional[tuple]:
    storage_info = getattr(expr, "storage_info", None)
    storage_key_fn = getattr(storage_info, "storage_identity_key", None)
    if not callable(storage_key_fn):
        return None
    try:
        storage_key = storage_key_fn()
    except (AttributeError, TypeError, ValueError):
        return None
    if storage_key is None:
        return None
    return ("parameter_storage", tuple(storage_key))


def _impl__parameter_expression_index_identity_key(self, expr: Expression) -> Optional[tuple]:
    try:
        index = getattr(expr, "value", None)
        if index is not None and int(index) >= 0:
            return ("parameter", int(index))
    except (TypeError, ValueError):
        return None
    return None


def _impl__parameter_expression_identity_keys(self, expr: Expression) -> set[tuple]:
    identities: set[tuple] = set()
    try:
        index = getattr(expr, "value", None)
        if index is not None and int(index) >= 0:
            identities.add(("parameter", int(index)))
    except (TypeError, ValueError):
        pass
    storage_info = getattr(expr, "storage_info", None)
    storage_key_fn = getattr(storage_info, "storage_identity_key", None)
    if callable(storage_key_fn):
        try:
            storage_key = storage_key_fn()
        except (AttributeError, TypeError, ValueError):
            storage_key = None
        if storage_key is not None:
            identities.add(("parameter_storage", tuple(storage_key)))
    return identities

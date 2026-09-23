"""Parameter identity keys, summary parameter references and auxiliary entailed extensions."""

from __future__ import annotations

from typing import Any, Dict, List, Mapping, Optional, Sequence, Tuple
from scripts.function_tracer_pcode.core import Expression, ExpressionType, StorageInfo
from scripts.function_tracer_pcode.core.render_smt import expression_smt_bit_width
from scripts.function_tracer_pcode.proof.strategies.pairwise_services._shared import (
    ParameterInfo,
)
from scripts.function_tracer_pcode.semantics.rewrite_contract import RewriteAssumption


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


def _impl__auxiliary_entailed_extensions_by_index(
    self,
    semantic_parameter_sources: Sequence[ParameterInfo],
) -> Dict[int, RewriteAssumption]:
    """補助 query の symbol へ引き継ぐ入力 extension 仮定。

    最終 ``InputCorrespondence`` が含意した ``ParameterInfo.entailed_extension``
    だけを使う。semantic hint（単一 use の射影主張）は入力全体の仮定ではないので
    読まない（Issue #167）。補助 query の symbol は (index, 幅) が同じなら左右
    どちらの parameter にもなり得るので、その (index, 幅) の **全ての** source が
    同じ仮定を含意するときだけ引き継ぐ（片側だけの含意を他方へ持ち込まない）。
    """
    by_slot: Dict[Tuple[int, int], List[Optional[RewriteAssumption]]] = {}
    for source in semantic_parameter_sources or ():
        try:
            slot = (int(getattr(source, "index")), int(getattr(source, "bit_width")))
        except (TypeError, ValueError):
            continue
        by_slot.setdefault(slot, []).append(getattr(source, "entailed_extension", None))
    extensions: Dict[int, RewriteAssumption] = {}
    for (index, bit_width), assumptions in sorted(by_slot.items()):
        first = assumptions[0]
        if first is None or first.parameter_bits != bit_width:
            continue
        if any(assumption != first for assumption in assumptions):
            continue
        current = extensions.get(index)
        if current is None or first.parameter_bits > current.parameter_bits:
            extensions[index] = first
    return extensions


def _impl__apply_auxiliary_entailed_extension(
    self,
    candidate: Dict[str, Any],
    *,
    size: int,
    extensions_by_index: Mapping[int, RewriteAssumption],
) -> None:
    try:
        index = int(candidate.get("index"))
        bit_width = max(1, int(size)) * 8
    except (TypeError, ValueError):
        return
    assumption = extensions_by_index.get(index)
    if assumption is None or assumption.parameter_bits != bit_width:
        return
    candidate["entailed_extension"] = assumption


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
                entailed_extension=spec.get("entailed_extension"),
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

"""Deferred-call and unknown-value references."""

from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass, replace
from typing import Any, Dict, Iterable, List, Mapping, Optional, Tuple
from scripts.function_tracer_pcode.core.live_values import (
    NOT_PLAIN,
    as_bool,
    as_int,
    attribute,
    elements_of,
    str_value,
    type_module,
    type_name,
)
from scripts.function_tracer_pcode.core.read_limits import elements_within_limit, scan_budget
from scripts.function_tracer_pcode.core.json_encoding import (
    as_list, builtin_str, inline, is_json_record, materialize, raw,
)
from scripts.function_tracer_pcode.core.call_target import CallTargetRef, coerce_call_target_ref
from scripts.function_tracer_pcode.core.runtime_refs.pcode import (
    PcodeOpRef,
)


@dataclass(frozen=True)
class DeferredCallRef:
    """Structured identity for a deferred call site."""

    caller_program_id: Optional[int] = None
    caller_entry_offset: Optional[int] = None
    pcode_op_ref: Optional[PcodeOpRef] = None
    target_ref: Optional[CallTargetRef] = None
    sequence: Optional[int] = None

    def __post_init__(self) -> None:
        object.__setattr__(self, "target_ref", coerce_call_target_ref(self.target_ref))

    def stable_key(self) -> Tuple[Any, ...]:
        return (
            "deferred_call_site",
            self.caller_program_id,
            self.caller_entry_offset,
            self.pcode_op_ref.stable_key() if self.pcode_op_ref is not None else None,
            self.target_ref.stable_key() if self.target_ref is not None else None,
            self.sequence,
        )

    def display_name(self) -> str:
        # field は owner の API / 型を確かめた package の method で読む（live な値の code を呼ばない）
        target = self.target_ref
        target_name = _call_target_display_name(target) if target is not None else "unknown"
        op = self.pcode_op_ref
        if op is not None:
            offset = op.address_offset if type(op) is PcodeOpRef else attribute(op, "address_offset")
            if offset is not None:
                return f"{builtin_str(target_name)}@0x{as_int(offset):x}"
        return target_name

    def json_items(self):
        yield "kind", "deferred_call_site"
        yield "caller_program_id", self.caller_program_id
        yield "caller_entry_offset", self.caller_entry_offset
        yield "pcode_op_ref", self.pcode_op_ref if self.pcode_op_ref is not None else None
        yield "target_ref", self.target_ref if self.target_ref is not None else None
        yield "sequence", self.sequence
        yield "display_name", self.display_name()

    def to_dict(self) -> Dict[str, Any]:
        return materialize(self)


def _call_target_display_name(target: Any) -> Any:
    """`target.display_name()`（`__post_init__` が正規化した `CallTargetRef` だけ。それ以外は `TypeError`）。"""

    if type(target) is CallTargetRef:
        return target.display_name()
    raise TypeError(f"{type_name(type(target))} is not a CallTargetRef")


def _deferred_call_display_name(ref: Any) -> Any:
    """`ref.display_name()`（`DeferredCallRef` だけ。それ以外は `TypeError`。live な値の method を呼ばない）。"""

    if type(ref) is DeferredCallRef:
        return ref.display_name()
    raise TypeError(f"{type_name(type(ref))} is not a DeferredCallRef")


def _runtime_ref_stable_key_or_repr(value: Any) -> Optional[Tuple[Any, ...]]:
    if value is None:
        return None
    stable_key = getattr(value, "stable_key", None)
    if callable(stable_key):
        try:
            key = stable_key()
        except (AttributeError, TypeError, ValueError, RecursionError):
            key = None
        if key is not None:
            return ("stable", key)
    return ("repr", type(value).__module__, type(value).__qualname__, repr(value))


def _runtime_ref_origin_source(value: Any) -> Tuple[Any, ...]:
    """出力の `origin_ref`（record でない origin の型だけ。identity・`repr` を bounded path で作らない）。

    origin の identity（`stable_key` / `repr`）は `UnknownValueRef.stable_key` の側（#194）が持つ。
    """

    kind = type(value)
    return ("ref", type_module(kind), type_name(kind))


@dataclass(frozen=True)
class UnknownValueRef:
    """Structured identity for UNKNOWN expressions used at runtime."""

    kind: str
    reason: Optional[str] = None
    target_ref: Optional[CallTargetRef] = None
    deferred_call_ref: Optional[DeferredCallRef] = None
    origin_kind: Optional[str] = None
    origin_ref: Optional[Any] = None
    display_hint: Optional[str] = None

    def __post_init__(self) -> None:
        normalized_target = coerce_call_target_ref(self.target_ref)
        object.__setattr__(self, "target_ref", normalized_target)

    @classmethod
    def deferred_call(
        cls,
        *,
        deferred_call_ref: Optional[DeferredCallRef] = None,
        target_ref=None,
        placeholder_name: Optional[str] = None,
        sequence: Optional[int] = None,
        deferred_key: Optional[Tuple[Any, ...]] = None,
    ) -> "UnknownValueRef":
        # `coerce_call_target_ref` は `CallTargetRef`（真偽を上書きしない record）か `None` を返す
        normalized = coerce_call_target_ref(target_ref)
        if normalized is None:
            normalized = CallTargetRef.unknown()
        normalized_ref = deferred_call_ref
        if normalized_ref is None:
            normalized_ref = DeferredCallRef(
                target_ref=normalized,
                sequence=sequence,
            )
        display_hint = placeholder_name or _deferred_call_display_name(normalized_ref)
        return cls(
            kind="deferred_call",
            reason="call_out_of_scope",
            target_ref=normalized,
            deferred_call_ref=normalized_ref,
            display_hint=display_hint,
        )

    @classmethod
    def out_of_scope_call(
        cls,
        *,
        reason: str,
        target_ref=None,
        display_hint: Optional[str] = None,
    ) -> "UnknownValueRef":
        normalized = coerce_call_target_ref(target_ref)
        return cls(
            kind="call_target",
            reason=reason,
            target_ref=normalized,
            display_hint=display_hint,
        )

    @classmethod
    def budget_exceeded(
        cls,
        *,
        operation: Optional[str] = None,
        origin_kind: Optional[str] = None,
        origin_ref: Optional[Any] = None,
    ) -> "UnknownValueRef":
        reason = f"{operation}_budget_exceeded" if operation else "budget_exceeded"
        return cls(
            kind="budget_exceeded",
            reason=reason,
            origin_kind=origin_kind,
            origin_ref=origin_ref,
            display_hint=reason,
        )

    @classmethod
    def opaque(
        cls,
        *,
        reason: Optional[str] = None,
        display_hint: Optional[str] = None,
        origin_kind: Optional[str] = None,
        origin_ref: Optional[Any] = None,
    ) -> "UnknownValueRef":
        normalized_reason = reason or "unknown"
        return cls(
            kind="opaque_unknown",
            reason=normalized_reason,
            origin_kind=origin_kind,
            origin_ref=origin_ref,
            display_hint=display_hint or normalized_reason,
        )

    @classmethod
    def phi_circular(
        cls,
        *,
        pcode_op_ref: Optional[Any] = None,
        display_hint: str = "phi_circular",
    ) -> "UnknownValueRef":
        return cls.opaque(
            reason="phi_circular",
            display_hint=display_hint,
            origin_kind="multiequal_pcode_op",
            origin_ref=pcode_op_ref,
        )

    def stable_key(self) -> Tuple[Any, ...]:
        target_key = self.target_ref.stable_key() if self.target_ref is not None else None
        origin_key = None
        stable_key = getattr(self.origin_ref, "stable_key", None)
        if callable(stable_key):
            try:
                candidate_key = stable_key()
            except (AttributeError, TypeError, ValueError, RecursionError):
                candidate_key = None
            if candidate_key is not None:
                origin_key = ("stable", candidate_key)
        return (
            self.kind,
            self.reason,
            target_key,
            self.deferred_call_ref.stable_key() if self.deferred_call_ref is not None else None,
            self.origin_kind,
            origin_key,
        )

    def diagnostic_key(self) -> Tuple[Any, ...]:
        key = self.stable_key()
        if self.origin_kind is None and self.origin_ref is None:
            return key
        return key + (("diagnostic_origin", _runtime_ref_stable_key_or_repr(self.origin_ref)),)

    def display_name(self) -> str:
        # field の真偽は owner の API、参照先の名前は型を確かめた package の method で読む
        hint = self.display_hint
        if as_bool(hint):
            return hint
        deferred = self.deferred_call_ref
        if deferred is not None:
            return _deferred_call_display_name(deferred)
        target = self.target_ref
        if target is not None:
            return _call_target_display_name(target)
        reason = self.reason
        return reason if as_bool(reason) else "unknown"

    def json_items(self):
        yield "kind", self.kind
        yield "display_name", self.display_name()
        if self.reason is not None:
            yield "reason", self.reason
        if self.deferred_call_ref is not None:
            yield "deferred_call_ref", self.deferred_call_ref
        if self.target_ref is not None:
            yield "target_ref", self.target_ref
        if self.origin_kind is not None:
            yield "origin_kind", self.origin_kind
        if self.origin_ref is not None:
            if is_json_record(self.origin_ref):
                yield "origin_ref", self.origin_ref
            else:
                # 固定個数の要素から成る identity（stable key か、型と有界な repr）。出力の側は
                # live な値の `repr` を呼ばない（identity の側 `stable_key` は旧実装のまま）
                yield "origin_ref", raw(_runtime_ref_origin_source(self.origin_ref))

    def to_dict(self) -> Dict[str, Any]:
        return materialize(self)


# ---------------------------------------------------------------------------
# Issue #131 PR-A: expansion/path budget truncation observation.
#
# 展開ケース数・経路数の上限で実際に切り捨てが起きた事実だけを記録する値型。
# 生成側は判定方針を持たず、消費側（PR-B）が fail-closed 判断に使う。
# ---------------------------------------------------------------------------

_EXPANSION_BUDGET_TRUNCATION_KEY_VERSION = "expansion_budget_truncation_v1"

EXPANSION_BUDGET_TRUNCATION_KINDS = frozenset({
    "dedup_case_limit",
    "path_limit",
    "condition_limit",
    "callee_analysis",
})

# Issue #131 PR-B: 切り捨てが観測された関数を判定へ倒すための登録 reason。
# 解析面（``FunctionReturnAnalysis`` の marker）と効果面（``EffectSummary`` の
# ``incomplete_reasons``）で ID を分け、効果面は既存の効果不完全性処理へ写像する。
EXPANSION_CASE_BUDGET_EXCEEDED_REASON = "expansion_case_budget_exceeded"
EFFECT_EXPANSION_CASE_BUDGET_EXCEEDED_REASON = "effect_expansion_case_budget_exceeded"


EXPANSION_BUDGET_TRUNCATION_SURFACES = frozenset({
    "return_value",
    "branch_condition",
    "store_value",
    "call_wrapper",
    "callee",
})


_CANONICAL_BUDGET_MAX_DEPTH = 12


def _canonical_budget_value(value: Any, depth: int = 0) -> Any:
    """決定的な JSON 化（producer 時点の identity: `stable_key` / `event_id`）。

    ``hash()``・オブジェクトアドレス・既定 ``repr`` には依存しない。表現できない
    object は型名だけの不透明値へ落とす（同一性を持ち込まない）。``stable_key`` が
    自分と同種の object を返し続ける実装（テスト用 Mock など）でも止まるよう、
    深さで打ち切る。

    Issue #22 PR-22-D: identity の構築（owner は #194）で、bounded path ではない。規則を
    変えない。`ExpansionBudgetTruncation` は構築のときにこの値を 1 度だけ作り、出力はその写し
    （組み込みの値だけの値）を読むだけ（bounded path で identity を組み立てない）。
    """

    if value is None or isinstance(value, (bool, int, str)):
        return value
    if depth >= _CANONICAL_BUDGET_MAX_DEPTH:
        return ["depth_limited", type(value).__module__, type(value).__qualname__]
    if isinstance(value, float):
        return repr(value)
    if isinstance(value, bytes):
        return ["bytes", value.hex()]
    if isinstance(value, (list, tuple)):
        return [_canonical_budget_value(item, depth + 1) for item in value]
    if isinstance(value, (set, frozenset)):
        return sorted(
            (_canonical_budget_value(item, depth + 1) for item in value),
            key=lambda item: json.dumps(item, ensure_ascii=False, sort_keys=True),
        )
    if isinstance(value, Mapping):
        return {
            str(key): _canonical_budget_value(item, depth + 1)
            for key, item in sorted(value.items(), key=lambda pair: str(pair[0]))
        }
    stable_key = getattr(value, "stable_key", None)
    if callable(stable_key):
        try:
            key = stable_key()
        except (AttributeError, TypeError, ValueError, RecursionError):
            key = None
        if key is not None:
            return ["stable", _canonical_budget_value(key, depth + 1)]
    return ["opaque", type(value).__module__, type(value).__qualname__]


def _canonical_budget_json(payload: Any) -> str:
    return json.dumps(
        _canonical_budget_value(payload),
        ensure_ascii=False,
        sort_keys=True,
        separators=(",", ":"),
    )


@dataclass(frozen=True)
class ExpansionBudgetTruncation:
    """1 件の切り捨て事実。

    ``kind`` に対応しない件数欄は ``None`` のままにする（取得できない件数を推定値で
    埋めない）。``event_id`` は発生事実キーの SHA-256 で、``referenced_event_ids`` の
    内容は含めない（参照先の履歴が再帰的に積み上がらないようにする）。
    """

    kind: str
    surface: Optional[str] = None
    owner_scope_key: Optional[Tuple[Any, ...]] = None
    label: Optional[str] = None
    pcode_op_ref: Optional[PcodeOpRef] = None
    dedup: Optional[Tuple[int, int, int]] = None
    paths: Optional[Tuple[int, int, int]] = None
    conditions: Optional[Tuple[int, int]] = None
    callee_scope_key: Optional[Tuple[Any, ...]] = None
    referenced_event_ids: Tuple[str, ...] = ()

    def __post_init__(self) -> None:
        object.__setattr__(self, "kind", str(self.kind))
        if self.surface is not None:
            object.__setattr__(self, "surface", str(self.surface))
        if self.label is not None:
            object.__setattr__(self, "label", str(self.label))
        for name in ("dedup", "paths", "conditions"):
            counts = getattr(self, name)
            if counts is None:
                continue
            object.__setattr__(self, name, tuple(int(item) for item in counts))
        object.__setattr__(
            self,
            "referenced_event_ids",
            tuple(sorted({str(item) for item in (self.referenced_event_ids or ())})),
        )
        # identity（owner #194 の規則 `_canonical_budget_value`）は構築のときに 1 度だけ作る。
        # 出力（`json_items`）はこの写し（組み込みの値だけの値）を読むだけで、bounded path で
        # identity を組み立てない（Issue #22 PR-22-D）
        object.__setattr__(self, "_owner_scope_value", _canonical_budget_value(self.owner_scope_key))
        object.__setattr__(self, "_callee_scope_value", _canonical_budget_value(self.callee_scope_key))
        object.__setattr__(self, "_event_id_cache", hashlib.sha256(
            _canonical_budget_json(self.stable_key()).encode("utf-8")
        ).hexdigest())

    def stable_key(self) -> Tuple[Any, ...]:
        """発生事実キー。``event_id`` と参照先 event の内容は含めない。"""

        return (
            _EXPANSION_BUDGET_TRUNCATION_KEY_VERSION,
            self.kind,
            self.surface,
            self._owner_scope_value,
            self.label,
            _canonical_budget_value(self.pcode_op_ref),
            self.dedup,
            self.paths,
            self.conditions,
            self._callee_scope_value,
        )

    @property
    def event_id(self) -> str:
        return self._event_id_cache

    def with_binding(
        self,
        *,
        surface: Optional[str] = None,
        owner_scope_key: Optional[Tuple[Any, ...]] = None,
    ) -> "ExpansionBudgetTruncation":
        """利用面・所有 scope を sink 側で束縛する（生成側は原因だけを持つ）。

        既に束縛済みの欄は上書きしない。生成側が原因だけを返し、利用側がその原因と
        利用箇所を結び付ける、という役割分担を型で守るため。
        """

        bound_surface = self.surface if self.surface is not None else surface
        bound_owner = (
            self.owner_scope_key if self.owner_scope_key is not None else owner_scope_key
        )
        if bound_surface == self.surface and bound_owner == self.owner_scope_key:
            return self
        return replace(self, surface=bound_surface, owner_scope_key=bound_owner)

    def json_items(self):
        yield "event_id", self.event_id
        yield "kind", self.kind
        if self.surface is not None:
            yield "surface", self.surface
        if self.owner_scope_key is not None:
            # 構築のときの identity の写し（組み込みの値だけ。walker が要素ごとに数える）
            yield "owner_scope_key", self._owner_scope_value
        if self.label is not None:
            yield "label", self.label
        if self.pcode_op_ref is not None:
            yield "pcode_op_ref", self.pcode_op_ref
        # 件数の欄は `__post_init__` が組み込みの tuple に正規化済み（型を確かめてから添字で読む）
        dedup = self.dedup
        if type(dedup) is tuple:
            yield "dedup", inline(
                ("candidate_count", dedup[0]),
                ("kept_count", dedup[1]),
                ("limit", dedup[2]),
            )
        paths = self.paths
        if type(paths) is tuple:
            yield "paths", inline(
                ("valid_path_count", paths[0]),
                ("kept_path_count", paths[1]),
                ("limit_paths", paths[2]),
            )
        conditions = self.conditions
        if type(conditions) is tuple:
            yield "conditions", inline(
                ("dropped_path_count", conditions[0]),
                ("max_conditions", conditions[1]),
            )
        if self.callee_scope_key is not None:
            yield "callee_scope_key", self._callee_scope_value
        if as_bool(self.referenced_event_ids):
            yield "referenced_event_ids", as_list(self.referenced_event_ids)

    def to_dict(self) -> Dict[str, Any]:
        return materialize(self)


def normalize_expansion_budget_truncations(
    items: Optional[Iterable[ExpansionBudgetTruncation]],
) -> Tuple[ExpansionBudgetTruncation, ...]:
    """``event_id`` で同じ発生事実をまとめ、参照 ID を和集合にして順序を正規化する。

    ID 集合が同じでも参照情報が増えた場合は別の値になる（更新として扱えるように
    するため）。
    """

    # record の値は owner の規則で読む（event id は構築のときに作った文字列、参照 ID は文字列の列）
    merged: Dict[str, ExpansionBudgetTruncation] = {}
    references: Dict[str, Tuple[str, ...]] = {}
    # 記録と参照 ID の和は owner の固定の上限まで（作業量を受け取らない正規化。超えれば `TypeError`）
    scan = scan_budget()
    for item in (() if items is None else elements_within_limit(items, scan)):
        if item is None:
            continue
        if type(item) is not ExpansionBudgetTruncation:
            raise TypeError("expansion budget truncations are ExpansionBudgetTruncation only")
        event_id = _plain_event_id(item._event_id_cache)
        referenced = tuple(
            _plain_event_id(ref) for ref in elements_within_limit(item.referenced_event_ids, scan)
        )
        current = merged.get(event_id)
        if current is None:
            merged[event_id] = item
            references[event_id] = referenced
            continue
        known = references[event_id]
        union = tuple(sorted(set(known) | set(referenced)))
        if union != known:
            merged[event_id] = replace(current, referenced_event_ids=union)
            references[event_id] = union
    return tuple(merged[event_id] for event_id in sorted(references))


def _plain_event_id(value: Any) -> str:
    """event id（組み込みの `str` の値。それ以外は `TypeError`）。"""

    text = str_value(value)
    if text is NOT_PLAIN:
        raise TypeError("an expansion budget event id is a str")
    return text


def merge_expansion_budget_truncations(
    *groups: Optional[Iterable[ExpansionBudgetTruncation]],
) -> Tuple[ExpansionBudgetTruncation, ...]:
    """複数の記録源を和集合にする（既存記録を空の記録源で消さない）。"""

    combined: List[ExpansionBudgetTruncation] = []
    for group in groups:
        if group is None:
            continue
        # 記録源は組み込みの列（owner の API で要素を読む。live な値の `__iter__` / `__bool__` を呼ばない）
        combined.extend(item for item in elements_within_limit(group) if item is not None)
    return normalize_expansion_budget_truncations(combined)


def expansion_budget_event_ids(
    items: Optional[Iterable[ExpansionBudgetTruncation]],
) -> Tuple[str, ...]:
    return tuple(sorted({item.event_id for item in (items or ()) if item is not None}))


class ExpansionBudgetCollector:
    """1 つの所有 scope 分の切り捨て記録を集める。

    ``sink`` は展開器へ渡す即時転送用の callable。上位 collector の list 長ではなく
    このオブジェクトの記録で「当該処理中に切り捨てが起きたか」を判定する。
    """

    __slots__ = ("_records", "_seen")

    def __init__(self) -> None:
        self._records: List[ExpansionBudgetTruncation] = []
        self._seen: set = set()

    def record(self, truncation: Optional[ExpansionBudgetTruncation]) -> None:
        if truncation is None:
            return
        event_id = truncation.event_id
        if event_id in self._seen:
            existing_index = next(
                index
                for index, item in enumerate(self._records)
                if item.event_id == event_id
            )
            existing = self._records[existing_index]
            union = tuple(sorted(
                set(existing.referenced_event_ids)
                | set(truncation.referenced_event_ids)
            ))
            if union != existing.referenced_event_ids:
                self._records[existing_index] = replace(
                    existing, referenced_event_ids=union
                )
            return
        self._seen.add(event_id)
        self._records.append(truncation)

    def extend(self, items: Optional[Iterable[ExpansionBudgetTruncation]]) -> None:
        for item in items or ():
            self.record(item)

    @property
    def sink(self):
        return self.record

    def __bool__(self) -> bool:
        return bool(self._records)

    def __len__(self) -> int:
        return len(self._records)

    def as_tuple(self) -> Tuple[ExpansionBudgetTruncation, ...]:
        return normalize_expansion_budget_truncations(self._records)

# Sibling modules reference each other at call time; import them last to avoid cycles.

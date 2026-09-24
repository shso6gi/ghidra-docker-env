"""Deferred-call and unknown-value references."""

from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass, replace
from typing import Any, Dict, Iterable, List, Mapping, Optional, Tuple
from scripts.function_tracer_pcode.core.json_encoding import (
    JsonBudget, as_list, each, inline, is_json_record, materialize, metered, pairs_of, raw,
    source_converter,
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
        target_name = self.target_ref.display_name() if self.target_ref is not None else "unknown"
        if self.pcode_op_ref is not None and self.pcode_op_ref.address_offset is not None:
            return f"{target_name}@0x{int(self.pcode_op_ref.address_offset):x}"
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
        deferred_call_ref = getattr(self, "deferred_call_ref", None)
        if isinstance(deferred_call_ref, DeferredCallRef):
            object.__setattr__(self, "deferred_call_ref", deferred_call_ref)

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
        normalized = coerce_call_target_ref(target_ref) or CallTargetRef.unknown()
        normalized_ref = deferred_call_ref
        if normalized_ref is None:
            normalized_ref = DeferredCallRef(
                target_ref=normalized,
                sequence=sequence,
            )
        display_hint = placeholder_name or normalized_ref.display_name()
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
        if self.display_hint:
            return self.display_hint
        if self.deferred_call_ref is not None:
            return self.deferred_call_ref.display_name()
        if self.target_ref is not None:
            return self.target_ref.display_name()
        return self.reason or "unknown"

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
                # 旧実装と同じ: 固定個数の要素から成る identity（stable key か repr）をそのまま置く
                yield "origin_ref", raw(_runtime_ref_stable_key_or_repr(self.origin_ref))

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
    深さで打ち切る。値の規則は `_canonical_budget_value_within`（1 つの実装）。
    """

    # producer 時点の identity の構築（key の大きさの owner は identity。出力の準備は
    # `_canonical_budget_source` が walk の作業量へ数える）
    return _canonical_budget_value_within(value, depth, work=JsonBudget(None))


def _charge_key(key: Any, work: Any) -> None:
    """mapping の key を `str(key)` にする手間を、作る前に数える。

    scalar は長さ（数値は桁数の上限）。それ以外（tuple の key など）は、書いたときの大きさを
    `work` の残りの中で数える（大きさに比例する `str()` を数える前に作らない）。
    """

    if isinstance(key, str):
        work.charge(1 + len(key))
    elif key is None or isinstance(key, (bool, float)):
        work.charge(8)
    elif isinstance(key, int):
        work.charge(1 + key.bit_length() // 3)
    else:
        from scripts.function_tracer_pcode.core.json_encoding import RESULT_JSON_POLICY, JsonValueRejected

        try:
            work.charge(1 + RESULT_JSON_POLICY.measure(key, max_bytes=work.remaining(), mode="legacy"))
        except JsonValueRejected:
            work.charge(1 + len(type(key).__qualname__))


def _canonical_budget_value_within(value: Any, depth: int = 0, *, work: Any) -> Any:
    """`_canonical_budget_value` の本体。容器は幅を、文字列は長さを `work` へ数えてから作る。"""

    if value is None or isinstance(value, (bool, int)):
        work.charge(1)
        return value
    if isinstance(value, str):
        work.charge(1 + len(value))
        return value
    if depth >= _CANONICAL_BUDGET_MAX_DEPTH:
        return ["depth_limited", type(value).__module__, type(value).__qualname__]
    if isinstance(value, float):
        return repr(value)
    if isinstance(value, bytes):
        work.charge(1 + 2 * len(value))
        return ["bytes", value.hex()]
    if isinstance(value, (list, tuple)):
        work.charge(1 + len(value))
        return [_canonical_budget_value_within(item, depth + 1, work=work) for item in value]
    if isinstance(value, (set, frozenset)):
        work.charge(1 + len(value))
        # 並びの key（要素の JSON）の長さは、要素を作るときに数えた量に比例する
        return sorted(
            (_canonical_budget_value_within(item, depth + 1, work=work) for item in value),
            key=lambda item: json.dumps(item, ensure_ascii=False, sort_keys=True),
        )
    if isinstance(value, Mapping):
        work.charge(1 + len(value))
        for key in value:
            _charge_key(key, work)
        return {
            str(key): _canonical_budget_value_within(item, depth + 1, work=work)
            for key, item in sorted(value.items(), key=lambda pair: str(pair[0]))
        }
    stable_key = getattr(value, "stable_key", None)
    if callable(stable_key):
        try:
            key = stable_key()
        except (AttributeError, TypeError, ValueError, RecursionError):
            key = None
        if key is not None:
            return ["stable", _canonical_budget_value_within(key, depth + 1, work=work)]
    return ["opaque", type(value).__module__, type(value).__qualname__]


def _canonical_budget_source(value: Any, depth: int = 0, *, work: Any) -> Any:
    """`_canonical_budget_value` と同じ値を 1 要素ずつ作らせる source（出力の準備用）。

    並べる前に幅を `work`（walk の作業量。`metered` が渡す）へ数える。集合だけは並びを
    決めるために要素の canonical な値を先に求める（旧実装と同じ順序。作る量を `work` へ
    数えながら）。
    """

    if value is None or isinstance(value, (bool, int, str)):
        return value
    if depth >= _CANONICAL_BUDGET_MAX_DEPTH:
        return each(("depth_limited", type(value).__module__, type(value).__qualname__))
    if isinstance(value, float):
        return repr(value)
    if isinstance(value, bytes):
        work.charge(1 + 2 * len(value))
        return each(("bytes", value.hex()))
    if isinstance(value, (list, tuple)):
        return each(value, source_converter(lambda item: _canonical_budget_source(item, depth + 1, work=work)))
    if isinstance(value, (set, frozenset)):
        work.charge(1 + len(value))
        ordered = sorted(
            value,
            key=lambda item: json.dumps(
                _canonical_budget_value_within(item, depth + 1, work=work), ensure_ascii=False, sort_keys=True,
            ),
        )
        return each(ordered, source_converter(lambda item: _canonical_budget_source(item, depth + 1, work=work)))
    if isinstance(value, Mapping):
        work.charge(1 + len(value))
        for key in value:
            _charge_key(key, work)
        return pairs_of(
            (str(key), _canonical_budget_source(item, depth + 1, work=work))
            for key, item in sorted(value.items(), key=lambda pair: str(pair[0]))
        )
    stable_key = getattr(value, "stable_key", None)
    if callable(stable_key):
        try:
            key = stable_key()
        except (AttributeError, TypeError, ValueError, RecursionError):
            key = None
        if key is not None:
            return each(("stable", _canonical_budget_source(key, depth + 1, work=work)))
    return each(("opaque", type(value).__module__, type(value).__qualname__))


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

    def stable_key(self) -> Tuple[Any, ...]:
        """発生事実キー。``event_id`` と参照先 event の内容は含めない。"""

        return (
            _EXPANSION_BUDGET_TRUNCATION_KEY_VERSION,
            self.kind,
            self.surface,
            _canonical_budget_value(self.owner_scope_key),
            self.label,
            _canonical_budget_value(self.pcode_op_ref),
            self.dedup,
            self.paths,
            self.conditions,
            _canonical_budget_value(self.callee_scope_key),
        )

    @property
    def event_id(self) -> str:
        cached = getattr(self, "_event_id_cache", None)
        if cached is not None:
            return cached
        digest = hashlib.sha256(
            _canonical_budget_json(self.stable_key()).encode("utf-8")
        ).hexdigest()
        object.__setattr__(self, "_event_id_cache", digest)
        return digest

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
            yield "owner_scope_key", metered(
                lambda work: _canonical_budget_source(self.owner_scope_key, work=work),
            )
        if self.label is not None:
            yield "label", self.label
        if self.pcode_op_ref is not None:
            yield "pcode_op_ref", self.pcode_op_ref
        if self.dedup is not None:
            yield "dedup", inline(
                ("candidate_count", self.dedup[0]),
                ("kept_count", self.dedup[1]),
                ("limit", self.dedup[2]),
            )
        if self.paths is not None:
            yield "paths", inline(
                ("valid_path_count", self.paths[0]),
                ("kept_path_count", self.paths[1]),
                ("limit_paths", self.paths[2]),
            )
        if self.conditions is not None:
            yield "conditions", inline(
                ("dropped_path_count", self.conditions[0]),
                ("max_conditions", self.conditions[1]),
            )
        if self.callee_scope_key is not None:
            yield "callee_scope_key", metered(
                lambda work: _canonical_budget_source(self.callee_scope_key, work=work),
            )
        if self.referenced_event_ids:
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

    merged: Dict[str, ExpansionBudgetTruncation] = {}
    for item in items or ():
        if item is None:
            continue
        event_id = item.event_id
        current = merged.get(event_id)
        if current is None:
            merged[event_id] = item
            continue
        union = tuple(sorted(
            set(current.referenced_event_ids) | set(item.referenced_event_ids)
        ))
        if union != current.referenced_event_ids:
            merged[event_id] = replace(current, referenced_event_ids=union)
    return tuple(merged[event_id] for event_id in sorted(merged))


def merge_expansion_budget_truncations(
    *groups: Optional[Iterable[ExpansionBudgetTruncation]],
) -> Tuple[ExpansionBudgetTruncation, ...]:
    """複数の記録源を和集合にする（既存記録を空の記録源で消さない）。"""

    combined: List[ExpansionBudgetTruncation] = []
    for group in groups:
        combined.extend(item for item in (group or ()) if item is not None)
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

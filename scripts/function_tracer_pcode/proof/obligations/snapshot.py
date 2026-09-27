"""Immutable analysis snapshots and derived semantic views."""

from __future__ import annotations

from dataclasses import dataclass, field
import hashlib
from types import MappingProxyType
from typing import Any, Mapping, Tuple

from scripts.function_tracer_pcode.core import json_encoding
from scripts.function_tracer_pcode.core.budget_policy import serialization_scope
from scripts.function_tracer_pcode.core.json_encoding import (
    LEGACY,
    RESULT_JSON_POLICY,
    builtin_view,
    cached_string_bytes,
    identity_key_of,
    is_json_record,
    materialize,
)
from scripts.function_tracer_pcode.core.live_values import (
    metered_storage_reads,
    NOT_PLAIN,
    as_bool,
    as_repr,
    as_str,
    builtin_mapping,
    builtin_sequence,
    builtin_set,
    dataclass_field_names,
    elements_of,
    enum_value,
    field_value,
    is_enum,
    is_kind,
    items_of,
    json_scalar,
    plain_scalar,
    size,
    type_name,
)
from scripts.function_tracer_pcode.proof.obligations.model import SemanticFactProvenance


SEMANTIC_ANALYSIS_NOTES = frozenset({
    "indirect_control_flow_unresolved",
    "symbolic_post_state_reads",
    "return_case_coverage_gap",
    "return_case_coverage_inconclusive",
    "effect_summary_path_coverage_incomplete",
    "bounded_call_refinement_argument_alignment_failed",
    "bounded_call_refinement_deferred_target_unresolved",
    "bounded_call_refinement_return_summary_unusable",
    "effect_call_argument_evidence_incomplete",
})

#: 比較（pair の comparison）が自分の観測として raw analysis に書き戻す note（Issue #167）。
#: semantic fingerprint には入る（blocker を知らずに作った証明を別の前提として扱う）が、
#: 比較の authority が束縛する raw pair の identity（``comparison_fingerprint``）には入らない:
#: 比較が自分で書いた観測で、比べている raw pair が別物になるわけではない。書くのは
#: ``record_comparison_annotation`` だけ（ここに無い note を比較が書くと identity が変わり、
#: 以後の branch は別の比較として扱われる = fail-closed）。
COMPARISON_ANNOTATION_NOTES = frozenset({
    "return_case_coverage_gap",
    "return_case_coverage_inconclusive",
})


def comparison_pair_identity(left: "AnalysisSnapshot", right: "AnalysisSnapshot") -> str:
    """比較の authority が束縛する raw pair の identity（左右の ``comparison_fingerprint`` の組）。"""

    return SnapshotFingerprintCodec.digest(
        ("comparison_raw_pair_v1", left.comparison_fingerprint, right.comparison_fingerprint)
    )


def record_comparison_annotation(analysis: Any, note: str) -> None:
    """比較の観測 ``note`` を raw analysis に書き戻す（登録済みの note だけ）。"""

    if note not in COMPARISON_ANNOTATION_NOTES:
        raise ValueError(f"unregistered comparison annotation: {note!r}")
    if note not in analysis.analysis_notes:
        analysis.analysis_notes.append(note)


# Every FunctionReturnAnalysis dataclass field must be classified here.  Fields
# represented by a normalized projection still remain listed explicitly.
FUNCTION_ANALYSIS_FIELD_CLASSIFICATION = MappingProxyType({
    "function_name": "semantic", "entry_point": "semantic", "parameters": "semantic",
    "returns": "semantic", "function_ref": "semantic", "return_type": "semantic",
    "return_type_obj": "semantic_projection", "signedness_result": "semantic",
    "unknown_event_count": "semantic", "unknown_event_reasons": "semantic",
    "analysis_notes": "typed_notes", "recovered_from_decompiler": "semantic",
    "incomplete_control_flow": "semantic", "deferred_calls": "semantic",
    "effect_summary": "semantic_projection", "signature_hypotheses": "semantic",
    "return_type_provenance": "semantic", "comparison_surface": "semantic",
    "analysis_scope_key": "semantic", "program_is_big_endian": "semantic",
    "completed_recovery_proof_ids": "derived_proof",
    "completed_recovery_proof_evidence": "derived_proof",
    "binary_id": "semantic", "summary_return_candidates": "semantic",
    "return_outcomes": "semantic", "divergence_outcomes": "semantic",
    "unknown_outcomes": "semantic", "analysis_view_identity": "semantic",
    "partition_revision": "semantic",
    "outcome_seed": "semantic",
    "termination_path_effect_evidence": "semantic",
    "quarantined_recurrence_proposals": "semantic",
    "return_abi_facts": "semantic",
    # Issue #131 PR-B: 切り捨て marker は解析前提の一部。``to_dict`` の正規化済み
    # 全記録が snapshot fingerprint に入るので、marker を知らずに作った証明は
    # 別の前提のものとして再利用されない。
    "expansion_budget_truncations": "semantic",
})


def deep_freeze(value: Any) -> Any:
    """組み込みの振る舞いの容器を読み取り専用の写しにする（`core/live_values` の規則で辿る: 上書きした
    `items()` / `__iter__` を呼ばない）。容器でない値はそのまま（葉）。振る舞いを上書きした dict の
    subclass は写すとその code を呼ぶので `TypeError`（変更できる mapping をそのまま snapshot に置かない:
    fail-closed。snapshot の意味の値は fingerprint の digest が先に拒む）。"""

    mapping = builtin_mapping(value)
    if mapping is not None:
        # key は置かれた dict と同じ key（新しい dict に置くときの hash は置いた側と同じ実装）
        return MappingProxyType({key: deep_freeze(item) for key, item in items_of(mapping)})
    if is_kind(value, dict):
        raise TypeError(f"{type_name(type(value))} overrides its mapping behaviour and is not frozen")
    if builtin_sequence(value):
        return tuple(deep_freeze(item) for item in elements_of(value))
    if builtin_set(value):
        return frozenset(deep_freeze(item) for item in elements_of(value))
    return value


def _semantic_effect_summary_projection(effect_summary: Any, work: Any = None) -> Any:
    if effect_summary is None:
        return None
    # The dataclass projection is object-derived and includes stores, calls,
    # completeness reasons, and the function control/effect profile.  freeze()
    # rejects any opaque object that lacks a stable key instead of stringifying it.
    # Issue #22 PR-22-D: 投影は写しながら直列化の作業量へ足す（`freeze(budget=work)`）。
    # 効果が大量でも、予算を超えた時点で残りを投影しない。
    return SnapshotFingerprintCodec.freeze(effect_summary, budget=work)


def _classify_analysis_notes(notes: Any) -> Tuple[Tuple[str, ...], Tuple[str, ...]]:
    semantic = []
    diagnostic = []
    # note は `core/live_values` の規則で読む（scalar・組み込みのままの enum は `str()` と同じ文字列、
    # それ以外は object ごとに区別する印（型名と identity: 値の `__str__` を呼ばない。別の note を 1 つに
    # 合併しない側。未知の note と同じく semantic 側）
    for raw_note in (elements_of(notes) if notes is not None and as_bool(notes) else ()):
        try:
            note = as_str(raw_note)
        except TypeError:
            note = f"<{type_name(type(raw_note))}@{id(raw_note):x}>"
        if note in SEMANTIC_ANALYSIS_NOTES:
            semantic.append(note)
        elif note.startswith(("debug:", "diagnostic:")):
            diagnostic.append(note)
        else:
            # Unknown notes are semantic by default.  This is conservative and
            # prevents a newly introduced blocker from silently missing identity.
            semantic.append(note)
    return tuple(semantic), tuple(diagnostic)


#: fingerprint の JSON の書き方（key 順・区切り `,` `:`・ASCII だけ）。凍結した値の書き出しと
#: mapping の key の並びの両方に使う
_FINGERPRINT_JSON = json_encoding.JsonEncodingPolicy(ensure_ascii=True, item_separator=",", key_separator=":")


def _fingerprint_json(value: Any) -> str:
    """凍結した値の fingerprint の JSON（`json.dumps(sort_keys=True, separators=(",", ":"), ensure_ascii=True)`）。"""

    return json_encoding.JsonEncodingPolicy.dumps(_FINGERPRINT_JSON, value)


def _enum_payload(value: Any) -> Any:
    """enum の member の値（instance の `_value_`。`value` の property を呼ばない）の写し。

    scalar は基底型の値、それ以外は組み込みの値だけで書き直した写し（`builtin_view` の固定の上限の中:
    予算つきの凍結と予算なしの凍結で同じ写し）。書き直せない値（live な object を含む値・固定の上限の
    外の値）は object-derived な identity を持たないので `TypeError`。
    """

    raw = enum_value(value)
    scalar = plain_scalar(raw)
    if scalar is not NOT_PLAIN:
        return scalar
    ok, view = builtin_view(raw)
    if not ok:
        raise TypeError(f"enum {type_name(type(value))} has no object-derived stable value")
    return view


def _mixin_enum(value: Any) -> bool:
    """`int` / `str` / `float` を mixin した enum か（JSON では基底型の値で書く。写しは member のまま）。"""

    return is_enum(value) and json_scalar(value) is not NOT_PLAIN


class _Text:
    """`_frozen_repr` が流す固定の文字列（区切り・括弧）。"""

    __slots__ = ("text",)

    def __init__(self, text: str) -> None:
        self.text = text


def _frozen_repr(value: Any) -> str:
    """凍結した値の `repr`（set の要素の並びの key）を、組み込みの `repr` の規則だけで作る。

    凍結した値は基底型の scalar・mixin の enum の member・tuple と、enum の値の写し（list / dict）
    だけから成る。葉は `live_values.as_repr`（scalar の subclass は基底型の `repr`、組み込みのままの
    enum は `Enum.__repr__`）。それ以外は `TypeError`。
    """

    if (type(value) is str or type(value) is int):
        return repr(value)
    pieces = []
    pending = [value]
    while pending:
        item = pending.pop()
        kind = type(item)
        if kind is _Text:
            pieces.append(as_str(item.text))
        elif kind is tuple:
            count = size(item)
            pieces.append("(")
            pending.append(_Text(",)" if count == 1 else ")"))
            for index in range(count - 1, -1, -1):
                pending.append(item[index])
                if index:
                    pending.append(_Text(", "))
        elif kind is list:
            count = size(item)
            pieces.append("[")
            pending.append(_Text("]"))
            for index in range(count - 1, -1, -1):
                pending.append(item[index])
                if index:
                    pending.append(_Text(", "))
        elif kind is dict:
            keys = []
            children = []
            for key, child in items_of(item):
                keys.append(key)
                children.append(child)
            pieces.append("{")
            pending.append(_Text("}"))
            for index in range(len(keys) - 1, -1, -1):
                pending.append(children[index])
                pending.append(_Text(": "))
                pending.append(keys[index])
                if index:
                    pending.append(_Text(", "))
        else:
            pieces.append(as_repr(item))
    return "".join(pieces)


def _set_members(frozen: Any) -> Tuple[Any, ...]:
    """凍結した set の要素を、要素の `repr` の順（同じ `repr` は元の順）に並べる。"""

    count = size(frozen)
    keyed = []
    for index in range(count):
        keyed.append((_frozen_repr(frozen[index]), index))
    keyed.sort()
    return tuple(frozen[index] for _text, index in keyed)


def _tagged(name: str, frozen: Any, meter: Any) -> Tuple[str, Any]:
    if meter is not None:
        meter.frame(2)
        meter.scalar(name)
    return (name, frozen)


class SnapshotFingerprintCodec:
    """Canonicalizes semantic DTO data without stringifying opaque objects.

    live な値は `core.live_values` の規則だけで読む（Issue #22 PR-22-D）: scalar の subclass は基底型の
    slot の値、enum の値は instance の `_value_`、容器は組み込みの振る舞いのもの（上書きした
    `items` / `__iter__` / `__len__` を持つ容器は辿らない）、型は `type(value)`（`__class__` を読まない）。
    """

    @classmethod
    def freeze(cls, value: Any, *, budget: Any = None) -> Any:
        """値の canonical な写し。`budget` を渡すと、写す値の byte を写しながら足す。

        `budget`（`JsonBudget` の interface、snapshot では `SerializationWork`）は写した
        葉と容器の区切りごとに数え、超えた時点で残りを写さない。record の `to_dict()`
        は walker が同じ `budget` で数えながら作る（作ってから数えない）。
        """

        if budget is None:
            return cls._freeze_unmetered(value)
        # 値の storage の読みも固定の上限を超えた分は同じ予算へ（超えればその予算の超過）
        with metered_storage_reads(budget):
            return cls._freeze(value, _FreezeMeter(budget))

    @classmethod
    def _freeze_unmetered(cls, value: Any) -> Any:
        """数えない写し（fingerprint の digest など）。`_freeze(value, None)` と同じ値。

        digest は snapshot のたびに値全体を写すので、数える経路の分岐・helper を通さない
        （`test_the_unmetered_freeze_equals_the_metered_copy` が同じ値であることを固定）。
        """

        if value is None:
            return None
        kind = type(value)
        if kind is str or kind is int or kind is bool or kind is float:
            return value
        freeze = cls._freeze_unmetered
        # 速い経路: 組み込みの型そのものの容器（組み込みの振る舞いと分かっている）
        if (type(value) is tuple or type(value) is list):
            return tuple(freeze(v) for v in value)
        if type(value) is dict:
            return cls.sorted_mapping_items(
                tuple((freeze(key), freeze(item)) for key, item in value.items())
            )
        scalar = plain_scalar(value)
        if scalar is not NOT_PLAIN:
            return scalar
        if is_enum(value):
            if _mixin_enum(value):
                return value
            return (type_name(kind), _enum_payload(value))
        if kind is bytes:
            return ("bytes", value.hex())
        mapping = builtin_mapping(value)
        if mapping is not None:
            return cls.sorted_mapping_items(
                tuple((freeze(key), freeze(item)) for key, item in items_of(mapping))
            )
        if builtin_sequence(value):
            return tuple(freeze(v) for v in elements_of(value))
        if builtin_set(value):
            return _set_members(tuple(freeze(v) for v in elements_of(value)))
        name = type_name(kind)
        has_key, identity_key = identity_key_of(value)
        if has_key:
            return (name, freeze(identity_key))
        if is_json_record(value):
            # record の LEGACY 表現（`to_dict()` と同じ walker。解析 1 件分の作業量の中ならそこへ数える）
            return (name, freeze(materialize(value)))
        names = dataclass_field_names(value)
        if names is not None:
            return (name, tuple((field_name, freeze(field_value(value, field_name))) for field_name in names))
        raise TypeError(f"opaque object {name} has no object-derived stable identity")

    @classmethod
    def _freeze(cls, value: Any, meter: Any) -> Any:
        if meter is None:
            return cls._freeze_unmetered(value)
        scalar = plain_scalar(value)
        if scalar is not NOT_PLAIN:
            meter.scalar(scalar)
            return scalar
        kind = type(value)
        if is_enum(value):
            base = json_scalar(value)
            if base is not NOT_PLAIN:
                # mixin の enum（写しは member のまま。JSON では基底型の値）
                meter.scalar(base)
                return value
            name = type_name(kind)
            # 写しは予算なしの凍結と同じ（固定の上限の中の組み込みの値だけの写し）。予算へは写しの
            # JSON の大きさを足す（写しは固定の上限の中なので、測るのも有界）
            payload = _enum_payload(value)
            meter.frame(2)
            meter.scalar(name)
            if plain_scalar(payload) is not NOT_PLAIN:
                meter.scalar(payload)
            else:
                meter.budget.charge(json_encoding.RESULT_JSON_POLICY.measure(payload))
            return (name, payload)
        if kind is bytes:
            meter.frame(2)
            meter.scalar("bytes")
            meter.scalar_bytes(2 * len(value) + 2)
            return ("bytes", value.hex())
        mapping = builtin_mapping(value)
        if mapping is not None:
            meter.frame(size(mapping))
            items = []
            for key, item in items_of(mapping):
                frozen_key = cls._freeze(key, meter)
                frozen_item = cls._freeze(item, meter)
                meter.frame(2)
                items.append((frozen_key, frozen_item))
            return cls.sorted_mapping_items(tuple(items))
        if builtin_sequence(value):
            meter.frame(size(value))
            return tuple(cls._freeze(v, meter) for v in elements_of(value))
        if builtin_set(value):
            meter.frame(size(value))
            return _set_members(tuple(cls._freeze(v, meter) for v in elements_of(value)))
        name = type_name(kind)
        has_key, identity_key = identity_key_of(value)
        if has_key:
            return _tagged(name, cls._freeze_key(identity_key, meter), meter)
        if is_json_record(value):
            # walker が `budget` で数えながら作る。写しは数え済みの値から作る（json record でない
            # object の `to_dict()` は任意の producer なので呼ばない: object-derived な identity の
            # 無い値として拒む）
            built = json_encoding.RESULT_JSON_POLICY.materialize(value, budget=meter.budget)
            return _tagged(name, cls._freeze(built, None), meter)
        names = dataclass_field_names(value)
        if names is not None:
            meter.frame(len(names))
            fields_frozen = []
            for field_name in names:
                frozen_field = cls._freeze(field_value(value, field_name), meter)
                meter.frame(2)
                meter.scalar(field_name)
                fields_frozen.append((field_name, frozen_field))
            return _tagged(name, tuple(fields_frozen), meter)
        raise TypeError(f"opaque object {name} has no object-derived stable identity")

    @classmethod
    def _freeze_key(cls, key: Any, meter: Any) -> Any:
        """identity key（`stable_key()` / `to_key()` の値）の写し。

        key は同じ値が何度も現れる（snapshot ごとに同じ効果を投影する）ので、大きさは
        walker が数え（tuple だけの部分木は pair の間 cache）、予算に収まってから写す。
        """

        if meter is None:
            return cls._freeze(key, None)
        meter.count_value(key)
        return cls._freeze(key, None)

    @classmethod
    def sorted_mapping_items(cls, items: Tuple[Tuple[Any, Any], ...]) -> Tuple[Tuple[Any, Any], ...]:
        """凍結した (key, 値) の組を、mapping の canonical な並び（key の JSON の順）にする。

        key の JSON が同じ組（canonical な key の重複）は `ValueError`。
        """

        keyed = []
        # 位置は数えながら持つ（組ごとに列の長さを読み直さない）
        count = 0
        for key, _item in items:
            keyed.append((_fingerprint_json(key), count))
            count += 1
        keyed.sort()
        for index in range(1, count):
            if keyed[index - 1][0] == keyed[index][0]:
                raise ValueError("mapping contains duplicate canonical semantic keys")
        return tuple(items[index] for _text, index in keyed)

    @staticmethod
    def _sort_key(value: Any) -> str:
        return _fingerprint_json(value)

    @classmethod
    def digest(cls, value: Any) -> str:
        frozen = cls.freeze(value)
        payload = _fingerprint_json(frozen)
        return hashlib.sha256(payload.encode("utf-8")).hexdigest()


class _FreezeMeter:
    """`freeze(budget=...)` が写した値の byte を `budget` へ足す（写しの JSON の大きさ）。"""

    __slots__ = ("budget", "_policy")

    def __init__(self, budget: Any) -> None:
        self.budget = budget
        self._policy = RESULT_JSON_POLICY

    def frame(self, count: int) -> None:
        self.budget.charge(self._policy.container_frame_bytes(count))

    def scalar(self, value: Any) -> None:
        policy = self._policy
        # 基底型の値（scalar の subclass・mixin の enum は基底型の slot）で数える
        base = json_scalar(value)
        kind = type(base)
        if kind is str:
            size_bytes = cached_string_bytes(policy, base, max_bytes=self.budget.remaining())
        elif base is None or base is True:
            size_bytes = 4
        elif base is False:
            size_bytes = 5
        elif kind is int:
            size_bytes = len(int.__repr__(base))
        elif kind is float:
            size_bytes = len(float.__repr__(base))
        else:
            size_bytes = policy.string_bytes(type_name(type(value)))
        self.budget.charge(size_bytes)

    def scalar_bytes(self, size_bytes: int) -> None:
        self.budget.charge(size_bytes)

    def count_value(self, value: Any) -> None:
        """既に在る値（identity key）の JSON byte を、写す前に数えて足す。"""

        self._policy.count_into(value, self.budget, mode=LEGACY)


#: snapshot 1 つ分の直列化の作業量を数える観測点。
SNAPSHOT_SERIALIZATION_SITE = "proof.obligations.snapshot.from_function_analysis"


@dataclass(frozen=True)
class AnalysisSnapshot:
    snapshot_id: Tuple[Any, ...]
    semantic_fields: Mapping[str, Any]
    semantic_fingerprint: str
    extraction_schema_version: int = 1
    diagnostic_refs: Mapping[str, Any] = field(default_factory=dict, compare=False, hash=False)

    @classmethod
    def create(
        cls,
        snapshot_id: Tuple[Any, ...],
        semantic_fields: Mapping[str, Any],
        *,
        diagnostic_refs: Mapping[str, Any] | None = None,
        extraction_schema_version: int = 1,
    ) -> "AnalysisSnapshot":
        payload = (extraction_schema_version, snapshot_id, semantic_fields)
        # fingerprint を先に求める（opaque な値・上書きした容器は digest が拒む。拒まれた値を写さない）
        fingerprint = SnapshotFingerprintCodec.digest(payload)
        return cls(
            snapshot_id=tuple(snapshot_id),
            semantic_fields=deep_freeze(dict(semantic_fields)),
            semantic_fingerprint=fingerprint,
            extraction_schema_version=extraction_schema_version,
            diagnostic_refs=deep_freeze(dict(diagnostic_refs or {})),
        )

    @property
    def comparison_fingerprint(self) -> str:
        """比較の authority が束縛する identity（比較自身が書いた note を除く、Issue #167）。"""

        semantic_fields = dict(self.semantic_fields)
        semantic_fields["semantic_analysis_notes"] = tuple(
            note
            for note in semantic_fields.get("semantic_analysis_notes", ()) or ()
            if note not in COMPARISON_ANNOTATION_NOTES
        )
        return SnapshotFingerprintCodec.digest(
            ("comparison_identity_v1", self.extraction_schema_version, self.snapshot_id, semantic_fields)
        )

    @classmethod
    def from_function_analysis(cls, analysis: Any) -> "AnalysisSnapshot":
        """Freeze the semantic extraction result, excluding mutable proof state."""

        to_dict = getattr(analysis, "to_dict", None)
        if not callable(to_dict):
            raise TypeError("analysis must provide object-derived to_dict() data")
        # Issue #22 PR-22-D: snapshot 1 つ分の最終表現（解析の `to_dict()` と効果要約の
        # 投影）を **1 つの直列化の作業量** として数える。木は DAG のまま見積もってから、
        # 木以外の値は walker / codec が 1 要素ずつ写しながら足し（作ってから数えない）、
        # 合計が予算を超えた時点で残りを作らずに pair terminal な限界になる（式 1 本ごとの
        # 予算とは別の aggregate）。
        with serialization_scope(
            site=SNAPSHOT_SERIALIZATION_SITE,
            target_parts=(
                "function_analysis_snapshot",
                getattr(analysis, "binary_id", None),
                getattr(analysis, "function_name", None),
                getattr(analysis, "entry_point", None),
            ),
        ) as work:
            return cls._from_function_analysis_with(analysis, to_dict, work)

    @classmethod
    def _from_function_analysis_with(cls, analysis: Any, to_dict: Any, work: Any) -> "AnalysisSnapshot":
        # 解析前提でない derived proof は下で捨てるので、表現できる解析は最初から
        # 作らない（`semantic_snapshot_dict`。残りは `to_dict()` と同じ値）
        semantic_view = getattr(analysis, "semantic_snapshot_dict", None)
        semantic_fields = dict(semantic_view() if callable(semantic_view) else to_dict())
        # These fields describe execution/diagnostic state rather than the
        # immutable extraction premise.  Proofs are applied through a derived
        # view and must never mutate snapshot identity.
        for key in ("completed_recovery_proof_ids", "completed_recovery_proof_evidence"):
            semantic_fields.pop(key, None)
        semantic_notes, diagnostic_notes = _classify_analysis_notes(
            semantic_fields.pop("analysis_notes", ())
        )
        semantic_fields["semantic_analysis_notes"] = semantic_notes
        semantic_fields["effect_summary"] = _semantic_effect_summary_projection(
            getattr(analysis, "effect_summary", None), work,
        )
        function_ref = getattr(analysis, "function_ref", None)
        has_key, function_key = (False, None) if function_ref is None else identity_key_of(function_ref)
        if not has_key:
            function_key = (getattr(analysis, "function_name", None), getattr(analysis, "entry_point", None))
        snapshot_id = (
            "function_analysis_snapshot",
            getattr(analysis, "binary_id", None),
            function_key,
            getattr(analysis, "analysis_scope_key", None),
        )
        return cls.create(
            snapshot_id,
            semantic_fields,
            diagnostic_refs={"function_ref": function_ref, "analysis_notes": diagnostic_notes},
        )


@dataclass(frozen=True)
class DerivedAnalysisView:
    view_id: Tuple[Any, ...]
    snapshot_id: Tuple[Any, ...]
    parent_view_id: Tuple[Any, ...] | None
    validated_proof_closure_id: Tuple[Any, ...]
    normalization_policy_digest: str
    view_builder_version: str
    semantic_surface: Mapping[str, Any]
    semantic_fingerprint: str
    fact_provenance: Mapping[Tuple[Any, ...], SemanticFactProvenance] = field(
        default_factory=dict, compare=False, hash=False
    )

    @classmethod
    def create(
        cls,
        *,
        snapshot_id: Tuple[Any, ...],
        parent_view_id: Tuple[Any, ...] | None,
        validated_proof_closure_id: Tuple[Any, ...],
        normalization_policy_digest: str,
        view_builder_version: str,
        semantic_surface: Mapping[str, Any],
        fact_provenance: Mapping[Tuple[Any, ...], SemanticFactProvenance] | None = None,
    ) -> "DerivedAnalysisView":
        fingerprint = SnapshotFingerprintCodec.digest(
            (snapshot_id, validated_proof_closure_id, normalization_policy_digest,
             view_builder_version, semantic_surface)
        )
        view_id = ("derived_view", tuple(snapshot_id), fingerprint)
        return cls(
            view_id=view_id,
            snapshot_id=tuple(snapshot_id),
            parent_view_id=parent_view_id,
            validated_proof_closure_id=tuple(validated_proof_closure_id),
            normalization_policy_digest=normalization_policy_digest,
            view_builder_version=view_builder_version,
            semantic_surface=deep_freeze(dict(semantic_surface)),
            semantic_fingerprint=fingerprint,
            fact_provenance=deep_freeze(dict(fact_provenance or {})),
        )

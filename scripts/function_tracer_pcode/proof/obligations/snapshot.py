"""Immutable analysis snapshots and derived semantic views."""

from __future__ import annotations

from dataclasses import dataclass, field
import hashlib
import json
from types import MappingProxyType
from typing import Any, Callable, Dict, Iterable, List, Mapping, NamedTuple, Optional, Tuple

from scripts.function_tracer_pcode.core import json_encoding
from scripts.function_tracer_pcode.core.budget_policy import serialization_scope, substituting_leaves
from scripts.function_tracer_pcode.core.json_encoding import (
    LEGACY,
    RESULT_JSON_POLICY,
    builtin_view,
    cached_string_bytes,
    identity_key_of,
    is_json_record,
    materialize,
    protocol_method,
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
    # Issue #185: 入力領域の正本と仮説の台帳は解析前提の一部。``to_dict`` は正本が現在の表と
    # 違うときと台帳があるときだけ出すので、差があれば fingerprint が別の前提になる。
    "raw_parameter_domains": "semantic",
    "parameter_domain_hypotheses": "semantic",
})


def deep_freeze(value: Any) -> Any:
    """組み込みの振る舞いの容器を読み取り専用の写しにする（`core/live_values` の規則で辿る: 上書きした
    `items()` / `__iter__` を呼ばない）。容器でない値はそのまま（葉）。振る舞いを上書きした dict の
    subclass は写すとその code を呼ぶので `TypeError`（変更できる mapping をそのまま snapshot に置かない:
    fail-closed。snapshot の意味の値は fingerprint の digest が先に拒む）。"""

    kind = type(value)
    # よくある形（組み込みの型そのもの）は型の同一性で振り分ける: 反復は組み込みの実装だけで、値の code を
    # 呼ばない（snapshot のたびに意味の値全体を辿るので、node ごとの判定を軽くする）
    if kind is str or kind is int or value is None or kind is bool or kind is float:
        return value
    if kind is dict:
        return MappingProxyType({key: deep_freeze(item) for key, item in dict.items(value)})
    if kind is tuple or kind is list:
        return tuple(deep_freeze(item) for item in value)
    if kind is frozenset or kind is set:
        return frozenset(deep_freeze(item) for item in value)
    mapping = builtin_mapping(value)
    if mapping is not None:
        # key は置かれた dict と同じ key を新しい dict へ置く: hash が組み込みでない key は置いたときと
        # 同じ `__hash__` をもう一度呼ぶ（main と同じ。変更できる元の mapping を snapshot に置かないことを
        # 優先する。意味の値の key は digest が確かめ、診断の値の key は production では str / tuple）
        return MappingProxyType({key: deep_freeze(item) for key, item in items_of(mapping)})
    if is_kind(value, dict):
        raise TypeError(f"{type_name(type(value))} is not a mapping that can be read without its own code; not frozen")
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

        **token を通さない**: 呼ぶ側の文脈（読みの最中・入力の code の中・入れ子・例外の後）によらず、token の型の
        値も opaque な値として拒む。token を写しに置けるのは、単一の読みが自分の置いた token（`PlacedTokens`）を
        明示して渡す内部の凍結（`_freeze_placing`。`read_snapshot_inputs` だけが呼ぶ）だけ。
        """

        return cls._freeze_placing(value, None)

    @classmethod
    def _freeze_placing(cls, value: Any, placed: Optional["PlacedTokens"]) -> Any:
        """`_freeze_unmetered` の本体。`placed` は、この凍結がそのまま写しに置いてよい token（その読みの hook が
        置いた object そのもの。identity で照合する）。`None` なら何も置かない（通常の codec）。

        許可は引数でだけ渡る（thread や module の状態を読まない）: この凍結の中で走る入力の code（`stable_key` /
        record の LEGACY 表現）が codec を呼べば、その呼び出しは `placed` を持たない通常の凍結になる。入力が作った
        同じ型の object は `placed` に無いので token ではない（main と同じく opaque として拒む）。
        """

        if value is None:
            return None
        kind = type(value)
        if kind is str or kind is int or kind is bool or kind is float:
            return value
        recurse = cls._freeze_placing
        # 速い経路: 組み込みの型そのものの容器（組み込みの振る舞いと分かっている）
        if (type(value) is tuple or type(value) is list):
            return tuple(recurse(v, placed) for v in value)
        if type(value) is dict:
            return cls.sorted_mapping_items(
                tuple((recurse(key, placed), recurse(item, placed)) for key, item in value.items())
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
                tuple((recurse(key, placed), recurse(item, placed)) for key, item in items_of(mapping))
            )
        if builtin_sequence(value):
            return tuple(recurse(v, placed) for v in elements_of(value))
        if builtin_set(value):
            return _set_members(tuple(recurse(v, placed) for v in elements_of(value)))
        if _is_placed_token(placed, value):
            return value
        name = type_name(kind)
        has_key, identity_key = identity_key_of(value)
        if has_key:
            # 入力の code（`stable_key`）が返した値: 入力の値なので token を通さない
            return (name, recurse(identity_key, None))
        if is_json_record(value):
            # record の LEGACY 表現（`to_dict()` と同じ walker。解析 1 件分の作業量の中ならそこへ数える）
            return (name, recurse(materialize(value), None))
        names = dataclass_field_names(value)
        if names is not None:
            return (name, tuple((field_name, recurse(field_value(value, field_name), None)) for field_name in names))
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
            # 写しは予算なしの凍結と同じ（固定の上限の中の組み込みの値だけの写し）。予算へは写しを
            # 同じ meter で凍結した大きさを足す（組み込みの値だけの写しなので凍結でき、固定の上限の中）
            payload = _enum_payload(value)
            meter.frame(2)
            meter.scalar(name)
            cls._freeze(payload, meter)
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
        return cls.digest_frozen(cls.freeze(value))

    @staticmethod
    def digest_frozen(frozen: Any) -> str:
        """凍結した値の digest（`digest(value)` は `digest_frozen(freeze(value))`）。"""

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


#: snapshot の再利用の token の型と、token が代わりに置かれた値の LEGACY の木を作る関数・identity。登録は token の
#: **展開の方法** を決めるだけで、token を扱う許可ではない（許可は `PlacedTokens`）。登録するのは再利用の owner だけ（静的 test）
_WITNESS_TOKEN_TYPES: List[Tuple[type, Callable[[Any], Any], Callable[[Any], int]]] = []


class PlacedTokens:
    """1 回の単一の読みで、葉の置き換え（`LeafSubstitution`）が **置いた** token（identity で照合する）。

    token を扱う許可はこれだけ: codec の内部の凍結（`SnapshotFingerprintCodec._freeze_placing`）・digest の印・
    展開は、この中にある object そのものだけを token として扱う。型だけでは token にならない（入力が作った同じ型の
    object は token ではない）。作るのは `read_snapshot_inputs` だけで、読みの値（`SnapshotRead`）と一緒に渡る。
    """

    __slots__ = ("_by_id",)

    def __init__(self, tokens: Iterable[Any]) -> None:
        by_id: Dict[int, Any] = {}
        for token in tokens:
            if _witness_token_tree(type(token)) is None:
                raise TypeError(f"{type_name(type(token))} is not a registered witness token type")
            by_id[id(token)] = token
        #: id → token（token への強参照も兼ねる: 生きている間 id は別の object に使い回されない）
        self._by_id = by_id

    def holds(self, value: Any) -> bool:
        return _is_placed_token(self, value)

    def __bool__(self) -> bool:
        return bool(self._by_id)


def _is_placed_token(placed: Optional[PlacedTokens], value: Any) -> bool:
    """`value` が `placed` にある token **そのもの** か（identity だけで照合する: 値の protocol を呼ばない）。"""

    if placed is None:
        return False
    token = placed._by_id.get(id(value))
    return token is not None and token is value


#: token を 1 つも置かなかった読み
NO_PLACED_TOKENS = PlacedTokens(())


def placed_tokens_of(leaf_substitution: Any) -> PlacedTokens:
    """葉の置き換えが置いた値（`LeafSubstitution.__placed_values__`）を、token の許可にする。"""

    if leaf_substitution is None:
        return NO_PLACED_TOKENS
    values = protocol_method(leaf_substitution, "__placed_values__")(leaf_substitution)
    return PlacedTokens(values) if values else NO_PLACED_TOKENS


def register_witness_token_type(kind: type, tree_of: Callable[[Any], Any], identity_of: Callable[[Any], int]) -> type:
    """再利用の owner が発行する token の型と、その展開・identity を登録する（その module の読み込み時に 1 回）。

    `tree_of(token)` は、token が代わりに置かれた葉を walker が置くはずだった LEGACY の木（組み込みの値だけ。
    入力の code を呼ばない純粋な関数）。`identity_of(token)` は、token が代わりに置かれた値の identity（同じ値の
    token どうしで同じ整数。token が値を生かしている間は別の値と重ならない）。
    """

    if not any(kind is known for known, _tree_of, _identity_of in _WITNESS_TOKEN_TYPES):
        _WITNESS_TOKEN_TYPES.append((kind, tree_of, identity_of))
    return kind


def _witness_token_tree(kind: type) -> Optional[Callable[[Any], Any]]:
    """`kind` が登録した token の型 **そのもの** ならその展開（型の比較は identity だけ: metaclass の `__eq__` を呼ばない）。"""

    for known, tree_of, _identity_of in _WITNESS_TOKEN_TYPES:
        if kind is known:
            return tree_of
    return None


def _witness_token_identity(kind: type) -> Optional[Callable[[Any], int]]:
    for known, _tree_of, identity_of in _WITNESS_TOKEN_TYPES:
        if kind is known:
            return identity_of
    return None


#: token でない JSON にできない値の例外を、標準の encoder と同じにするための instance（`default` は値だけを読む）
_PLAIN_ENCODER = json.JSONEncoder()

#: token の印の key（凍結した写しの JSON に object（`{...}`）を書くのは enum の値の写しだけで、その key がこの
#: 文字列と重なっても、同じ位置の `retained_form` の写し（token か enum の member か）が違う）
_WITNESS_TOKEN_MARK = "\u0000witness_token"


def witness_fingerprint_digest(frozen: Any, placed: PlacedTokens) -> str:
    """codec の写し（token を含み得る）の fingerprint の digest。token は、代わりに置かれた値の identity の印で書く。

    token の無い写しでは `digest_frozen(frozen)` と同じ。token の位置が同じで同じ値を指す写しどうしは、展開した
    写しの digest（snapshot の fingerprint）も同じ: 印の外の JSON が同じなら、展開した JSON も同じ。token の位置は
    意味の view の木の中だけで、`retained_form` の写しの同じ位置にも同じ token がある（再利用は両方を比べる）。
    """

    return _marked_fingerprint_digest(frozen, placed)[0]


def _marked_fingerprint_digest(frozen: Any, placed: PlacedTokens) -> Tuple[str, bool]:
    """`witness_fingerprint_digest` と、写しに token があったか（JSON を 1 回書く。token が無ければ、書く JSON は
    `digest_frozen` と同じ: 印の関数は JSON にできない値でだけ呼ばれる）。"""

    marked = [False]

    def mark(value: Any) -> Any:
        identity_of = _witness_token_identity(type(value)) if placed.holds(value) else None
        if identity_of is None:
            # token でない値: `digest_frozen` の JSON の writer と同じ例外（型・文面）
            return json.JSONEncoder.default(_PLAIN_ENCODER, value)
        marked[0] = True
        return {_WITNESS_TOKEN_MARK: identity_of(value)}

    payload = json_encoding.JsonEncodingPolicy.dumps(_FINGERPRINT_JSON, frozen, default=mark)
    return hashlib.sha256(payload.encode("utf-8")).hexdigest(), marked[0]


def _replace_witness_tokens(
    value: Any, leaf: Callable[[Any, Callable[[Any], Any]], Any], placed: PlacedTokens,
) -> Any:
    """組み込みの容器（tuple / list / dict / MappingProxy / frozenset）の中の、`placed` にある token を
    `leaf(token, tree_of)` に置き換える。token の無い容器は同じ object を返す（容器でない値・入力の object の中は
    辿らない。`placed` に無い同じ型の object はそのまま）。"""

    kind = type(value)
    if placed.holds(value):
        return leaf(value, _witness_token_tree(kind))
    if kind is tuple or kind is list or kind is frozenset:
        items = [_replace_witness_tokens(item, leaf, placed) for item in value]
        if all(new is old for new, old in zip(items, value)):
            return value
        return kind(items)
    if kind is dict or kind is MappingProxyType:
        rows = [
            (key, _replace_witness_tokens(key, leaf, placed), item, _replace_witness_tokens(item, leaf, placed))
            for key, item in value.items()
        ]
        if all(new_key is key and new_item is item for key, new_key, item, new_item in rows):
            return value
        rebuilt = {new_key: new_item for _key, new_key, _item, new_item in rows}
        return MappingProxyType(rebuilt) if kind is MappingProxyType else rebuilt
    return value


def expand_witness_tokens(frozen: Any, placed: PlacedTokens) -> Any:
    """凍結した値（codec の写し）の、`placed` にある token を、token が代わりに置かれた値の凍結した写しへ戻す（純粋）。"""

    return _replace_witness_tokens(
        frozen, lambda token, tree_of: SnapshotFingerprintCodec._freeze_unmetered(tree_of(token)), placed,
    )


def _expand_held_tokens(held: Any, placed: PlacedTokens) -> Any:
    """snapshot に置く値（`retained_form` の写し）の、`placed` にある token を、置かれるはずだった木の写しへ戻す（純粋）。"""

    return _replace_witness_tokens(held, lambda token, tree_of: deep_freeze(tree_of(token)), placed)


#: `AnalysisSnapshot.create` の既定の抽出 schema の版
SNAPSHOT_EXTRACTION_SCHEMA_VERSION = 1


def fingerprint_payload(snapshot_id: Any, semantic_fields: Any, extraction_schema_version: int) -> Tuple[Any, ...]:
    """snapshot の fingerprint が digest する値（**fingerprint の唯一の材料**。`create` と再利用が共有する）。"""

    return (extraction_schema_version, snapshot_id, semantic_fields)


def retained_form(snapshot_id: Any, semantic_fields: Any, diagnostic_refs: Any) -> Tuple[Any, Any, Any]:
    """`create` が snapshot に置く値（**保持の契約**。`create` と再利用が共有する）。

    `snapshot_id` は浅い tuple にするだけで、要素は渡された object のまま置く（後で変われば snapshot の
    `snapshot_id` も変わる）。`semantic_fields` / `diagnostic_refs` は `deep_freeze` が容器を写し、容器でない
    値は参照のまま置く。
    """

    return (
        tuple(snapshot_id),
        deep_freeze(dict(semantic_fields)),
        deep_freeze(dict(diagnostic_refs or {})),
    )

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
        extraction_schema_version: int = SNAPSHOT_EXTRACTION_SCHEMA_VERSION,
    ) -> "AnalysisSnapshot":
        # fingerprint を先に求める（opaque な値・上書きした容器は digest が拒む。拒まれた値を写さない）
        fingerprint = SnapshotFingerprintCodec.digest(
            fingerprint_payload(snapshot_id, semantic_fields, extraction_schema_version)
        )
        held_id, held_fields, held_refs = retained_form(snapshot_id, semantic_fields, diagnostic_refs)
        return cls._from_parts(fingerprint, held_id, held_fields, held_refs, extraction_schema_version)

    @classmethod
    def _from_parts(
        cls, fingerprint: str, held_id: Any, held_fields: Any, held_refs: Any, extraction_schema_version: int,
    ) -> "AnalysisSnapshot":
        """`create` が最後に作る snapshot（digest と `retained_form` の写しから）。"""

        return cls(
            snapshot_id=held_id,
            semantic_fields=held_fields,
            semantic_fingerprint=fingerprint,
            extraction_schema_version=extraction_schema_version,
            diagnostic_refs=held_refs,
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
        """Freeze the semantic extraction result, excluding mutable proof state.

        Issue #219: 同じ read-set の本体は pair の中で作り直さない。再利用するかどうかは
        snapshot の再利用の owner（`snapshot_reuse.reuse_or_build`）だけが決め、作るのは
        常に `_build_from_function_analysis`（この snapshot の唯一の本体）。
        """

        from scripts.function_tracer_pcode.proof.obligations import snapshot_reuse

        return snapshot_reuse.reuse_or_build(cls, analysis)

    @classmethod
    def _build_from_function_analysis(cls, analysis: Any) -> "AnalysisSnapshot":
        """snapshot の本体（再利用の判断をしない。main の本体と同じ読み・同じ結果）。"""

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
            target_parts=snapshot_serialization_target(analysis),
        ) as work:
            material = snapshot_material(analysis, to_dict, work)
            return cls.create(
                material.snapshot_id,
                material.semantic_fields,
                diagnostic_refs=material.diagnostic_refs,
            )


class SnapshotMaterial(NamedTuple):
    """snapshot を作る材料（`AnalysisSnapshot.create` の引数そのもの）。

    本体と、再利用の witness（`snapshot_reuse`）は **同じ** `snapshot_material` で作る:
    schema・identity の材料を足すのはここだけで、再利用の側は列挙を持たない。
    """

    snapshot_id: Tuple[Any, ...]
    semantic_fields: Dict[str, Any]
    diagnostic_refs: Dict[str, Any]


def snapshot_serialization_target(analysis: Any) -> Tuple[Any, ...]:
    """snapshot 1 つ分の直列化の target（限界の identity の材料）。"""

    return (
        "function_analysis_snapshot",
        getattr(analysis, "binary_id", None),
        getattr(analysis, "function_name", None),
        getattr(analysis, "entry_point", None),
    )


def snapshot_material(
    analysis: Any, to_dict: Any, work: Any, leaf_substitution: Any = None,
) -> SnapshotMaterial:
    """解析から snapshot の材料を作る（**唯一の抽出**。`work` は開いた直列化の作業量）。

    `leaf_substitution`（`core/budget_policy.LeafSubstitution`）は、意味の view（`semantic_snapshot_dict` /
    `to_dict()`）の walk の間だけ効き、それを使うのは、その walk（view が walk の外から始めた LEGACY の構築）だけ
    （`SerializationWork.claim_leaf_substitution`: その間、同じ thread の別の walk（新しい context のものも）・別の
    thread の walk・walk の中の producer が始めた walk は置き換えを受け取らない）。token になり得るのは、その walk が
    record の field の値・列の要素として置く葉だけ（walker は key を `json_items` の名前から作り、set を作らない）。
    入力の code が token を受け取ることは無いので、`snapshot_id`・効果要約の投影・診断の参照に token は来ない
    （入力が作った同じ型の object は token ではない: `PlacedTokens`）。
    """

    # 解析前提でない derived proof は下で捨てるので、表現できる解析は最初から
    # 作らない（`semantic_snapshot_dict`。残りは `to_dict()` と同じ値）
    semantic_view = getattr(analysis, "semantic_snapshot_dict", None)
    if leaf_substitution is not None and not _view_returns_its_walk(analysis):
        # 置き換えた葉を受け取るのが view 自身の code になり得る（view が walk の結果を読む・作り直す）
        leaf_substitution = None
    with substituting_leaves(work, leaf_substitution):
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
    return SnapshotMaterial(
        snapshot_id,
        semantic_fields,
        {"function_ref": function_ref, "analysis_notes": diagnostic_notes},
    )


def _view_returns_its_walk(analysis: Any) -> bool:
    """`analysis` の意味の view が、owner（`core/analysis.FunctionReturnAnalysis`）の定義のままで、walk の結果を
    そのまま返すか（置き換えた葉を受け取るのが snapshot の材料だけである、と言える view か）。

    型そのもので、view（`semantic_snapshot_dict` → `_materialize`）を instance・class のどちらでも置き換えて
    いないときだけ。それ以外の view では置き換えない（読みは同じ 1 回: 置き換えないだけ）。
    """

    from scripts.function_tracer_pcode.core.analysis import FunctionReturnAnalysis

    if type(analysis) is not FunctionReturnAnalysis:
        return False
    instance = getattr(analysis, "__dict__", {})
    if "semantic_snapshot_dict" in instance or "_materialize" in instance:
        return False
    namespace = FunctionReturnAnalysis.__dict__
    return (
        namespace.get("semantic_snapshot_dict") is _CANONICAL_VIEW[0]
        and namespace.get("_materialize") is _CANONICAL_VIEW[1]
    )


def _canonical_view() -> Tuple[Any, Any]:
    from scripts.function_tracer_pcode.core.analysis import FunctionReturnAnalysis

    namespace = FunctionReturnAnalysis.__dict__
    return namespace["semantic_snapshot_dict"], namespace["_materialize"]


class SnapshotRead(NamedTuple):
    """canonical な生成経路の本体が読んだもの（`read_snapshot_inputs`）。snapshot はこれの純粋な関数。

    token（`leaf_substitution` が置いた値）は、意味の view の木から写した `frozen_payload` / `held_fields` の中に
    だけある（view の walk だけが置き換えを使い、入力の code へは渡らない）。token として扱うのは `placed` にある
    object そのものだけ。
    """

    #: `create` の digest が凍結する値（`fingerprint_payload` の codec の写し）の JSON の digest。token は値の identity の
    #: 印で書く（`witness_fingerprint_digest`）。token が無ければ `create` の fingerprint そのもの
    frozen_digest: str
    #: token を含む codec の写し（token はそのまま。token が無ければ `None`: `create` と同じく、写しは digest の後すぐ
    #: 手放し、`retained_form` の写しを作る間に持たない）
    frozen_payload: Any
    #: `create` が snapshot に置く値（`retained_form`。token はそのまま）
    held_id: Tuple[Any, ...]
    held_fields: Any
    held_refs: Any
    #: この読みの直列化が描いた runtime ref の表現（`SerializationWork.observed_runtime_ref`）
    observed_runtime_ref: Callable[[Any, Any], Any]
    #: この読みの直列化の作業量が数えた byte の大きさ（置き換えた葉も数える。数えない作業量では 0）
    serialized_bytes: int
    #: この読みの葉の置き換えが置いた token（token を扱う唯一の許可。置かなければ `NO_PLACED_TOKENS`）
    placed: PlacedTokens


def read_snapshot_inputs(analysis: Any, leaf_substitution: Any = None) -> SnapshotRead:
    """`_build_from_function_analysis` と **同じ読みを同じ順に 1 回** 行い、snapshot を作る前で止める。

    同じ scope（site・target・上限・観測）の中で、抽出・digest の凍結・`retained_form` を本体と同じ順に行う。
    入力の code（解析の view・record の protocol・`stable_key`）を走らせるのはここだけで、`assemble_snapshot`
    は読んだ値から snapshot を作る純粋な関数。`leaf_substitution` が置き換えた葉は、作業量の量・上限の超過・
    観測値を変えない（`core/budget_policy.substituting_leaves`）。
    """

    to_dict = getattr(analysis, "to_dict", None)
    if not callable(to_dict):
        raise TypeError("analysis must provide object-derived to_dict() data")
    with serialization_scope(
        site=SNAPSHOT_SERIALIZATION_SITE,
        target_parts=snapshot_serialization_target(analysis),
    ) as work:
        material = snapshot_material(analysis, to_dict, work, leaf_substitution)
        # token を扱う許可は、この読みの置き換えが置いた token だけ（`PlacedTokens`）。置かなければ本体と同じ通常の
        # 凍結（`_freeze_unmetered`）
        placed = placed_tokens_of(leaf_substitution)
        frozen = SnapshotFingerprintCodec._freeze_placing(
            fingerprint_payload(material.snapshot_id, material.semantic_fields, SNAPSHOT_EXTRACTION_SCHEMA_VERSION),
            placed if placed else None,
        )
        # `create` と同じく、codec の写しは digest にしてから `retained_form` の写しを作る（token が無ければ写しを
        # 手放す: 大きな写しを、次の写しを作る間に持ち越さない）
        has_tokens = False
        if placed:
            frozen_digest, has_tokens = _marked_fingerprint_digest(frozen, placed)
        if not has_tokens:
            # token が写しに無い（置かなかった・置いた葉が fingerprint の材料に残らなかった）: digest は本体と同じ writer
            frozen_digest = SnapshotFingerprintCodec.digest_frozen(frozen)
            frozen = None
        held_id, held_fields, held_refs = retained_form(
            material.snapshot_id, material.semantic_fields, material.diagnostic_refs,
        )
    return SnapshotRead(
        frozen_digest, frozen, held_id, held_fields, held_refs, work.observed_runtime_ref, work.consumed, placed,
    )


def assemble_snapshot(read: SnapshotRead) -> "AnalysisSnapshot":
    """読んだ値から、`create` と同じ snapshot を作る（純粋: 入力の code を呼ばない）。

    読みが置いた token（`read.placed`）を、token が代わりに置かれた値の木に戻す: digest は凍結した写しの中で、
    snapshot に置く値は `retained_form` の写しの中で。token を置かなかった読みでは戻す走査をしない。codec の写しに
    token が無ければ、読みが求めた digest がそのまま fingerprint（`create` の残りそのもの）。
    """

    held = read.held_fields
    if read.placed:
        held = _expand_held_tokens(held, read.placed)
    fingerprint = read.frozen_digest
    if read.frozen_payload is not None:
        fingerprint = SnapshotFingerprintCodec.digest_frozen(expand_witness_tokens(read.frozen_payload, read.placed))
    return AnalysisSnapshot._from_parts(
        fingerprint,
        read.held_id,
        held,
        read.held_refs,
        SNAPSHOT_EXTRACTION_SCHEMA_VERSION,
    )


def canonical_generation_path(cls: Any) -> bool:
    """`cls.from_function_analysis` の生成経路が、`read_snapshot_inputs` / `assemble_snapshot` が再現する経路か。

    `AnalysisSnapshot` そのもので、本体（`_build_from_function_analysis`）と `create` が定義のままのときだけ。
    派生の型・置き換えた本体は、ここが再現しない生成経路（通常の本体へ回す）。
    """

    if cls is not AnalysisSnapshot:
        return False
    namespace = AnalysisSnapshot.__dict__
    codec = SnapshotFingerprintCodec.__dict__
    return (
        namespace.get("create") is _CANONICAL_CREATE
        and namespace.get("_build_from_function_analysis") is _CANONICAL_BUILD
        and namespace.get("_from_parts") is _CANONICAL_FROM_PARTS
        # 本体の `create` が通る codec の入口（`digest` → `freeze` → `_freeze_unmetered`）も定義のまま
        and codec.get("digest") is _CANONICAL_CODEC[0]
        and codec.get("freeze") is _CANONICAL_CODEC[1]
        and codec.get("_freeze_unmetered") is _CANONICAL_CODEC[2]
        and codec.get("digest_frozen") is _CANONICAL_CODEC[3]
        and codec.get("_freeze_placing") is _CANONICAL_CODEC[4]
    )


_CANONICAL_CREATE = AnalysisSnapshot.__dict__["create"]
_CANONICAL_BUILD = AnalysisSnapshot.__dict__["_build_from_function_analysis"]
_CANONICAL_FROM_PARTS = AnalysisSnapshot.__dict__["_from_parts"]
_CANONICAL_CODEC = tuple(
    SnapshotFingerprintCodec.__dict__[name]
    for name in ("digest", "freeze", "_freeze_unmetered", "digest_frozen", "_freeze_placing")
)
_CANONICAL_VIEW = _canonical_view()


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

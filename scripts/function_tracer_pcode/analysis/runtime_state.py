"""Long-lived mutable runtime state of :class:`ReturnAnalyzer` (Phase 6a-2)."""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Dict, List, Mapping, Optional, Set, Tuple

from scripts.function_tracer_pcode.core.analysis import FunctionReturnAnalysis
from scripts.function_tracer_pcode.core.runtime_refs import ExpansionBudgetTruncation


CALLEE_PARAMETER_CACHE_DIAGNOSTICS_SCHEMA = "callee-parameter-decompile-cache-v1"


def _copy_parameter_descriptor(parameter: Any) -> Any:
    """parameter descriptor 1 件を、共有可変状態を残さない形で複製する。

    ``storage`` だけが入れ子の dict なのでそこまでを複製し、``data_type_obj`` の
    ような Ghidra 側 object は所有権が無いので参照のまま持つ（複製しない）。
    """
    if not isinstance(parameter, Mapping):
        return parameter
    copied = dict(parameter)
    storage = copied.get("storage")
    if isinstance(storage, Mapping):
        copied["storage"] = dict(storage)
    return copied


@dataclass(frozen=True)
class SuccessfulDecompileParameterSnapshot:
    """成功した callee decompile 1 回分の完全な parameter descriptor 群（Issue #47 PR-A）。

    ``effect_summary_parameter_cache`` が「今までに見えた中で最も豊富な descriptor」の
    partial cache であるのに対し、この snapshot は **decompile が完了し HighFunction が
    存在した** 場合にだけ作る complete な観測結果である。したがってこれだけが
    「同じ callee をもう一度 decompile し直す代わりに使える」freshness evidence になる。

    失敗した decompile・HighFunction 欠落からは決して作らない（``high_function_present``
    が偽なら構築時に拒否する）。``decompile_contract_id`` / ``program_identity`` は
    「どの条件で観測したか」を保持し、条件が違う要求には再利用しない。
    """

    parameters: Tuple[Any, ...]
    decompile_contract_id: str
    program_identity: Optional[int]
    high_function_present: bool = True

    def __post_init__(self) -> None:
        if not self.high_function_present:
            raise ValueError(
                "SuccessfulDecompileParameterSnapshot requires a present HighFunction"
            )

    @classmethod
    def from_successful_decompile(
        cls,
        parameters: Optional[List[Dict]],
        *,
        decompile_contract_id: str,
        program_identity: Optional[int],
    ) -> "SuccessfulDecompileParameterSnapshot":
        return cls(
            parameters=tuple(_copy_parameter_descriptor(param) for param in (parameters or [])),
            decompile_contract_id=str(decompile_contract_id),
            program_identity=program_identity,
            high_function_present=True,
        )

    def matches_observation_contract(
        self,
        *,
        decompile_contract_id: str,
        program_identity: Optional[int],
    ) -> bool:
        return (
            self.decompile_contract_id == str(decompile_contract_id)
            and self.program_identity == program_identity
        )

    def materialize_parameters(self) -> List[Dict]:
        """呼び出し側が自由に書き換えてよい複製を返す（snapshot 本体は共有しない）。"""
        return [_copy_parameter_descriptor(param) for param in self.parameters]


@dataclass
class CalleeParameterDecompileCacheStats:
    """callee parameter snapshot cache の hit/miss 計数（診断専用・判定には使わない）。

    ``hits`` は decompile を 1 回省けたこと、``misses`` は snapshot を再利用できず
    decompile を実行したことを表す。``miss_reasons`` は「なぜ再利用できなかったか」、
    ``uncacheable_reasons`` は「decompile したのに snapshot を作れなかった / そもそも
    decompile に到達しなかった」理由の内訳。
    """

    hits: int = 0
    misses: int = 0
    snapshots_stored: int = 0
    invalidations: int = 0
    miss_reasons: Dict[str, int] = field(default_factory=dict)
    uncacheable_reasons: Dict[str, int] = field(default_factory=dict)

    def record_hit(self) -> None:
        self.hits += 1

    def record_miss(self, reason: str) -> None:
        self.misses += 1
        self.miss_reasons[reason] = self.miss_reasons.get(reason, 0) + 1

    def record_uncacheable(self, reason: str) -> None:
        self.uncacheable_reasons[reason] = self.uncacheable_reasons.get(reason, 0) + 1

    def record_snapshot_stored(self) -> None:
        self.snapshots_stored += 1

    def record_invalidation(self, entries: int) -> None:
        """実際に snapshot を捨てた無効化だけを数える（空 cache の通知は数えない）。"""
        if entries > 0:
            self.invalidations += 1

    def snapshot(self) -> Dict[str, Any]:
        return {
            "schema": CALLEE_PARAMETER_CACHE_DIAGNOSTICS_SCHEMA,
            "hits": self.hits,
            "misses": self.misses,
            "snapshots_stored": self.snapshots_stored,
            "invalidations": self.invalidations,
            "miss_reasons": dict(sorted(self.miss_reasons.items())),
            "uncacheable_reasons": dict(sorted(self.uncacheable_reasons.items())),
        }


CALLEE_ANALYSIS_CACHE_DIAGNOSTICS_SCHEMA = "callee-analysis-cache-v1"

# ``_analysis_scope_key()`` の構成要素で分類した miss 原因（診断専用のラベル）。
# 分類そのものは ``analysis.returns.lifecycle`` の純関数が行う。
CALLEE_ANALYSIS_MISS_TARGET_FIRST = "target_first_analysis"
CALLEE_ANALYSIS_MISS_BOUND_SIGNATURE = "bound_signature_differs"
CALLEE_ANALYSIS_MISS_STORAGE_BOUND_SIGNATURE = "storage_bound_signature_differs"
CALLEE_ANALYSIS_MISS_BOTH_SIGNATURES = "bound_and_storage_bound_signature_differ"
CALLEE_ANALYSIS_MISS_UNCLASSIFIED = "unclassified"

# 1 pair の診断 JSON が無制限に伸びないための上限。超えた分は件数だけ残す。
CALLEE_ANALYSIS_CACHE_TARGET_REPORT_LIMIT = 50


@dataclass
class CalleeAnalysisTargetStats:
    """1 つの解析対象（callee / top-level）についての analysis cache 計数。"""

    identity: str
    is_external: Optional[bool] = None
    is_thunk: Optional[bool] = None
    # thunk の場合、その先が external か。「本体を持つ internal callee」と
    # 「external への thunk」を診断だけで区別するために持つ（#47-B / #47-C の切り分け）。
    thunked_is_external: Optional[bool] = None
    hits: int = 0
    misses: int = 0
    miss_reasons: Dict[str, int] = field(default_factory=dict)
    # 束縛付き要求が miss し、かつ再利用できる unbound entry も無かった回数
    # （「unbound entry 不在」。PR-47-B / PR-47-C が対象にする形の miss）。
    bound_misses_without_unbound_entry: int = 0
    # 同一 target を何通りの scope key で解析したか（診断用の観測値）。
    distinct_scope_keys: int = 0

    def snapshot(self) -> Dict[str, Any]:
        payload: Dict[str, Any] = {
            "target": self.identity,
            "hits": self.hits,
            "misses": self.misses,
            "miss_reasons": dict(sorted(self.miss_reasons.items())),
            "bound_misses_without_unbound_entry": self.bound_misses_without_unbound_entry,
            "distinct_scope_keys": self.distinct_scope_keys,
        }
        payload.update(binding_induced_miss_counts(self.miss_reasons))
        if self.is_external is not None:
            payload["is_external"] = bool(self.is_external)
        if self.is_thunk is not None:
            payload["is_thunk"] = bool(self.is_thunk)
        if self.thunked_is_external is not None:
            payload["thunked_is_external"] = bool(self.thunked_is_external)
        return payload


@dataclass
class CalleeAnalysisCacheStats:
    """``call_analysis_cache`` の hit/miss と miss 原因の計数（診断専用・判定に使わない）。

    ``callee_parameter_decompile_stats`` が parameter descriptor の snapshot cache を見るのに
    対し、こちらは **callee 解析そのもの** の cache（``_analysis_scope_key()`` で引く
    ``call_analysis_cache``）を見る。両者は対象が違うので混ぜない。

    miss 原因は ``_analysis_scope_key()`` の構成要素で分類する。key の意味自体は変えない。
    ``analyze_function()`` は top-level 関数の解析にも使われるので、pair ごとに top-level 1 件が
    ``target_first_analysis`` の miss として現れる。
    """

    hits: int = 0
    misses: int = 0
    miss_reasons: Dict[str, int] = field(default_factory=dict)
    bound_misses_without_unbound_entry: int = 0
    targets: Dict[str, CalleeAnalysisTargetStats] = field(default_factory=dict)

    def _target(
        self,
        identity: str,
        *,
        is_external: Optional[bool] = None,
        is_thunk: Optional[bool] = None,
        thunked_is_external: Optional[bool] = None,
    ) -> CalleeAnalysisTargetStats:
        entry = self.targets.get(identity)
        if entry is None:
            entry = CalleeAnalysisTargetStats(
                identity=identity,
                is_external=is_external,
                is_thunk=is_thunk,
                thunked_is_external=thunked_is_external,
            )
            self.targets[identity] = entry
        return entry

    def record_hit(
        self,
        identity: str,
        *,
        is_external: Optional[bool] = None,
        is_thunk: Optional[bool] = None,
        thunked_is_external: Optional[bool] = None,
    ) -> None:
        self.hits += 1
        self._target(
            identity,
            is_external=is_external,
            is_thunk=is_thunk,
            thunked_is_external=thunked_is_external,
        ).hits += 1

    def record_miss(
        self,
        identity: str,
        reason: str,
        *,
        is_external: Optional[bool] = None,
        is_thunk: Optional[bool] = None,
        thunked_is_external: Optional[bool] = None,
        unbound_entry_absent: bool = False,
        same_target_scope_keys: int = 0,
    ) -> None:
        self.misses += 1
        self.miss_reasons[reason] = self.miss_reasons.get(reason, 0) + 1
        entry = self._target(
            identity,
            is_external=is_external,
            is_thunk=is_thunk,
            thunked_is_external=thunked_is_external,
        )
        entry.misses += 1
        entry.miss_reasons[reason] = entry.miss_reasons.get(reason, 0) + 1
        # この miss 自身が新しい scope key なので、観測済み key 数 + 1 を保持する。
        entry.distinct_scope_keys = max(entry.distinct_scope_keys, int(same_target_scope_keys) + 1)
        if unbound_entry_absent:
            self.bound_misses_without_unbound_entry += 1
            entry.bound_misses_without_unbound_entry += 1

    def snapshot(self) -> Dict[str, Any]:
        ordered = sorted(
            self.targets.values(), key=lambda entry: (-entry.misses, -entry.hits, entry.identity)
        )
        reported = ordered[:CALLEE_ANALYSIS_CACHE_TARGET_REPORT_LIMIT]
        payload: Dict[str, Any] = {
            "schema": CALLEE_ANALYSIS_CACHE_DIAGNOSTICS_SCHEMA,
            "hits": self.hits,
            "misses": self.misses,
            "miss_reasons": dict(sorted(self.miss_reasons.items())),
            "bound_misses_without_unbound_entry": self.bound_misses_without_unbound_entry,
            "targets": [entry.snapshot() for entry in reported],
            **binding_induced_miss_counts(self.miss_reasons),
            "targets_truncated": max(0, len(ordered) - len(reported)),
            "repeated_miss_targets": repeated_miss_targets(
                entry.snapshot() for entry in ordered
            ),
        }
        return payload


def binding_induced_miss_counts(miss_reasons: Optional[Mapping[str, int]]) -> Dict[str, int]:
    """miss 原因の内訳から、束縛差が原因の miss 回数を成分ごとに数える。

    「両方違う」は bound / storage-bound の双方に数える（どちらの成分でも再解析を
    引き起こしているため）。内訳は ``miss_reasons`` にそのまま残るので情報は失わない。
    """
    reasons = dict(miss_reasons or {})
    both = int(reasons.get(CALLEE_ANALYSIS_MISS_BOTH_SIGNATURES, 0) or 0)
    return {
        "bound_signature_induced_misses": int(
            reasons.get(CALLEE_ANALYSIS_MISS_BOUND_SIGNATURE, 0) or 0
        )
        + both,
        "storage_bound_signature_induced_misses": int(
            reasons.get(CALLEE_ANALYSIS_MISS_STORAGE_BOUND_SIGNATURE, 0) or 0
        )
        + both,
    }


def repeated_miss_targets(target_snapshots) -> Dict[str, List[str]]:
    """同じ理由で 2 回以上 miss した target を理由ごとに列挙する。

    「同一 target で ``bound_signature`` 起因の miss が複数回起きたか」を、
    こちらで解釈を加えずに機械判定できるようにするための集計。
    """
    grouped: Dict[str, List[str]] = {}
    for entry in target_snapshots:
        for reason, count in (entry.get("miss_reasons") or {}).items():
            if int(count or 0) >= 2:
                grouped.setdefault(reason, []).append(str(entry.get("target")))
    return {reason: sorted(targets) for reason, targets in sorted(grouped.items())}


CALLEE_UNBOUND_REUSE_DIAGNOSTICS_SCHEMA = "callee-unbound-reuse-v1"

# 束縛ゼロ解析を再利用してよいか（Issue #47 PR-B）の判定ラベル。判定そのものは
# ``analysis.returns.callee_unbound_reuse`` が行い、ここは所有する状態の語彙だけを持つ。
UNBOUND_REUSE_ELIGIBLE = "eligible_external_placeholder"
UNBOUND_REUSE_CALLEE_IS_INTERNAL = "callee_is_internal"
UNBOUND_REUSE_EXTERNAL_RESOLUTION_AMBIGUOUS = "external_resolution_ambiguous"
UNBOUND_REUSE_DECOMPILE_INCOMPLETE = "decompile_incomplete"
UNBOUND_REUSE_HIGH_FUNCTION_MISSING = "high_function_missing"
UNBOUND_REUSE_PCODE_BODY_PRESENT = "pcode_body_present"
UNBOUND_REUSE_PCODE_BODY_UNREADABLE = "pcode_body_unreadable"
UNBOUND_REUSE_CACHE_KEY_UNAVAILABLE = "cache_key_unavailable"
UNBOUND_REUSE_UNBOUND_ANALYSIS_UNAVAILABLE = "unbound_analysis_unavailable"


@dataclass(frozen=True)
class CalleeUnboundReuseVerdict:
    """1 つの callee について「束縛ゼロ解析を再利用してよいか」の静的判定。

    ``eligible`` が真になるのは、external と確定していて解決が曖昧でなく、decompile が
    完了し HighFunction があり、その本体に「戻る」以外の P-code が無い場合だけ
    （= この binary に本体が無い placeholder）。それ以外は ``reason`` に不適格の理由を
    持ち、呼び出し側は従来の bound-sensitive 経路を使う。

    ``program_identity`` は判定を観測した program。program が変われば判定し直す。
    """

    eligible: bool
    reason: str
    program_identity: Optional[int] = None
    resolution_reason: Optional[str] = None


@dataclass
class CalleeUnboundReuseTargetStats:
    """1 つの callee についての再利用計数（診断専用）。"""

    identity: str
    eligible: Optional[bool] = None
    verdict_reason: Optional[str] = None
    resolution_reason: Optional[str] = None
    unbound_analyses: int = 0
    reuses: int = 0
    declines: Dict[str, int] = field(default_factory=dict)
    shadow_comparisons: int = 0
    shadow_mismatches: int = 0

    def snapshot(self) -> Dict[str, Any]:
        payload: Dict[str, Any] = {
            "target": self.identity,
            "unbound_analyses": self.unbound_analyses,
            "reuses": self.reuses,
            "shadow_comparisons": self.shadow_comparisons,
            "shadow_mismatches": self.shadow_mismatches,
            "declines": dict(sorted(self.declines.items())),
        }
        if self.eligible is not None:
            payload["eligible"] = bool(self.eligible)
        if self.verdict_reason is not None:
            payload["verdict_reason"] = self.verdict_reason
        if self.resolution_reason is not None:
            payload["resolution_reason"] = self.resolution_reason
        return payload


@dataclass
class CalleeUnboundReuseCacheOwnership:
    """PR-47-B が再利用の根拠として使った ``call_analysis_cache`` entry の追跡。

    Program を書き換えると、その前に得た decompile 由来の解析は根拠として使えない。
    適格判定（``callee_unbound_reuse_verdicts``）を捨てるだけでは足りず、判定に基づいて

    - 束縛ゼロ scope に作った解析（再利用の authority 本体）
    - そこから materialize した束縛 scope の view
    - 同じ束縛ゼロ解析を指す generic ``_function_cache_key`` の別名

    が cache に残っていると、``analyze_function()`` 冒頭の cache 参照が適格判定より先に
    書き換え前の解析を返してしまう。ここで所有権を追跡し、Program 変更時に **この範囲
    だけ** を落とす（無関係な解析結果は残す）。

    entry は identity で照合してから落とす。同じ key を別の経路が書き換えていた場合、
    それは PR-47-B の authority ではないので巻き添えにしない。
    """

    unbound_authorities: Dict[Tuple[Any, ...], Any] = field(default_factory=dict)
    view_authorities: Dict[Tuple[Any, ...], Any] = field(default_factory=dict)
    # generic ``_function_cache_key`` → その別名が指す束縛ゼロ scope key
    generic_alias_keys: Dict[Tuple[Any, ...], Tuple[Any, ...]] = field(default_factory=dict)

    def record_unbound_authority(self, unbound_key: Tuple[Any, ...], analysis: Any) -> None:
        """束縛ゼロ解析を再利用の根拠として使ったことを記録する。"""
        if unbound_key is None or analysis is None:
            return
        self.unbound_authorities[unbound_key] = analysis

    def record_view(self, view_key: Tuple[Any, ...], view: Any) -> None:
        """束縛 scope へ materialize した view を cache に置いたことを記録する。"""
        if view_key is None or view is None:
            return
        self.view_authorities[view_key] = view

    def record_generic_alias(
        self, generic_key: Tuple[Any, ...], unbound_key: Tuple[Any, ...]
    ) -> None:
        """generic key が同じ束縛ゼロ解析を指していることを記録する。"""
        if generic_key is None or unbound_key is None:
            return
        self.generic_alias_keys[generic_key] = unbound_key

    def owned_keys(self) -> Tuple[Tuple[Any, ...], ...]:
        return tuple(self.view_authorities) + tuple(self.generic_alias_keys) + tuple(
            self.unbound_authorities
        )

    def evict_from(self, cache: Dict[Tuple[Any, ...], Any]) -> int:
        """所有している entry だけを cache から落とし、追跡を空にする。"""
        removed = 0
        for key, view in self.view_authorities.items():
            if cache.get(key) is view:
                del cache[key]
                removed += 1
        for generic_key, unbound_key in self.generic_alias_keys.items():
            owned = self.unbound_authorities.get(unbound_key)
            if owned is not None and cache.get(generic_key) is owned:
                del cache[generic_key]
                removed += 1
        for key, analysis in self.unbound_authorities.items():
            if cache.get(key) is analysis:
                del cache[key]
                removed += 1
        self.clear()
        return removed

    def clear(self) -> None:
        self.unbound_authorities.clear()
        self.view_authorities.clear()
        self.generic_alias_keys.clear()


@dataclass
class CalleeUnboundReuseStats:
    """eligible external placeholder の束縛ゼロ解析再利用の計数（診断専用）。

    ``reuses`` は「束縛付き要求を、callee を解析し直さずに満たした回数」= 削減できた
    callee 解析回数。``unbound_analyses`` は実際に走らせた束縛ゼロ解析の回数。
    ``shadow_mismatches`` は shadow validation で従来経路と一致しなかった回数で、
    0 でないなら再利用は採用されていない（従来結果を採る）。
    """

    reuses: int = 0
    unbound_analyses: int = 0
    shadow_comparisons: int = 0
    shadow_mismatches: int = 0
    # Program 変更で再利用の根拠（判定と cache entry）を捨てた回数と、落とした entry 数。
    invalidations: int = 0
    evicted_cache_entries: int = 0
    verdicts: Dict[str, int] = field(default_factory=dict)
    declines: Dict[str, int] = field(default_factory=dict)
    targets: Dict[str, CalleeUnboundReuseTargetStats] = field(default_factory=dict)

    def _target(self, identity: str) -> CalleeUnboundReuseTargetStats:
        entry = self.targets.get(identity)
        if entry is None:
            entry = CalleeUnboundReuseTargetStats(identity=identity)
            self.targets[identity] = entry
        return entry

    def record_verdict(self, identity: str, verdict: CalleeUnboundReuseVerdict) -> None:
        """callee ごとに 1 回だけ確定する静的判定を記録する。"""
        self.verdicts[verdict.reason] = self.verdicts.get(verdict.reason, 0) + 1
        entry = self._target(identity)
        entry.eligible = bool(verdict.eligible)
        entry.verdict_reason = verdict.reason
        entry.resolution_reason = verdict.resolution_reason

    def record_unbound_analysis(self, identity: str) -> None:
        self.unbound_analyses += 1
        self._target(identity).unbound_analyses += 1

    def record_reuse(self, identity: str) -> None:
        self.reuses += 1
        self._target(identity).reuses += 1

    def record_decline(self, identity: str, reason: str) -> None:
        """eligible だったが、この要求では再利用しなかった理由。"""
        self.declines[reason] = self.declines.get(reason, 0) + 1
        entry = self._target(identity)
        entry.declines[reason] = entry.declines.get(reason, 0) + 1

    def record_invalidation(self, verdicts: int, evicted_cache_entries: int) -> None:
        """実際に何かを捨てた無効化だけを数える（空状態の通知は数えない）。"""
        if verdicts <= 0 and evicted_cache_entries <= 0:
            return
        self.invalidations += 1
        self.evicted_cache_entries += int(evicted_cache_entries)

    def record_shadow(self, identity: str, matched: bool) -> None:
        self.shadow_comparisons += 1
        entry = self._target(identity)
        entry.shadow_comparisons += 1
        if not matched:
            self.shadow_mismatches += 1
            entry.shadow_mismatches += 1

    def snapshot(self) -> Dict[str, Any]:
        ordered = sorted(
            self.targets.values(),
            key=lambda entry: (-entry.reuses, -entry.unbound_analyses, entry.identity),
        )
        reported = ordered[:CALLEE_ANALYSIS_CACHE_TARGET_REPORT_LIMIT]
        return {
            "schema": CALLEE_UNBOUND_REUSE_DIAGNOSTICS_SCHEMA,
            "reuses": self.reuses,
            "unbound_analyses": self.unbound_analyses,
            "shadow_comparisons": self.shadow_comparisons,
            "shadow_mismatches": self.shadow_mismatches,
            "invalidations": self.invalidations,
            "evicted_cache_entries": self.evicted_cache_entries,
            "verdicts": dict(sorted(self.verdicts.items())),
            "declines": dict(sorted(self.declines.items())),
            "targets": [entry.snapshot() for entry in reported],
            "targets_truncated": max(0, len(ordered) - len(reported)),
            "shadow_mismatch_targets": sorted(
                entry.identity for entry in ordered if entry.shadow_mismatches > 0
            ),
        }


@dataclass
class AnalysisRuntimeState:
    """State whose lifetime is the analyzer's, not one nested analysis context.

    :class:`~scripts.function_tracer_pcode.analysis.session.AnalysisSession` holds the
    per-analysis fields that ``_analysis_context`` pushes and pops.  This object holds the
    long-lived mutable state that must survive across nested analyses: memo caches, the
    direct call graph and its completed-node set, the in-progress recursion guard, and the
    deferred-call sequence counter.  It is deliberately *not* only caches, hence the name.

    Configuration/limits (``bounded_call_*``), the decompiler resource and diagnostic status
    stay outside this object (Phase 6a-3 / #77 / Phase 6a-4).  ``ReturnAnalyzer`` exposes
    every field through a property pair so the existing ``analyzer.<name>`` seams
    (read, in-place mutation, direct assignment, ``+=``) keep working unchanged.
    """

    call_analysis_cache: Dict[Tuple[Any, ...], Optional[FunctionReturnAnalysis]] = field(default_factory=dict)
    local_target_cache: Dict[Tuple[object, ...], Optional[List[Any]]] = field(default_factory=dict)
    effect_summary_cache: Dict[Tuple[Any, ...], Any] = field(default_factory=dict)
    effect_summary_parameter_cache: Dict[Tuple[Any, ...], List[Dict]] = field(default_factory=dict)
    # Issue #47 (PR-A): 成功した decompile から得た complete な parameter snapshot。
    # ``effect_summary_parameter_cache`` は partial/richer descriptor cache のままで、
    # 「decompile をもう一度やらずに済む」根拠になるのはこちらだけ。
    callee_parameter_decompile_cache: Dict[
        Tuple[Any, ...], SuccessfulDecompileParameterSnapshot
    ] = field(default_factory=dict)
    callee_parameter_decompile_stats: CalleeParameterDecompileCacheStats = field(
        default_factory=CalleeParameterDecompileCacheStats
    )
    # Issue #47: callee 解析そのものの cache（``call_analysis_cache``）の hit/miss と
    # miss 原因。cache 方針は変えず、観測だけを足す。
    callee_analysis_cache_stats: CalleeAnalysisCacheStats = field(
        default_factory=CalleeAnalysisCacheStats
    )
    # Issue #47 (PR-B): callee ごとに 1 回だけ確定する「束縛ゼロ解析を再利用してよいか」
    # の静的判定。decompile 由来の証拠を含むので program を書き換えたら捨てる。
    callee_unbound_reuse_verdicts: Dict[
        Tuple[Any, ...], CalleeUnboundReuseVerdict
    ] = field(default_factory=dict)
    callee_unbound_reuse_stats: CalleeUnboundReuseStats = field(
        default_factory=CalleeUnboundReuseStats
    )
    # Issue #47 (PR-B): 再利用の根拠として使った analysis cache entry の所有権。
    # Program 変更時にこの範囲だけを evict する。
    callee_unbound_reuse_cache_ownership: CalleeUnboundReuseCacheOwnership = field(
        default_factory=CalleeUnboundReuseCacheOwnership
    )
    direct_call_graph: Dict[Tuple[Any, ...], Set[Tuple[Any, ...]]] = field(default_factory=dict)
    direct_call_graph_complete_nodes: Set[Tuple[Any, ...]] = field(default_factory=set)
    analysis_in_progress: Dict[Tuple[Any, ...], FunctionReturnAnalysis] = field(default_factory=dict)
    deferred_call_counter: int = 0
    # Issue #131: 効果要約 1 件に対応する切り捨て記録。key と寿命は
    # ``effect_summary_cache`` に揃える（再構築時は置き換え、cache hit 時は同じ key
    # から参照情報を作る）。判定の根拠は保存済み要約側であり、この dict ではない。
    effect_summary_budget_diagnostics: Dict[
        Tuple[Any, ...], Tuple[ExpansionBudgetTruncation, ...]
    ] = field(default_factory=dict)

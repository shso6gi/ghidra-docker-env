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

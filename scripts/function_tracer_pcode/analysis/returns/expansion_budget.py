"""Issue #131: 展開ケース数・経路数の切り捨て marker の収集と同期。

生成（``ExpressionExpander`` / ``ConditionTracker``）→ 保持（``AnalysisSession`` /
効果要約診断 cache）→ 伝搬（利用面ごとの sink、callee 参照）→ 同期
（``FunctionReturnAnalysis``）の各段を ``ReturnAnalyzer`` 側から扱うための service
実装。PR-B からは同期時に共通の依存表で派生 authority を無効化する（判定 gate は
``proof`` 側が ``has_expansion_budget_truncation()`` を通して読む）。
"""

from __future__ import annotations

import json
import os
from typing import Any, Callable, Iterable, Optional, Tuple

from scripts.function_tracer_pcode.core.analysis import (
    invalidate_semantic_successor_fields,
)
from scripts.function_tracer_pcode.core.runtime_refs import (
    EFFECT_EXPANSION_CASE_BUDGET_EXCEEDED_REASON,
    ExpansionBudgetCollector,
    ExpansionBudgetTruncation,
    expansion_budget_event_ids,
    merge_expansion_budget_truncations,
)


def make_expansion_budget_sink(
    collector: ExpansionBudgetCollector,
    *,
    surface: str,
    owner_scope_key: Optional[Tuple[Any, ...]] = None,
) -> Callable[[Optional[ExpansionBudgetTruncation]], None]:
    """collector へ即時転送する sink を作り、利用面と所有 scope を束縛する。

    collector は生成時に捕捉する。展開の途中で callee 解析が別の scope を push しても、
    その展開が属する scope へ記録が残る（後から一括転送する二次 list は持たない）。
    """

    bound_surface = str(surface)
    bound_scope = owner_scope_key

    def sink(truncation: Optional[ExpansionBudgetTruncation]) -> None:
        if truncation is None:
            return
        collector.record(
            truncation.with_binding(
                surface=bound_surface,
                owner_scope_key=bound_scope,
            )
        )

    # 展開の所有 scope を 1 つの出どころにする: 式サイズ予算の target
    # （`expander_multiequal._checkpoint_expansion_size`）も同じ値を読む。
    sink.owner_scope_key = bound_scope
    return sink


def mark_effect_expansion_case_budget_exceeded(summary) -> bool:
    """効果要約に ``effect_expansion_case_budget_exceeded`` を 1 度だけ足す。

    Issue #131 PR-B: 効果面の切り捨ては要約自身が持つ不完全性にする。診断 dict と
    違って要約は cache に載るので、cache hit でも不完全性が失われない。
    ``incomplete_reasons`` は昇順・重複なしで保つ（v2 の効果 reason 分類がその形を
    要求する）。
    """

    reasons = tuple(getattr(summary, "incomplete_reasons", ()) or ())
    if EFFECT_EXPANSION_CASE_BUDGET_EXCEEDED_REASON in reasons:
        return False
    summary.incomplete_reasons = tuple(sorted(
        set(reasons) | {EFFECT_EXPANSION_CASE_BUDGET_EXCEEDED_REASON}
    ))
    return True


def callee_reference_truncation(
    records: Optional[Iterable[ExpansionBudgetTruncation]],
    *,
    callee_scope_key,
    owner_scope_key=None,
    label: Optional[str] = None,
    surface: str = "callee",
) -> Optional[ExpansionBudgetTruncation]:
    """採用した callee 側の記録から ``callee_analysis`` marker を 1 件作る。

    3 つを明示する:

    * 誰が利用したか … ``owner_scope_key``（利用した caller の解析/要約 scope）
    * 何を利用したか … ``callee_scope_key``
    * 何を参照したか … ``referenced_event_ids``

    callee の marker 本体は再帰コピーせず、callee scope と参照 event ID だけを持つ。
    ``owner_scope_key`` は発生事実キーに入るので、同じ callee を別 caller scope から
    利用した場合は別 event になる。記録が無ければ marker を作らない（診断欠落から
    切り捨てを推定しない）。
    """

    event_ids = expansion_budget_event_ids(records)
    if not event_ids:
        return None
    return ExpansionBudgetTruncation(
        kind="callee_analysis",
        surface=surface,
        owner_scope_key=owner_scope_key,
        callee_scope_key=callee_scope_key,
        label=label,
        referenced_event_ids=event_ids,
    )


def _impl__make_expansion_budget_sink(
    self,
    *,
    surface: str,
    owner_scope_key: Optional[Tuple[Any, ...]] = None,
    collector: Optional[ExpansionBudgetCollector] = None,
) -> Callable[[Optional[ExpansionBudgetTruncation]], None]:
    """利用面と所有 scope を束縛した即時転送 sink を作る。

    collector は生成時に捕捉する。展開の途中で callee 解析が子 session を push しても、
    その展開が属する scope へ記録が残る（後から一括転送する二次 list は持たない）。
    """

    target = (
        collector
        if collector is not None
        else self._current_expansion_budget_collector
    )
    return make_expansion_budget_sink(
        target,
        surface=surface,
        owner_scope_key=owner_scope_key,
    )


def _impl__record_expansion_budget_truncations(
    self,
    items: Optional[Iterable[ExpansionBudgetTruncation]],
    *,
    collector: Optional[ExpansionBudgetCollector] = None,
) -> None:
    """既に束縛済みの記録を、そのまま所有 scope へ取り込む。"""

    target = (
        collector
        if collector is not None
        else self._current_expansion_budget_collector
    )
    target.extend(items)


def _impl__record_callee_analysis_expansion_budget(
    self,
    analysis,
    *,
    surface: str = "callee",
    owner_scope_key=None,
    collector: Optional[ExpansionBudgetCollector] = None,
) -> None:
    """callee 解析結果を意味入力として採用した箇所で ``callee_analysis`` を残す。

    ``owner_scope_key`` は「誰が利用したか」。省略時は現在の解析 scope を使う。
    callee の marker 本体は再帰コピーせず、callee scope と参照 event ID だけを持つ。
    記録が無い callee からは marker を作らない（診断欠落から切り捨てを推定しない）。
    """

    if analysis is None:
        return
    marker = callee_reference_truncation(
        getattr(analysis, "expansion_budget_truncations", ()) or (),
        callee_scope_key=getattr(analysis, "analysis_scope_key", None),
        owner_scope_key=(
            owner_scope_key
            if owner_scope_key is not None
            else self._current_analysis_scope_key
        ),
        label=(
            analysis.function_ref.display_name()
            if getattr(analysis, "function_ref", None) is not None
            else getattr(analysis, "function_name", None)
        ),
        surface=surface,
    )
    if marker is None:
        return
    self._record_expansion_budget_truncations((marker,), collector=collector)


def _impl__absorb_effect_summary_budget_diagnostics(
    self,
    summary_cache_key,
    *,
    collector: Optional[ExpansionBudgetCollector] = None,
) -> None:
    """自分自身の効果要約の診断を、現在の解析 scope へ取り込む。

    callee 要約分は別 key の entry に入っており、caller 側の entry には
    ``callee_analysis`` marker として現れる。
    """

    if summary_cache_key is None:
        return
    self._record_expansion_budget_truncations(
        self._effect_summary_budget_diagnostics.get(summary_cache_key) or (),
        collector=collector,
    )


def _impl__sync_expansion_budget_truncations(
    self,
    result,
    *,
    collector: Optional[ExpansionBudgetCollector] = None,
):
    """解析結果の marker を「結果が既に持つ記録」と「同じ scope の session の記録」の
    和集合へ更新する。

    session が空であることを理由に結果側の marker を消さない（返された view や callee
    由来の結果が既に保持する記録を保護する）。正規化済みの全記録が同じなら何も
    変更しない（同じ記録の再同期は no-op）。

    PR-B: 記録または参照情報が増えた場合は semantic 入力が変わったということなので、
    共通の依存表（``returns`` と同じ範囲）で派生 authority を無効化する。marker の
    反映と無効化はこの 1 か所で連続して行い、途中状態を証明・cache 利用者へ
    公開しない。
    """

    if result is None:
        return result
    source = (
        collector
        if collector is not None
        else self._current_expansion_budget_collector
    )
    existing = tuple(getattr(result, "expansion_budget_truncations", ()) or ())
    merged = merge_expansion_budget_truncations(existing, source.as_tuple())
    if merged != existing:
        result.expansion_budget_truncations = merged
        invalidate_semantic_successor_fields(result, "expansion_budget_truncations")
    return result


EXPANSION_BUDGET_DIAGNOSTIC_BEGIN = "=== EXPANSION_BUDGET_DIAGNOSTIC_JSON_BEGIN ==="
EXPANSION_BUDGET_DIAGNOSTIC_END = "=== EXPANSION_BUDGET_DIAGNOSTIC_JSON_END ==="

_DIAGNOSTIC_ENV_VAR = "FT_EXPANSION_BUDGET_DIAGNOSTICS"


def expansion_budget_diagnostics_enabled(environ=None) -> bool:
    """診断出力の有効判定。既定は有効（``0``/``false``/``off`` で抑止）。"""

    source = environ if environ is not None else os.environ
    raw = str(source.get(_DIAGNOSTIC_ENV_VAR, "1")).strip().lower()
    return raw not in {"0", "false", "off", "no"}


def analysis_expansion_budget_payload(analysis) -> Optional[dict]:
    """解析結果 1 件分の診断 payload。marker が無ければ ``None``。"""

    records = tuple(getattr(analysis, "expansion_budget_truncations", ()) or ())
    if not records:
        return None
    function_ref = getattr(analysis, "function_ref", None)
    return {
        "schema": "expansion_budget_diagnostic_v1",
        "binary_id": getattr(analysis, "binary_id", None),
        "function_name": getattr(analysis, "function_name", None),
        "entry_point": getattr(analysis, "entry_point", None),
        "function_ref": (
            function_ref.to_dict()
            if function_ref is not None and callable(getattr(function_ref, "to_dict", None))
            else None
        ),
        "analysis_scope_key": _canonical_scope_key(
            getattr(analysis, "analysis_scope_key", None)
        ),
        "truncation_count": len(records),
        "truncations": [record.to_dict() for record in records],
    }


def _canonical_scope_key(value):
    from scripts.function_tracer_pcode.core.runtime_refs import _canonical_budget_value

    return _canonical_budget_value(value)


def emit_analysis_expansion_budget_diagnostics(analysis, *, stream=None) -> bool:
    """観測した切り捨てを 1 関数分だけ標準出力へ出す（判定結果は変えない）。

    ``EQUIVALENCE_RESULT_JSON`` とは別ブロックで、結果 payload・署名対象には入れない。
    debug メッセージ数上限で抑止され得る ``Too many cases`` の代わりに、これを一次資料
    として使う。
    """

    payload = analysis_expansion_budget_payload(analysis)
    if payload is None or not expansion_budget_diagnostics_enabled():
        return False
    text = "\n".join(
        (
            EXPANSION_BUDGET_DIAGNOSTIC_BEGIN,
            json.dumps(payload, ensure_ascii=False, sort_keys=True),
            EXPANSION_BUDGET_DIAGNOSTIC_END,
        )
    )
    if stream is None:
        print(text)
    else:
        stream.write(text + "\n")
    return True

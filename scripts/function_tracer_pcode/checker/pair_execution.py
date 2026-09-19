# -*- coding: utf-8 -*-
"""pair 実行制御の **consumer 側**（Issue #106 PR-106-0）。

責務の境界:

```text
core.errors.PairFailureLedger      … 記録 / 畳み込み / 優先順位 / stop state
        ↓ PairExecutionControl（安定 interface）+ PairPendingFailure（値）
checker.pair_execution             … 「今止めるべき failure」を結果へ変換する
        ↓
checker.result_assembly / authority … UNKNOWN / ERROR の判定・receipt・JSON
```

この module が持つのは **変換だけ** で、

* どの failure が勝つか（内部バグ > 限界）
* 記録をどう保存・畳み込むか
* stop state をどう上げるか

は一切知らない。台帳から受け取るのは優先順位解決済みの `PairPendingFailure`
1 件だけで、`PairFailureLedger` の内部（records / internal_bugs / limitations）
には触れない（`test_issue106_pair_limitation_propagation.py` が静的に固定する）。

新しい failure class（`AnalysisFailureError` 派生）が増えても、この module も
workflow / boundary も変更点は無い。`PairFailureKind` が 1 つ増えるとき — つまり
「UNKNOWN でも `internal_exception` ERROR でもない新しい結果の種類」を足すとき —
だけ、下の `_RESULT_FACTORY_BY_KIND` が唯一の対応点になる。
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Callable

from scripts.function_tracer_pcode.core.errors import (
    PairFailureKind,
    PairPendingFailure,
    PairStopState,
    adopt_pair_failure,
    current_pair_ledger,
    pending_pair_failure,
)
from scripts.function_tracer_pcode.checker.result_assembly import (
    INTERNAL_EXCEPTION_STATUS,
    analysis_limitation_result_for_pair,
    attach_pair_stop_state,
    internal_error_result_for_pair,
)


def pair_stop_state() -> PairStopState:
    """今の pair の stop state（scope の外では `NONE`）。"""
    ledger = current_pair_ledger()
    return PairStopState.NONE if ledger is None else ledger.stop_state()


def pair_allows_semantic_analysis() -> bool:
    """新しい意味解析を始めてよいか（phase 再解析 / conditional lane の前に読む）。"""
    return pair_stop_state().allows_semantic_analysis()


def raise_pending_pair_failure() -> None:
    """未解消の failure があればここで raise する（G1 / G2 の本体）。

    raise するのは台帳が正規化した例外なので、握り潰された内部バグは
    `InternalError`、限界は `AnalysisLimitation` として下の handler へ届く。
    """
    failure = pending_pair_failure()
    if failure is not None:
        raise failure.exception


def binary_display_name(program, fallback: str) -> str:
    return program.getName() if hasattr(program, "getName") else fallback


@dataclass(frozen=True)
class _KindHandling:
    """1 つの `PairFailureKind` について consumer が知るべきことのすべて。

    `build_result` = その種別の結果をどう組むか。
    `already_in_result` = その種別が既に結果の判定面に出ているか。

    種別が増えたときに触るのはこの表の 1 行だけで、gate 側（workflow /
    boundary）にも `pair_failure_result` 本体にも分岐は増えない。
    """

    build_result: Callable[..., Any]
    already_in_result: Callable[[Any, PairPendingFailure], bool]


def _build_limitation_result(checker, failure, **common):
    return analysis_limitation_result_for_pair(
        failure.exception,
        session=getattr(checker, "_active_v2_dual_write_pilot_session", None),
        **common,
    )


def _build_internal_bug_result(checker, failure, **common):
    return internal_error_result_for_pair(failure.exception, **common)


def _limitation_already_in_result(result, failure) -> bool:
    """EQ / NOT_EQ なら必ず作り直す。UNKNOWN / ERROR は既に出ていれば作り直さない。

    既存の ERROR を意味的な UNKNOWN へ格下げしないために、ERROR は「出ている」
    扱いにする。
    """
    if result.is_equivalent is not None:
        return False
    if getattr(result, "error_message", None):
        return True
    reason_id = getattr(failure.exception, "reason_id", None)
    return any(
        getattr(reason, "reason_id", None) == reason_id
        for reason in (getattr(result, "unknown_reasons", None) or ())
    )


def _internal_bug_already_in_result(result, failure) -> bool:
    """限界の UNKNOWN 結果であっても ERROR へ上書きする（内部バグが優先）。"""
    return getattr(result, "failure_status", None) == INTERNAL_EXCEPTION_STATUS


#: 種別 → 扱い方。`PairFailureKind` に member を足したらここへ 1 行足す。
#: 足し忘れは `KeyError` で即座に落ちる（黙って別種別として扱わない）。
_HANDLING_BY_KIND = {
    PairFailureKind.LIMITATION: _KindHandling(
        _build_limitation_result, _limitation_already_in_result,
    ),
    PairFailureKind.INTERNAL_BUG: _KindHandling(
        _build_internal_bug_result, _internal_bug_already_in_result,
    ),
}


def pair_failure_result(
    checker,
    failure: PairPendingFailure,
    *,
    function_name1: str,
    function_name2: str,
    binary1_name: str,
    binary2_name: str,
    start_time: float,
    result=None,
):
    """`PairPendingFailure` 1 件を pair の結果にする（G3 / G4-a / G5 の共通本体）。

    `result` を渡した場合は、その結果の **診断だけ** を引き継いで判定面は作り直す。
    """
    return _HANDLING_BY_KIND[failure.kind].build_result(
        checker,
        failure,
        stop_state=failure.stop_state,
        function_name1=function_name1,
        function_name2=function_name2,
        binary1_name=binary1_name,
        binary2_name=binary2_name,
        start_time=start_time,
        carry_from=result,
    )


def pair_failure_result_for_exception(
    checker,
    exc: BaseException,
    **kwargs,
):
    """境界を抜けようとした例外を pair の結果にする（G3 / G5 の入口）。

    例外そのものではなく **台帳が優先順位を解決した failure** を結果にする。
    握り潰されずに上がってきた内部バグも、`raise_limitation` を経由しなかった
    限界も、ここで同じ 1 本の経路に合流する。台帳にも型情報にも根拠が無い場合
    だけ `None` を返し、呼び出し側は従来の generic 経路へ落とす。
    """
    failure = adopt_pair_failure(exc)
    if failure is None:
        return None
    return pair_failure_result(checker, failure, **kwargs)


def apply_pair_failure_gate(
    checker,
    result,
    *,
    function_name1: str,
    function_name2: str,
    start_time: float,
):
    """未解消の failure が結果に出ないまま返させない（G3 / G4-a）。

    置き換えるのは「その failure がまだ結果に出ていない」ときだけ。同じ pair で
    G3（workflow）と G4-a（boundary）の 2 回通るので、2 度目が同じ結果を作り
    直さないように、出ているかどうかを結果そのもの（`failure_status` と
    reason 集合）から判断する。診断 block は読まない。

    「出ているか」の判定は種別ごとに `_HANDLING_BY_KIND` が持つ。どの分岐でも
    stop state は結果へ写す（診断）。

    台帳が無い（pair scope の外で呼ばれた）ときは何もしない。
    """
    if result is None:
        return result
    failure = pending_pair_failure()
    if failure is None:
        return result
    if _failure_already_in_result(result, failure):
        attach_pair_stop_state(result, failure.stop_state)
        return result
    return pair_failure_result(
        checker,
        failure,
        function_name1=(getattr(result, "function1_name", None) or function_name1),
        function_name2=(getattr(result, "function2_name", None) or function_name2),
        binary1_name=result.binary1_name,
        binary2_name=result.binary2_name,
        start_time=start_time,
        result=result,
    )


def _failure_already_in_result(result, failure: PairPendingFailure) -> bool:
    """この failure が既に結果の **判定面** に出ているか（診断 block は見ない）。"""
    return _HANDLING_BY_KIND[failure.kind].already_in_result(result, failure)


__all__ = [
    "apply_pair_failure_gate",
    "binary_display_name",
    "pair_allows_semantic_analysis",
    "pair_failure_result",
    "pair_failure_result_for_exception",
    "pair_stop_state",
    "pending_pair_failure",
    "raise_pending_pair_failure",
]


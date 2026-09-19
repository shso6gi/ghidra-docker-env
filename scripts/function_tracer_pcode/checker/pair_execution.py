# -*- coding: utf-8 -*-
"""pair 実行制御の **consumer 側** 補助（Issue #106 PR-106-0）。

台帳（`core.errors.PairFailureLedger`）を所有するのは pair 境界
（`authority/lifecycle/production_boundary.py`）で、この module は checker 側の
読み手が同じ規則を書き写さずに済むようにするだけの薄い層。ここには

* 失敗の優先順位（内部バグ > 限界）
* 「未解消の失敗があるなら、その場で例外にして handler へ渡す」（G1 / G2）
* 「その失敗がまだ結果に出ていないなら、pair 単位で組み直す」（G3 / G4-a / G5）

の 3 つだけを置く。**UNKNOWN / ERROR の最終判断も receipt も JSON も持たない**。
判定規則そのものは `checker.result_assembly` と authority が持ち、ここはどの
規則をいつ適用するかだけを決める。

G1（初回 / 再解析の直後）と G2（`check()` の result assembly 直前）はどちらも
`raise_pending_pair_failure()` を呼ぶ。限界が途中の `except Exception` に握り
潰されていても台帳には残っているので、ここで改めて例外に戻せる。
"""

from __future__ import annotations

from typing import Optional

from scripts.function_tracer_pcode.core.errors import (
    AnalysisLimitation,
    InternalError,
    PairStopState,
    current_pair_ledger,
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


def pending_pair_failure() -> Optional[BaseException]:
    """未解消の失敗を 1 件、例外 object として返す（無ければ `None`）。

    内部バグは限界より優先する。限界を UNKNOWN にする前に「壊れていた」ことを
    ERROR として出す必要があるため。`InternalError` の `site` は **記録された
    観測点**（バグが起きた場所）で、gate の場所ではない。
    """
    ledger = current_pair_ledger()
    if ledger is None:
        return None
    bugs = ledger.internal_bugs()
    if bugs:
        return InternalError(bugs[0].exception, site=bugs[0].site)
    return ledger.pending()


def raise_pending_pair_failure() -> None:
    """未解消の失敗があればここで raise する（G1 / G2 の本体）。"""
    failure = pending_pair_failure()
    if failure is not None:
        raise failure


def binary_display_name(program, fallback: str) -> str:
    return program.getName() if hasattr(program, "getName") else fallback


def pair_failure_result(
    checker,
    exc,
    *,
    function_name1: str,
    function_name2: str,
    binary1_name: str,
    binary2_name: str,
    start_time: float,
    result=None,
):
    """限界 / 内部バグを pair 1 件の結果にする（G3 / G5 の共通本体）。

    内部バグを限界より優先するのは `pair_execution` と同じ規則。`result` を
    渡した場合は、その結果の **診断だけ** を引き継いで判定面は作り直す。
    """
    common = dict(
        stop_state=pair_stop_state(),
        function_name1=function_name1,
        function_name2=function_name2,
        binary1_name=binary1_name,
        binary2_name=binary2_name,
        start_time=start_time,
        carry_from=result,
    )
    if isinstance(exc, InternalError):
        return internal_error_result_for_pair(exc, **common)
    return analysis_limitation_result_for_pair(
        exc,
        session=getattr(checker, "_active_v2_dual_write_pilot_session", None),
        **common,
    )


def apply_pair_failure_gate(
    checker,
    result,
    *,
    function_name1: str,
    function_name2: str,
    start_time: float,
):
    """未解消の限界 / 内部バグが結果に出ないまま返させない（G3 / G4-a）。

    置き換えるのは「その失敗がまだ結果に出ていない」ときだけ。同じ pair で
    G3（workflow）と G4-a（boundary）の 2 回通るので、2 度目が同じ結果を作り
    直さないように、出ているかどうかを結果そのもの（`failure_status` と
    reason 集合）から判断する。診断 block は読まない。

    * 内部バグ → 既に `internal_exception` の ERROR でなければ置き換える
      （限界より優先する。UNKNOWN の限界結果でも ERROR へ上書きする）。
    * 限界 → EQ / NOT_EQ なら必ず置き換える。UNKNOWN / ERROR のときは、
      既に ERROR か、その reason が既に出ているなら置き換えない
      （基盤の ERROR を意味的な UNKNOWN へ格下げしない）。
    * どの分岐でも stop state は結果へ写す（診断）。

    台帳が無い（pair scope の外で呼ばれた）ときは何もしない。
    """
    if result is None:
        return result
    failure = pending_pair_failure()
    if failure is None:
        return result
    if _failure_already_in_result(result, failure):
        attach_pair_stop_state(result, pair_stop_state())
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


def _failure_already_in_result(result, failure) -> bool:
    """この失敗が既に結果の **判定面** に出ているか（診断 block は見ない）。"""
    if isinstance(failure, InternalError):
        return getattr(result, "failure_status", None) == INTERNAL_EXCEPTION_STATUS
    if result.is_equivalent is not None:
        return False
    if getattr(result, "error_message", None):
        return True
    return any(
        getattr(reason, "reason_id", None) == failure.reason_id
        for reason in (getattr(result, "unknown_reasons", None) or ())
    )


__all__ = [
    "AnalysisLimitation",
    "InternalError",
    "PairStopState",
    "apply_pair_failure_gate",
    "binary_display_name",
    "pair_allows_semantic_analysis",
    "pair_failure_result",
    "pair_stop_state",
    "pending_pair_failure",
    "raise_pending_pair_failure",
]

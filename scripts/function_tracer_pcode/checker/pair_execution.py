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
    analysis_limitation_result,
    analysis_limitation_result_for_pair,
    attach_pair_stop_state,
    internal_error_result,
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


#: 結果へ焼き込む failure 識別子の置き場（private・非 authoritative）。
#: `EquivalenceResult` の宣言 field にしないのは、判定にも serialization にも
#: 関与させないため（`_conditional_lane_analyses` などと同じ扱い）。
PAIR_FAILURE_IDENTITY_ATTRIBUTE = "_pair_failure_identity"


@dataclass(frozen=True)
class _KindHandling:
    """1 つの `PairFailureKind` について consumer が知るべきことのすべて。

    `build_result` = 解析が無くても組める結果（G3 / G4-a / G5）。
    `build_result_with_analyses` = 両側 analysis がある場所（`check()`）用の
    richer な結果。**どちらも winner は台帳が決めたものを受け取る**（この
    module が例外から winner を推測することはない）。
    `replaces_unrelated_result` = 別の failure を表す結果を置き換えてよいか。

    種別が増えたときに触るのはこの表の 1 行だけで、gate 側（workflow /
    boundary / `check()`）にも分岐は増えない。
    """

    build_result: Callable[..., Any]
    build_result_with_analyses: Callable[..., Any]
    replaces_unrelated_result: Callable[[Any, PairPendingFailure], bool]


def _build_limitation_result(checker, failure, **common):
    return analysis_limitation_result_for_pair(
        failure.exception,
        session=getattr(checker, "_active_v2_dual_write_pilot_session", None),
        **common,
    )


def _build_internal_bug_result(checker, failure, **common):
    return internal_error_result_for_pair(failure.exception, **common)


def _build_limitation_result_with_analyses(checker, failure, **common):
    return analysis_limitation_result(
        failure.exception,
        session=getattr(checker, "_active_v2_dual_write_pilot_session", None),
        **common,
    )


def _build_internal_bug_result_with_analyses(checker, failure, **common):
    return internal_error_result(failure.exception, **common)


def _limitation_replaces_unrelated_result(result, failure) -> bool:
    """EQ / NOT_EQ は必ず置き換える。既存の ERROR は置き換えない。

    基盤側の ERROR（`function_lookup_miss` など）を意味的な UNKNOWN へ
    格下げしないため。UNKNOWN は置き換えて、限界を reason として出す。
    """
    return result.is_equivalent is not None or not getattr(
        result, "error_message", None
    )


def _internal_bug_replaces_unrelated_result(result, failure) -> bool:
    """内部バグは何であれ置き換える（限界の UNKNOWN も既存 ERROR も上書き）。"""
    return True


#: 種別 → 扱い方。`PairFailureKind` に member を足したらここへ 1 行足す。
#: 足し忘れは `KeyError` で即座に落ちる（黙って別種別として扱わない）。
_HANDLING_BY_KIND = {
    PairFailureKind.LIMITATION: _KindHandling(
        _build_limitation_result,
        _build_limitation_result_with_analyses,
        _limitation_replaces_unrelated_result,
    ),
    PairFailureKind.INTERNAL_BUG: _KindHandling(
        _build_internal_bug_result,
        _build_internal_bug_result_with_analyses,
        _internal_bug_replaces_unrelated_result,
    ),
}


def _stamp_pair_failure_identity(result, failure: PairPendingFailure):
    """この結果がどの failure を表しているかを焼き込む（照合専用）。

    結果を組む場所はこの module 1 つなので、焼き込みもここ 1 箇所で済む。
    """
    if result is not None:
        setattr(result, PAIR_FAILURE_IDENTITY_ATTRIBUTE, failure.identity)
    return result


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
    return _stamp_pair_failure_identity(
        _HANDLING_BY_KIND[failure.kind].build_result(
            checker,
            failure,
            stop_state=failure.stop_state,
            function_name1=function_name1,
            function_name2=function_name2,
            binary1_name=binary1_name,
            binary2_name=binary2_name,
            start_time=start_time,
            carry_from=result,
        ),
        failure,
    )


def pair_failure_result_from_check(
    checker,
    exc: BaseException,
    *,
    analysis1,
    analysis2,
    binary1_name: str,
    binary2_name: str,
    start_time: float,
    type_fix_result,
    retry_count: int,
    original_signature1,
    original_signature2,
):
    """`check()` が捕まえた typed failure を、解析付きの結果にする。

    **winner を決めるのは台帳**（`adopt_pair_failure`）で、捕まえた例外そのもの
    ではない。`check()` の中で raise された failure も、その前に記録されて握り
    潰された failure も、同じ winner 解決を通る。ここが `check()` 用に別経路を
    持つのは「両側 analysis があるので richer な結果を組める」という理由だけで、
    どの failure を結果化するかの判断は共有している。

    族の外の例外は `None` を返す（呼び出し側の generic 経路が扱う）。
    """
    failure = adopt_pair_failure(exc)
    if failure is None:
        return None
    return _stamp_pair_failure_identity(
        _HANDLING_BY_KIND[failure.kind].build_result_with_analyses(
            checker,
            failure,
            analysis1=analysis1,
            analysis2=analysis2,
            binary1_name=binary1_name,
            binary2_name=binary2_name,
            start_time=start_time,
            type_fix_result=type_fix_result,
            retry_count=retry_count,
            original_signature1=original_signature1,
            original_signature2=original_signature2,
        ),
        failure,
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

    判定は 2 段。(1) 結果が **winner そのもの** を表していれば作り直さない
    （failure 識別子の完全一致。同種の別 failure とは区別する）。(2) そうで
    なければ、種別ごとの置き換え規則（`_HANDLING_BY_KIND`）に従う。どの分岐でも
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
    """この結果が **今の winner そのもの** を表しているか（診断 block は見ない）。

    照合は failure 識別子の完全一致で行う。種別（`internal_exception` かどうか）
    だけで判定すると、同じ種別の **別の** failure を表す結果を「既に出ている」と
    誤認してしまう。識別子が違えば、その結果は winner を表していないので、
    種別ごとの置き換え規則（`replaces_unrelated_result`）へ進む。
    """
    if getattr(result, PAIR_FAILURE_IDENTITY_ATTRIBUTE, None) == failure.identity:
        return True
    return not _HANDLING_BY_KIND[failure.kind].replaces_unrelated_result(
        result, failure
    )


__all__ = [
    "apply_pair_failure_gate",
    "binary_display_name",
    "pair_allows_semantic_analysis",
    "pair_failure_result",
    "pair_failure_result_for_exception",
    "pair_failure_result_from_check",
    "pair_stop_state",
    "pending_pair_failure",
    "raise_pending_pair_failure",
]


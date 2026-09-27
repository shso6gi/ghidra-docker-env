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
「既存どちらの変換規則にも載らない failure handling policy」を足すとき — だけ、
下の 3 つの振り分け（`_build_result_for` など）が唯一の対応点になる。

`PairFailureKind` は **最終 outcome ではなく変換 policy の category** である点に
注意。`LIMITATION` の結果が reason 付き UNKNOWN になるか
`limitation_unattributed` の ERROR になるかは attribution しだいで、ここでは
決めない（`analysis_limitation_result*` の先、authority 側が決める）。
"""

from __future__ import annotations

from typing import Any

from scripts.function_tracer_pcode.core import live_values
# pair の実行制御の owner は、作業量を受け取らない値の storage の読みの量の意味の owner
# （`core/read_limits`: 上限の外を型つきの限界として台帳へ記録する）が登録済みであることを保証する
from scripts.function_tracer_pcode.core import read_limits  # noqa: F401
from scripts.function_tracer_pcode.core.json_encoding import value_token
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


def _build_limitation_result(checker, failure, **common):
    return analysis_limitation_result_for_pair(
        failure.exception,
        session=live_values.attribute(checker, "_active_v2_dual_write_pilot_session"),
        **common,
    )


def _build_internal_bug_result(checker, failure, **common):
    return internal_error_result_for_pair(failure.exception, **common)


def _build_limitation_result_with_analyses(checker, failure, **common):
    return analysis_limitation_result(
        failure.exception,
        session=live_values.attribute(checker, "_active_v2_dual_write_pilot_session"),
        **common,
    )


def _build_internal_bug_result_with_analyses(checker, failure, **common):
    return internal_error_result(failure.exception, **common)


def _limitation_replaces_unrelated_result(result, failure) -> bool:
    """EQ / NOT_EQ は必ず置き換える。既存の ERROR は置き換えない。

    基盤側の ERROR（`function_lookup_miss` など）を意味的な UNKNOWN へ
    格下げしないため。UNKNOWN は置き換えて、限界を reason として出す。
    """
    if live_values.attribute(result, "is_equivalent") is not None:
        return True
    message = live_values.attribute(result, "error_message")
    return message is None or not live_values.as_bool(message)


def _internal_bug_replaces_unrelated_result(result, failure) -> bool:
    """内部バグは何であれ置き換える（限界の UNKNOWN も既存 ERROR も上書き）。"""
    return True


#: 種別 → 扱い方。`PairFailureKind` に member を足したら、下の 3 つの振り分けへ 1 分岐ずつ足す。
#: 関数の表を値として持たず、扱い方ごとに振り分けを分けるのは bounded path の監査（J19）の精度のため:
#: 表の callable は解決できない呼び出しになり、1 つの振り分けへ全部の扱い方をまとめると、監査が
#: 呼び元ごとの引数・戻り値を合流させて live な値の流れを見失う（受け入れた trade-off）。足し忘れは
#: test（`test_every_failure_kind_is_handled_by_every_dispatcher`）と、実行時の `KeyError` で落ちる。


def _build_result_for(kind: PairFailureKind, checker: Any, failure: PairPendingFailure, **common: Any) -> Any:
    if kind is PairFailureKind.LIMITATION:
        return _build_limitation_result(checker, failure, **common)
    if kind is PairFailureKind.INTERNAL_BUG:
        return _build_internal_bug_result(checker, failure, **common)
    raise KeyError(kind)


def _build_result_with_analyses_for(
    kind: PairFailureKind, checker: Any, failure: PairPendingFailure, **common: Any,
) -> Any:
    if kind is PairFailureKind.LIMITATION:
        return _build_limitation_result_with_analyses(checker, failure, **common)
    if kind is PairFailureKind.INTERNAL_BUG:
        return _build_internal_bug_result_with_analyses(checker, failure, **common)
    raise KeyError(kind)


def _replaces_unrelated_result_for(kind: PairFailureKind, result: Any, failure: PairPendingFailure) -> bool:
    if kind is PairFailureKind.LIMITATION:
        return _limitation_replaces_unrelated_result(result, failure)
    if kind is PairFailureKind.INTERNAL_BUG:
        return _internal_bug_replaces_unrelated_result(result, failure)
    raise KeyError(kind)


def _stamp_pair_failure_identity(result, failure: PairPendingFailure):
    """この結果がどの failure を表しているかを焼き込む（照合専用）。

    結果を組む場所はこの module 1 つなので、焼き込みもここ 1 箇所で済む。
    """
    if result is not None:
        live_values.set_state(result, PAIR_FAILURE_IDENTITY_ATTRIBUTE, failure.identity)
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
        _build_result_for(
            failure.kind,
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
        _build_result_with_analyses_for(
            failure.kind,
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
    なければ、種別ごとの置き換え規則（`_replaces_unrelated_result_for`）に従う。どの分岐でも
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
        function_name1=_name_or(live_values.attribute(result, "function1_name"), function_name1),
        function_name2=_name_or(live_values.attribute(result, "function2_name"), function_name2),
        binary1_name=live_values.attribute(result, "binary1_name"),
        binary2_name=live_values.attribute(result, "binary2_name"),
        start_time=start_time,
        result=result,
    )


def _name_or(name, fallback):
    """結果の名前（空なら `fallback`。旧 `name or fallback`）。"""
    return name if name is not None and live_values.as_bool(name) else fallback


def _failure_already_in_result(result, failure: PairPendingFailure) -> bool:
    """この結果が **今の winner そのもの** を表しているか（診断 block は見ない）。

    照合は failure 識別子の完全一致で行う。種別（`internal_exception` かどうか）
    だけで判定すると、同じ種別の **別の** failure を表す結果を「既に出ている」と
    誤認してしまう。識別子が違えば、その結果は winner を表していないので、
    種別ごとの置き換え規則（`replaces_unrelated_result`）へ進む。
    """
    # 焼き込んだ識別子は値の印で比べる（結果の object の `__eq__` を呼ばない）。値の印にできない live な
    # target は identity の印なので、値が等しい別 object は「別」と見て winner の結果を作り直す側へ倒れる
    # （同じ winner の結果を組み直すだけで、別の failure を表す結果を残すことはない）
    stamped = live_values.attribute(result, PAIR_FAILURE_IDENTITY_ATTRIBUTE)
    if stamped is not None and value_token(stamped) == value_token(failure.identity):
        return True
    return not _replaces_unrelated_result_for(failure.kind, result, failure)


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


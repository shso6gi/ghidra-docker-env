"""Recurrence promotion stage of :meth:`EquivalenceChecker.check` (Phase 6b-4, #82).

C 段（UNKNOWN reason refinement）の後に走る D 段。checker facade を直接書き換えず、明示的な入力を受け取る
module-level の段関数として、旧 ``check()`` の (1)〜(8) のうち facade を書かない部分だけを持つ:

(1) promotion authority 判定（``recurrence_promotion_authority`` callable、check() が gate 条件を判定）と
(2) ``promote_recurrence_pair`` → :func:`prepare_recurrence_promotion`（authority / promoted pair / runtime / attempt を返す）
(3) ``_last_recurrence_promotion_attempt = attempt`` → **check() が書く**（(2) の直後、(4) より前）
(4) ABORTED の debug print / COMPOSED の completion signal emission → :func:`complete_recurrence_promotion_signals`
    （再帰へ進むべきかを返す。signal 1 件ごとの失敗は shadow error として記録し、旧実装どおり握りつぶす）
(5) ``_obligation_runtime_session = recurrence_runtime`` (6) ``_active_recurrence_promotion_authority = authority``
(7) 再帰 ``self.check(...)`` (8) finally で active authority 削除 → **すべて check() に残す**

(2)〜(4) を helper 内で一括処理して (3) の位置を後ろへずらしてはならない（#82）。
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Callable, Optional

from scripts.function_tracer_pcode.proof.recurrence_promotion import (
    PairPromotionState,
    promote_recurrence_pair,
)


@dataclass(frozen=True)
class RecurrencePromotionPreparation:
    """(1)(2) の結果。``attempt`` を check() が ``_last_recurrence_promotion_attempt`` に書く。"""

    authority: Any
    promoted1: Any
    promoted2: Any
    recurrence_runtime: Any
    attempt: Any


def prepare_recurrence_promotion(
    strategy_result,
    analysis1,
    analysis2,
    *,
    comparison_session_id: str,
    branch_id: str,
    recurrence_promotion_authority: Callable[..., Any],
) -> Optional[RecurrencePromotionPreparation]:
    """authority が得られなければ ``None``（旧実装の ``if authority is not None`` の外側）。"""
    authority = recurrence_promotion_authority(
        strategy_result,
        comparison_session_id=comparison_session_id,
        branch_id=branch_id,
    )
    if authority is None:
        return None
    promoted1, promoted2, recurrence_runtime, recurrence_attempt = promote_recurrence_pair(
        analysis1, analysis2, authority
    )
    return RecurrencePromotionPreparation(
        authority=authority,
        promoted1=promoted1,
        promoted2=promoted2,
        recurrence_runtime=recurrence_runtime,
        attempt=recurrence_attempt,
    )


def recurrence_promotion_composed(attempt) -> bool:
    """旧 ``elif`` 条件: COMPOSED かつ左右いずれかに proposal がある。"""
    return attempt.state == PairPromotionState.COMPOSED and (
        attempt.left is not None
        and attempt.left.proposal is not None
        or attempt.right is not None
        and attempt.right.proposal is not None
    )


def complete_recurrence_promotion_signals(attempt, *, debug_print: Callable[[str], None]) -> bool:
    """(4)。ABORTED なら debug print のみ。COMPOSED（proposal あり）なら側ごとに completion signal を emit し
    ``True`` を返す（check() は (5)〜(8) へ進む）。それ以外は何もせず ``False``。"""
    if attempt.state == PairPromotionState.ABORTED:
        debug_print(
            "Recurrence promotion declined: "
            + str(attempt.failure or "unknown")
        )
        return False
    if not recurrence_promotion_composed(attempt):
        return False
    for promoted_side in (attempt.left, attempt.right):
        if promoted_side is None or promoted_side.proposal is None:
            continue
        try:
            from scripts.function_tracer_pcode.authority.domains.loop_recurrence import (
                RecurrenceValidationCompletionSignal,
            )
            from scripts.function_tracer_pcode.authority.lifecycle.production_signals import (
                emit_loop_recurrence_signal,
            )

            emit_loop_recurrence_signal(
                RecurrenceValidationCompletionSignal.from_side_promotion(promoted_side),
                producer_site_manifest_id="checker-recurrence-validation-completed",
            )
        except Exception as exc:
            from scripts.function_tracer_pcode.authority.lifecycle.production_signals import (
                record_production_pilot_shadow_error,
            )

            record_production_pilot_shadow_error(exc)
    return True

"""UNKNOWN reason refinement stage of :meth:`EquivalenceChecker.check` (Phase 6b-3, #82).

strategy 実行の直後、recurrence promotion より前に走る C 段。checker facade を直接書き換えず、
明示的な入力を受け取る module-level の段関数として、旧 ``check()`` と同じ逐次順序を固定する:

1. call-effect comparison identity の計算（shadow manifest から）
2. recurrence proposal blocker の付与（``strategy_result`` を読む）
3. call-effect specialization（2 の出力を ``list(...)`` でコピーして渡す。comparison identity を使う）
4. root blocker identity の付与（3 の出力と同じ comparison identity を使う）

各段の出力は旧実装どおり ``strategy_result.unknown_reasons`` へ順に書き戻す（``strategy_result`` は
明示的な入力であり、checker facade ではない）。4 つの処理本体は checker の mixin メソッドで、
callable として受け取る（テストの class-level / instance-level patch seam を維持）。
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Callable, List, Sequence


@dataclass(frozen=True)
class UnknownRefinementOutcome:
    """C 段の各出力。``final_reasons`` は ``strategy_result.unknown_reasons`` に書き戻された最終値と同一 object。"""

    comparison_identity: Any
    reasons_after_recurrence_blockers: Sequence[Any]
    reasons_after_call_effect_specialization: Sequence[Any]
    final_reasons: Sequence[Any]


def refine_unknown_reasons(
    strategy_result,
    analysis1,
    analysis2,
    call_effect_shadow_manifest,
    *,
    branch_id: str,
    call_effect_comparison_identity: Callable[..., Any],
    attach_recurrence_proposal_blockers: Callable[..., List[Any]],
    specialize_call_effect_unknown_reasons: Callable[..., List[Any]],
    attach_root_blocker_identities: Callable[..., List[Any]],
) -> UnknownRefinementOutcome:
    comparison_identity = call_effect_comparison_identity(
        analysis1,
        analysis2,
        call_effect_shadow_manifest,
    )
    strategy_result.unknown_reasons = attach_recurrence_proposal_blockers(
        strategy_result,
        analysis1,
        analysis2,
        branch_id=branch_id,
    )
    after_recurrence = strategy_result.unknown_reasons
    strategy_result.unknown_reasons = specialize_call_effect_unknown_reasons(
        list(getattr(strategy_result, "unknown_reasons", ()) or ()),
        call_effect_shadow_manifest,
        comparison_identity=comparison_identity,
    )
    after_specialization = strategy_result.unknown_reasons
    strategy_result.unknown_reasons = attach_root_blocker_identities(
        strategy_result.unknown_reasons,
        comparison_identity,
    )
    return UnknownRefinementOutcome(
        comparison_identity=comparison_identity,
        reasons_after_recurrence_blockers=after_recurrence,
        reasons_after_call_effect_specialization=after_specialization,
        final_reasons=strategy_result.unknown_reasons,
    )

"""Strategy execution stage of :meth:`EquivalenceChecker.check` (Phase 6b-2, #82).

``check()`` は orchestration のみを持ち、本 module は B 段（strategy 実行）を、**checker facade を直接書き換えず、
明示的な入力を受け取る module-level の段関数**に分ける（純粋関数ではない: manifest callback の副作用、frame 構築失敗時の
lease revoke、strategy / dispatch frame / ledger / manifest の更新と lease revoke を含む。書かないのは checker facade の属性だけ）:

1. :func:`prepare_preflight_projection` — solver surface / call-effect shadow manifest / projection を組み立てる。
   :func:`build_prepared_dispatch_frame` — dispatch frame を構築する（失敗時は check() が発行した lease を revoke）。
   **branch authority lease の発行は ``check()`` に残す**: ``issue_production_branch_authority`` は呼び出し元を
   ``EquivalenceChecker.check`` の code object に pin する authority TCB なので、発行位置（projection の後、frame 構築の前）を
   変えずに check() 側で行う。
2. :func:`prepare_strategy_runtime` — どの :class:`ObligationRuntimeSession` を使うか、facade に保存するかを決める。
   **facade への保存そのものは ``check()`` が行う**（strategy 実行より前）。
3. :func:`run_strategy_branch` — runtime を strategy / frame に束縛し、dispatch frame の push → ``strategy.check`` →
   receipt finalize → frame close / lease revoke（finally）→ preflight final gate → diagnostic projection を現行順で実行する。

legacy モード（preflight projection でない場合）は :func:`run_legacy_strategy`。
どの関数も checker の facade 属性を書かない。checker の mixin メソッド（shadow manifest / final gate /
phase2 discharge / debug print）は callable として受け取る（テストの instance patch seam を維持）。
"""

from __future__ import annotations

from dataclasses import dataclass, replace
from typing import Any, Callable, Dict

from scripts.function_tracer_pcode.checker.arch.input_extension import (
    provide_input_extension_evidence,
)
from scripts.function_tracer_pcode.proof.obligations.branch_context import BranchCheckContext
from scripts.function_tracer_pcode.proof.call_effect.preflight import (
    PreparedDispatchFrame,
    StrategySourceAnalysisPair,
    close_prepared_dispatch_frame,
    diagnostic_projection,
    finalize_pairwise_comparison_receipt,
    prepare_solver_surface,
    push_prepared_dispatch_frame,
    validate_call_resolution_projection,
)
from scripts.function_tracer_pcode.proof.strategies.monolithic import MonolithicStrategy
from scripts.function_tracer_pcode.proof.strategies.pairwise import PairwiseStrategy


@dataclass
class PreflightProjectionPreparation:
    """solver surface と call-effect shadow manifest、projection の組（frame 構築と strategy 実行の入力）。"""

    source_pair: Any
    prepared_pair: Any
    call_effect_shadow_manifest: Dict[str, Any]
    projection: Any


def prepare_preflight_projection(
    ctx: BranchCheckContext,
    analysis1,
    analysis2,
    binary1_name: str,
    binary2_name: str,
    *,
    observation_contract_id: Any,
    trusted_proof_artifacts: Callable[[], Any],
    enable_completed_recovery_proofs: bool,
    call_effect_shadow_manifest: Callable[..., Dict[str, Any]],
) -> PreflightProjectionPreparation:
    # raw pair と、validator を通った入力 extension 証拠（現在の provider は
    # 信頼済み signature が無いので発行しない。Issue #167）。
    source_pair = StrategySourceAnalysisPair.create(
        analysis1,
        analysis2,
        input_extension_evidence=provide_input_extension_evidence(analysis1, analysis2),
    )
    prepared_pair = prepare_solver_surface(
        source_pair,
        observation_contract_digest=observation_contract_id,
        comparison_session_id=ctx.comparison_session_id,
        branch_id=ctx.branch_id,
        generation=ctx.generation,
        decision_mode=ctx.decision_mode,
    )
    manifest = call_effect_shadow_manifest(
        prepared_pair.analysis1,
        prepared_pair.analysis2,
        binary1_name,
        binary2_name,
    )
    projection = validate_call_resolution_projection(
        manifest,
        prepared_pair,
        generation=ctx.generation,
        # facade の _last_internal_call_effect_artifacts は manifest 計算の副作用で更新されるため、
        # 旧実装と同じく manifest 呼び出しの後に supplier で読む（先読みすると stale になる）。
        trusted_proof_artifacts=trusted_proof_artifacts(),
    )
    if not enable_completed_recovery_proofs and projection.required:
        projection = replace(
            projection,
            status="inconclusive",
            root_blockers=("completed_recovery_proofs_disabled",),
            covered_blockers=(),
        )
    return PreflightProjectionPreparation(
        source_pair=source_pair,
        prepared_pair=prepared_pair,
        call_effect_shadow_manifest=manifest,
        projection=projection,
    )


def build_prepared_dispatch_frame(
    ctx: BranchCheckContext,
    preparation: PreflightProjectionPreparation,
    *,
    trusted_proof_artifacts: Callable[[], Any],
    branch_authority: Any,
    locally_issued_branch_authority: Any,
) -> PreparedDispatchFrame:
    """dispatch frame を構築する。構築に失敗した場合、check() が直前に発行した lease があれば revoke して re-raise する
    （artifacts の tuple 化を含め、旧実装の try 範囲と同じ）。"""
    try:
        return PreparedDispatchFrame(
            comparison_session_id=ctx.comparison_session_id,
            branch_id=ctx.branch_id,
            generation=ctx.generation,
            source=preparation.source_pair,
            prepared=preparation.prepared_pair,
            projection=preparation.projection,
            preflight_manifest=preparation.call_effect_shadow_manifest,
            trusted_proof_artifacts=tuple(trusted_proof_artifacts()),
            decision_mode=ctx.decision_mode,
            production_branch_authority_lease=branch_authority,
        )
    except Exception:
        if locally_issued_branch_authority is not None:
            from scripts.function_tracer_pcode.proof.monolithic_authority import (
                revoke_production_branch_authority,
            )
            revoke_production_branch_authority(locally_issued_branch_authority)
        raise


@dataclass(frozen=True)
class StrategyRuntimePreparation:
    """使う runtime と、それを facade（``_obligation_runtime_session``）へ保存すべきかどうか。"""

    runtime: Any
    store_on_facade: bool


def prepare_strategy_runtime(existing_runtime, replan_plan, analysis1, analysis2) -> StrategyRuntimePreparation:
    """旧 ``check()`` と同じ規則。

    - 既存 runtime があり、replan 中でなく、branch-local な ``pending_successor`` を持つ場合:
      successor intent を他の strategy に消費させないため **新しい runtime をローカルに作るが facade には保存しない**。
    - 既存 runtime が無い場合: 新しい runtime を作り **facade に保存する**。
    - それ以外: 既存 runtime をそのまま使い、保存しない。
    """
    obligation_runtime = existing_runtime
    if (
        obligation_runtime is not None
        and replan_plan is None
        and obligation_runtime.pair_ledger_manager.pending_successor is not None
    ):
        # A successor intent is branch-local authority.  Recursive
        # abstraction or another strategy must not consume it.
        from scripts.function_tracer_pcode.proof.obligations.runtime import (
            ObligationRuntimeSession,
        )

        return StrategyRuntimePreparation(ObligationRuntimeSession.create(analysis1, analysis2), False)
    if obligation_runtime is None:
        from scripts.function_tracer_pcode.proof.obligations.runtime import (
            ObligationRuntimeSession,
        )

        return StrategyRuntimePreparation(ObligationRuntimeSession.create(analysis1, analysis2), True)
    return StrategyRuntimePreparation(obligation_runtime, False)


@dataclass
class StrategyBranchOutcome:
    strategy_result: Any
    call_effect_shadow_manifest: Dict[str, Any]
    preflight_gate_delta_diagnostic: Dict[str, Any]
    cleanup_complete: bool


def run_strategy_branch(
    ctx: BranchCheckContext,
    dispatch_frame: PreparedDispatchFrame,
    obligation_runtime,
    analysis1,
    analysis2,
    save_formula: bool,
    *,
    locally_issued_branch_authority: Any,
    call_effect_shadow_manifest: Dict[str, Any],
    debug_print: Callable[[str], None],
    apply_preflight_final_gate: Callable[..., None],
) -> StrategyBranchOutcome:
    strategy = ctx.strategy
    replan_plan = ctx.replan_plan
    cleanup_complete = True

    try:
        strategy._obligation_runtime_session = obligation_runtime
    except (AttributeError, TypeError):
        pass
    dispatch_frame.obligation_runtime = obligation_runtime
    if replan_plan is not None:
        current_plan = obligation_runtime.pair_ledger_manager.pending_successor
        if current_plan is not replan_plan:
            raise RuntimeError("pair_replan_successor_plan_missing")
        dispatch_frame.replan_successor_plan = replan_plan

    debug_print(f"Using strategy: {strategy.__class__.__name__}")
    if isinstance(strategy, (PairwiseStrategy, MonolithicStrategy)):
        token = None
        try:
            token = push_prepared_dispatch_frame(dispatch_frame)
            strategy_result = strategy.check(analysis1, analysis2, save_formula)
            if (
                isinstance(strategy, PairwiseStrategy)
                and dispatch_frame.pair_disposition_ledger is not None
                and dispatch_frame.receipt is None
            ):
                strategy_result.comparison_execution_receipt = (
                    finalize_pairwise_comparison_receipt(dispatch_frame)
                )
        finally:
            if token is None:
                dispatch_frame.close()
                dispatch_frame.cleanup_complete = True
                cleanup_complete = True
            else:
                cleanup_complete = close_prepared_dispatch_frame(dispatch_frame, token)
            if locally_issued_branch_authority is not None:
                from scripts.function_tracer_pcode.proof.monolithic_authority import (
                    revoke_production_branch_authority,
                )
                revoke_production_branch_authority(locally_issued_branch_authority)
    else:
        # Non-built-in compatibility branches cannot consume a
        # projection.  Their EQ is vetoed below whenever call proof
        # preflight is required.
        try:
            strategy_result = strategy.check(analysis1, analysis2, save_formula)
        finally:
            dispatch_frame.close()
            dispatch_frame.cleanup_complete = True
    ordinary_outcome = strategy_result.is_equivalent
    stage_runner_owns_finalization = str(ctx.branch_id).startswith("S_")
    if (
        isinstance(strategy, PairwiseStrategy)
        and dispatch_frame.pair_disposition_ledger is not None
        and not stage_runner_owns_finalization
    ):
        strategy_result.comparison_execution_receipt = (
            finalize_pairwise_comparison_receipt(dispatch_frame)
        )
    elif isinstance(strategy, MonolithicStrategy) and not stage_runner_owns_finalization:
        from scripts.function_tracer_pcode.proof.call_effect.preflight import (
            finalize_monolithic_comparison_receipt,
        )
        strategy_result.comparison_execution_receipt = (
            finalize_monolithic_comparison_receipt(dispatch_frame)
        )
    if not stage_runner_owns_finalization:
        apply_preflight_final_gate(
            strategy_result,
            dispatch_frame,
            cleanup_complete=cleanup_complete,
        )
    call_effect_shadow_manifest = diagnostic_projection(
        call_effect_shadow_manifest,
        dispatch_frame,
    )
    preflight_gate_delta_diagnostic = {
        "status": "diagnostic_not_legacy_canary",
        "ordinary_comparison_outcome": (
            "EQ" if ordinary_outcome is True
            else "NOT_EQ" if ordinary_outcome is False
            else "UNKNOWN"
        ),
        "preflight_terminal_outcome": (
            "EQ" if strategy_result.is_equivalent is True
            else "NOT_EQ" if strategy_result.is_equivalent is False
            else "UNKNOWN"
        ),
        "gate_effect": (
            "agree"
            if ordinary_outcome is strategy_result.is_equivalent
            else "preflight_veto"
        ),
        "decision_mode": "preflight_projection",
        "comparison_branch": ctx.branch_id,
    }
    call_effect_shadow_manifest["preflight_gate_delta_diagnostic"] = preflight_gate_delta_diagnostic
    return StrategyBranchOutcome(
        strategy_result=strategy_result,
        call_effect_shadow_manifest=call_effect_shadow_manifest,
        preflight_gate_delta_diagnostic=preflight_gate_delta_diagnostic,
        cleanup_complete=cleanup_complete,
    )


@dataclass
class LegacyStrategyOutcome:
    strategy_result: Any
    call_effect_shadow_manifest: Dict[str, Any]


def run_legacy_strategy(
    strategy,
    analysis1,
    analysis2,
    binary1_name: str,
    binary2_name: str,
    save_formula: bool,
    *,
    debug_print: Callable[[str], None],
    call_effect_shadow_manifest: Callable[..., Dict[str, Any]],
    apply_phase2_relational_call_discharge: Callable[..., None],
) -> LegacyStrategyOutcome:
    debug_print(f"Using strategy: {strategy.__class__.__name__}")
    strategy_result = strategy.check(analysis1, analysis2, save_formula)
    manifest = call_effect_shadow_manifest(analysis1, analysis2, binary1_name, binary2_name)
    apply_phase2_relational_call_discharge(strategy_result, analysis1, analysis2, manifest)
    return LegacyStrategyOutcome(strategy_result=strategy_result, call_effect_shadow_manifest=manifest)

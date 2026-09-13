# -*- coding: utf-8 -*-
"""独立 finalization の共有ヘルパー（計画 v4 §9.2）。

「診断 field を足しても semantic projection は変わらない」ことを主張する PR は、
同じ入力から **2 本の finalization を独立に起こして** preimage と projection を
比べる。片方の bundle を加工して他方を作ったり、消費済みの session /
finalization 状態を再利用したりすると、一致が vacuous になる。

元は `test_issue54a_result_surface.py` のローカルヘルパー。Issue #124 以降の
PR も同じ手順を使うのでここへ出した（挙動は変えていない）。
"""


def _independent_finalization(tmp_path, monkeypatch, *, case_id, result_payload_preimage):
    """1 本の production-pilot session を新規に起こし、渡した preimage で finalize する。

    session / evidence / bundle はこの呼び出し専用で、呼び出し間で共有しない。
    """
    from scripts.function_tracer_pcode.authority.contracts import authority_digest
    from scripts.function_tracer_pcode.authority.decision.canonical_result import (
        build_canonical_result_finalization_bundle,
    )
    from scripts.function_tracer_pcode.authority.domains.sat_safety import SatSafetyPilotEncoder
    from scripts.function_tracer_pcode.authority.lifecycle.execution_authority import (
        PINNED_SOLVER_EXECUTION_ISSUER,
    )
    from scripts.function_tracer_pcode.authority.lifecycle.pilot import (
        ProductionDualWritePilotConnector,
    )
    from scripts.function_tracer_pcode.authority.lifecycle.production_signals import (
        CompositeProductionSignalEncoder,
        SatSafetyBlockerProductionSignal,
        issue_pending_eq_closure_authority,
        production_signal_scope,
    )
    from scripts.function_tracer_pcode.authority.lifecycle.reducer import ShadowLifecycleReducer
    from scripts.function_tracer_pcode.authority.process.supervisor import (
        PROCESS_DURABLE_REASON_REGISTRY,
        PROCESS_DURABLE_RECOVERY_REGISTRY,
    )
    from scripts.function_tracer_pcode.checker.checker import EquivalenceChecker
    from scripts.function_tracer_pcode.tests.unit.test_monolithic_region_split import _analysis
    from types import SimpleNamespace

    connector = ProductionDualWritePilotConnector(
        ShadowLifecycleReducer(
            reason_registry=PROCESS_DURABLE_REASON_REGISTRY,
            recovery_registry=PROCESS_DURABLE_RECOVERY_REGISTRY,
        ),
        domain_signal_encoder=CompositeProductionSignalEncoder({
            SatSafetyBlockerProductionSignal: SatSafetyPilotEncoder(),
        }),
    )
    # 両 finalization で同じ semantic evidence を作るため、session の begin payload と
    # occurrence nonce は同一にする（nonce は semantic projection から除かれる）。
    session = connector.begin({"case": "issue54a-surface"})
    with production_signal_scope(session):
        trusted_result = EquivalenceChecker(
            strategy="monolithic", timeout=5, monolithic_timeout=5,
            canonical_decision_cutover=False,
        ).check(_analysis("left", 7), _analysis("right", 7))
    # EQ closure authority を発行して event stream に記録を入れる（空 prefix は封印できない）。
    frame = trusted_result._prepared_dispatch_frame
    issue_pending_eq_closure_authority(session, frame.receipt, frame)
    occurrence_payload = dict(session.execution_payload)
    occurrence_nonce = occurrence_payload.pop("result_entry_occurrence_nonce")
    session.result_entry_occurrence_receipt = (
        PINNED_SOLVER_EXECUTION_ISSUER.issue_result_entry_occurrence(
            result_occurrence_id=session.identity.result_occurrence_id,
            execution_payload_digest=authority_digest(occurrence_payload),
            startup_receipt_digests=(),
            occurrence_nonce=occurrence_nonce,
        )
    )
    evidence = connector.finish(
        session,
        SimpleNamespace(
            is_equivalent=True,
            error_message=None,
            failure_status=None,
            failure_message=None,
            unknown_reasons=[],
            unknown_recovery_actions=[],
            is_timeout=lambda: False,
        ),
        case_id=case_id,
    )
    bundle = build_canonical_result_finalization_bundle(
        result_payload_preimage=result_payload_preimage,
        evidence=evidence,
        session=session,
    )
    return bundle, session, evidence

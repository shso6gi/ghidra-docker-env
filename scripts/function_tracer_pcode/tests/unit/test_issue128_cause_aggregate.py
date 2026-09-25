# -*- coding: utf-8 -*-
"""Issue #128 PR-128-A: lossless compact aggregate と canonical 化。

この file が固定する契約は 2 本あり、混同してはいけない。

* **A（canonical 化）**: 最終 UNKNOWN reason の正本を `decision_receipt` を持つ
  canonical payload の `unknown_reasons` に統一したことによる、意図的な語彙・
  件数の変化。`test_canonical_source_change_is_measured_separately` /
  `test_final_unknown_reasons_prefer_canonical_payload` が測る。
* **B（情報保全）**: `debug_trace` を省いても原因分析（root blocker / backlog /
  completion / causal transition）を失わないこと。
  `test_aggregate_is_lossless_for_required_reporting` が oracle。

A の差を「aggregate の情報欠落」と読まない／B の欠落を「canonical 化による変更」
と読まないために、fixture と比較面をこの file の中で完全に固定する。
"""

import copy
import json

import pytest

from scripts.function_tracer_pcode.authority.contracts import authority_digest
from scripts.function_tracer_pcode.checker.cause_aggregate import (
    UNKNOWN_CAUSE_AGGREGATE_SCHEMA,
    attach_cause_aggregate,
    build_unknown_cause_aggregate,
    resolve_pool_refs,
)
from scripts.function_tracer_pcode.checker.debug_trace import (
    Attempt,
    AttemptIdentity,
    DebugTrace,
    ProofCompletionEvent,
    ReasonCausalTransition,
    ReasonCompletionEvent,
    ReasonOccurrenceId,
)
from scripts.function_tracer_pcode.checker.result import EquivalenceResult
from scripts.function_tracer_pcode.checker.unknown_reason import make_unknown_reason
from scripts.function_tracer_pcode.proof.cause_identity import (
    ProofRequirementContract,
    ProofRequirementId,
    RelationalCauseKey,
    UnaryCauseKey,
)
from scripts.function_tracer_pcode.reporting.root_blocker_summary import (
    summarize_root_blockers,
)
from scripts.function_tracer_pcode.reporting.unknown_reason_summary import (
    _extract_final_unknown_reasons,
    format_validation_unknown_summary,
    summarize_validation_unknowns,
)
from scripts.function_tracer_pcode.authority.seal_work import SealWorkBudget


# ---------------------------------------------------------------------------
# fixture 部品
# ---------------------------------------------------------------------------

BIN1 = ("sha256", "left-binary")
BIN2 = ("sha256", "right-binary")


class _CanonicalAuthorityStandIn:
    """`decision_receipt` が「確定済み」であることだけを表す印。

    本物の `DecisionReceipt` は factory token 無しには作れない（意図的）。
    producer が読むのは「None かどうか」だけで、reporting が読むのは
    serialized 形（`_serialized_receipt`）なので、両方をこの形で与える。
    """


def _serialized_receipt(outcome, occurrence_id):
    body = {
        "result_occurrence_id": occurrence_id,
        "outcome": outcome,
        "lifecycle_projection_digest": f"lpd-{occurrence_id}",
        "authority_input_digest": f"aid-{occurrence_id}",
    }
    return {**body, "receipt_digest": authority_digest(body)}


def _unary_cause(object_name):
    return UnaryCauseKey(
        cause_kind="call_argument_evidence",
        binary_content_identity=BIN1,
        function_ir_identity=("pcode", "f", 0x1000),
        semantic_object_identity=("callsite", object_name),
    ).to_dict()


def _relational_cause(object_name):
    return RelationalCauseKey(
        cause_kind="return_width_relation",
        comparison_domain=("left-sha", "right-sha", "abi-v1"),
        left_semantic_object=("return", object_name, "left"),
        right_semantic_object=("return", object_name, "right"),
        correspondence_contract=("return", "width-bridge"),
    ).to_dict()


def _v2_projection_cause(name):
    """canonical `unknown_reasons` が持つ v2 authority projection 形。

    実 run の canonical record はこの形で、`cause_key_from_dict` は受け付けない
    （`unknown_typed_cause_schema`）。だから root blocker は `debug_trace` の
    legacy record からしか作れない = aggregate が無いと失われる。
    """
    return {
        "authority_class": "V2_FACTORY_PROJECTION",
        "cause_id": f"cause-{name}",
        "occurrence_id": f"occurrence-{name}",
        "event_digest": f"digest-{name}",
        "expected_cause_slot_id": f"slot:{name}",
    }


def _requirement(proof_kind, target):
    return ProofRequirementId.create(
        proof_kind,
        ("target", target),
        ProofRequirementContract(
            f"{proof_kind} holds for {target}",
            observation_surface=("return",),
        ),
    )


def _reason(
    reason_id,
    *,
    cause,
    target,
    action_status=None,
    requirement_kinds=(),
    pair_or_case=None,
    detail=None,
    evidence_refs=(),
):
    return make_unknown_reason(
        reason_id,
        object_target_key=("call_argument_evidence", "function1", ("function_ref", target)),
        proof_obligation_id=(reason_id, "stage", "kind", "evidence", (target,)),
        typed_cause_key=cause,
        proof_requirement_ids=tuple(
            _requirement(kind, target).to_dict() for kind in requirement_kinds
        ),
        action_status=action_status,
        pair_or_case=pair_or_case,
        detail=detail or f"{reason_id} at {target}",
        evidence_refs=tuple(evidence_refs) or (f"evidence:{target}",),
    )


def _attempt(attempt_id, strategy, reasons, *, result=None, transition="UNKNOWN"):
    return Attempt(
        attempt_id=attempt_id,
        retry_count=0,
        phase="P0_BASE",
        stage_path=["stage"],
        strategy=strategy,
        result=result,
        transition_reason=transition,
        unknown_reasons=list(reasons),
    )


def _occurrence_id(strategy, attempt_id, ordinal):
    return ReasonOccurrenceId(AttemptIdentity(strategy, attempt_id), ordinal)


def _reason_completion(reason, *, occurrence_id, at_attempt, proof_kind, status="APPLICABLE"):
    return ReasonCompletionEvent(
        completion_event_id=("reason-completion", occurrence_id.reason_ordinal),
        completed_occurrence_id=occurrence_id,
        exact_target_id=reason.object_target_key,
        exact_missing_fact_or_proof_slot=proof_kind,
        source_snapshot_fingerprint="snapshot-1",
        semantic_seed_or_premise_digest="premise-1",
        evidence_or_artifact_digest="artifact-1",
        recognizing_stage="stage",
        completed_at_attempt=at_attempt,
        applicability_status=status,
    )


def _payload(
    *,
    case,
    outcome,
    trace,
    unknown_reasons=(),
    is_equivalent=None,
    error_message=None,
    canonical=True,
    emit_debug_trace=True,
):
    """1 結果分の payload。canonical なら serialized receipt を持たせる。

    `emit_debug_trace=False` は PR-128-B の通常 run（trace は object 上に在るが
    JSON へ添付しない）。既定 True は従来どおり。
    """
    result = EquivalenceResult(
        is_equivalent=is_equivalent,
        function1_name=case,
        function2_name=case,
        binary1_name="left",
        binary2_name="right",
        solver_results=None,
        error_message=error_message,
        debug_trace=trace,
        unknown_reasons=list(unknown_reasons),
        binary1_content_identity=BIN1,
        binary2_content_identity=BIN2,
        function1_identity=("function", "left", case),
        function2_identity=("function", "right", case),
        emit_debug_trace=emit_debug_trace,
    )
    if canonical:
        # producer は「確定したか」だけを見る。serialization は下で行う。
        result.decision_receipt = _CanonicalAuthorityStandIn()
    attach_cause_aggregate(result)
    result.decision_receipt = None
    payload = result.to_dict()
    payload["case_id"] = case
    payload["run_identity"] = "run-1"
    payload["artifact_identity"] = ("run-1", case)
    if canonical:
        payload["decision_receipt"] = _serialized_receipt(outcome, f"occ-{case}")
        payload["final_outcome"] = outcome
    return payload


def _fixture_payloads(emit_debug_trace=True):
    """UNKNOWN / TIMEOUT / ERROR / EQ / NOT_EQ と completion あり/なしを含む集合。

    `emit_debug_trace=False` で同じ入力の「trace を添付しない通常 run」形が得られる
    （PR-128-B）。呼び出し側の既定は従来どおり添付あり。
    """
    payloads = []

    # --- 1. UNKNOWN: 同一 reason の 2 cause、片方だけ completed、transition あり ---
    cause_x = _unary_cause("callsite-x")
    cause_y = _unary_cause("callsite-y")
    cause_z = _relational_cause("ret-z")
    r_x0 = _reason(
        "summary_effect_unmodeled", cause=cause_x, target="x",
        action_status="pending_proof", requirement_kinds=("effect_summary_completion",),
        pair_or_case=("case-l", "case-r"),
    )
    r_y0 = _reason(
        "summary_effect_unmodeled", cause=cause_y, target="y",
        action_status="pending_proof", requirement_kinds=("effect_summary_completion",),
    )
    r_x1 = _reason(
        "summary_effect_unmodeled", cause=cause_x, target="x",
        action_status="pending_proof", requirement_kinds=("effect_summary_completion",),
        pair_or_case=("case-l", "case-r"),
    )
    r_z1 = _reason(
        "return_width_bridge_missing", cause=cause_z, target="z",
        action_status="planned",
    )
    attempt0 = _attempt(0, "pairwise", [r_x0, r_y0])
    attempt1 = _attempt(1, "monolithic", [r_x1, r_z1])
    trace = DebugTrace(attempts=[attempt0, attempt1])
    trace.reason_completion_events.append(
        _reason_completion(
            r_y0,
            occurrence_id=_occurrence_id("pairwise", 0, 1),
            at_attempt=AttemptIdentity("monolithic", 1),
            proof_kind="effect_summary_completion",
        )
    )
    trace.causal_transitions.append(
        ReasonCausalTransition(
            transition_id=("supersede", 0),
            target_occurrence_id=_occurrence_id("pairwise", 0, 0),
            transition_kind="superseded",
            cause_kind="reason_occurrence",
            cause_ref=_occurrence_id("monolithic", 1, 0).to_dict(),
            emitted_at_attempt=AttemptIdentity("monolithic", 1),
            transition_ordinal=0,
        )
    )
    trace.proof_completion_events.append(
        ProofCompletionEvent(
            completion_id=("proof-completion", 0),
            proof_requirement_id=_requirement("effect_summary_completion", "x").to_dict(),
            proof_artifact_ref=("artifact", 0),
            proof_status="PROVED",
            completed_at_attempt=AttemptIdentity("monolithic", 1),
        )
    )
    canonical_x = _reason(
        "summary_effect_unmodeled", cause=_v2_projection_cause("x"), target="x",
        action_status="pending_proof", requirement_kinds=("effect_summary_completion",),
        pair_or_case=("case-l", "case-r"),
    )
    payloads.append(_payload(
        emit_debug_trace=emit_debug_trace,
        case="with_completions", outcome="UNKNOWN", trace=trace,
        unknown_reasons=[canonical_x],
    ))

    # --- 2. UNKNOWN: completion / transition が 1 件も無い（0 件と unknown の別） ---
    cause_w = _unary_cause("callsite-w")
    r_w = _reason(
        "return_coverage_gap", cause=cause_w, target="w", action_status="pending_proof",
    )
    r_ops = _reason(
        "decompilation_failed", cause=_unary_cause("expr-op"), target="op",
    )
    trace2 = DebugTrace(attempts=[_attempt(0, "pairwise", [r_w, r_ops])])
    canonical_w = _reason(
        "return_coverage_gap", cause=_v2_projection_cause("w"), target="w",
        action_status="pending_proof",
    )
    payloads.append(_payload(
        emit_debug_trace=emit_debug_trace,
        case="no_completions", outcome="UNKNOWN", trace=trace2, unknown_reasons=[canonical_w],
    ))

    # --- 3. TIMEOUT ---
    r_t = _reason(
        "solver_unknown_timeout", cause=_unary_cause("loop-t"), target="t",
        action_status="no_registered_plan",
    )
    trace3 = DebugTrace(attempts=[_attempt(0, "pairwise", [r_t], transition="TIMEOUT")])
    canonical_t = _reason(
        "solver_unknown_timeout", cause=_v2_projection_cause("t"), target="t",
        action_status="no_registered_plan",
    )
    payloads.append(_payload(
        emit_debug_trace=emit_debug_trace,
        case="timeout_case", outcome="TIMEOUT", trace=trace3, unknown_reasons=[canonical_t],
    ))

    # --- 4. ERROR ---
    trace4 = DebugTrace(
        attempts=[_attempt(0, "pairwise", [], result=None, transition="critical_error")],
        error_message="strategy_exception",
    )
    payloads.append(_payload(
        emit_debug_trace=emit_debug_trace,
        case="error_case", outcome="ERROR", trace=trace4, error_message="strategy_exception",
    ))

    # --- 5. EQUIVALENT ---
    trace5 = DebugTrace(
        attempts=[_attempt(0, "pairwise", [], result=True, transition="UNSAT")],
        final_result=True,
    )
    payloads.append(_payload(
        emit_debug_trace=emit_debug_trace,
        case="eq_case", outcome="EQUIVALENT", trace=trace5, is_equivalent=True,
    ))

    # --- 6. NOT_EQ ---
    trace6 = DebugTrace(
        attempts=[_attempt(0, "pairwise", [], result=False, transition="SAT")],
        final_result=False,
    )
    payloads.append(_payload(
        emit_debug_trace=emit_debug_trace,
        case="not_eq_case", outcome="NOT_EQ", trace=trace6, is_equivalent=False,
    ))
    return payloads


# ---------------------------------------------------------------------------
# 比較面（O と R で同じ関数を使うが、経路は別）
# ---------------------------------------------------------------------------

# final reason authority が決める surface（A の対象）。O と R では同じ
# canonical payload から読むので、ここが一致しても diagnostic の一致は言えない。
FINAL_REASON_SURFACE_NAMES = (
    "unknown_results",
    "unknown_units",
    "final_result_counts",
    "unknown_by_reason",
    "unknown_by_decision_effect",
    "unknown_by_reason_scope",
    "unknown_by_reason_detail",
)
# diagnostic source が決める surface（B の対象）。O は full `debug_trace`、
# R は `unknown_cause_aggregate` という**別経路**から作る。
DIAGNOSTIC_SURFACE_NAMES = (
    "validation_unknown_unit_multiset",
    "reason_record_multiset",
    "proof_action_multiset",
    "proof_backlog_by_reason",
    "proof_backlog_by_proof_kind",
    "proof_backlog_by_recovery_action",
    "proof_backlog_by_action_status",
    "operational_unknown_by_reason",
    "operational_unknown_by_class",
)


def _final_reason_surface(summary_dict):
    return {name: summary_dict[name] for name in FINAL_REASON_SURFACE_NAMES}


def _diagnostic_surface(summary_dict):
    """診断系 surface 一式。root blocker / completion / causal status を含む。"""
    root = summary_dict["root_blocker_summary"]
    surface = {name: summary_dict[name] for name in DIAGNOSTIC_SURFACE_NAMES}
    surface["root_active_count"] = root["active_root_blocker_count"]
    surface["root_candidate_count"] = root["candidate_root_blocker_count"]
    surface["root_required_unique_proofs"] = root["required_unique_proof_count"]
    surface["root_active_blocker_ids"] = sorted(
        repr(item["blocker_id"]) for item in root["active_root_blockers"]
    )
    surface["root_candidate_blocker_ids"] = sorted(
        repr(item["blocker_id"]) for item in root["observed_candidate_blockers"]
    )
    # per-blocker の内訳（affected results / case pairs / required proofs /
    # observed reason ids / causal certainty）まで比べる。
    surface["root_active_blocker_shape"] = sorted(
        (
            repr(item["blocker_id"]),
            len(item["affected_unknown_results"]),
            len(item["affected_case_pairs"]),
            len(item["required_proof_ids"]),
            tuple(item["observed_reason_ids"]),
            tuple(item["causal_certainties"]),
            item["proof_requirements_complete"],
        )
        for item in root["active_root_blockers"]
    )
    # coverage は completion linkage / transition emission を含むので、
    # completion と causal transition の集計はここで比較される。
    surface["root_coverage"] = root["coverage"]
    surface["root_diagnostics"] = root["diagnostics"]
    # completion / causal transition の集計そのもの。
    surface["causal_evidence"] = summary_dict["causal_evidence"]
    return surface


def _reporting_surface(payloads):
    summary = summarize_validation_unknowns(payloads).to_dict()
    surface = _final_reason_surface(summary)
    surface.update(_diagnostic_surface(summary))
    return surface


def _without_aggregate(payloads):
    out = []
    for payload in copy.deepcopy(payloads):
        payload.pop("unknown_cause_aggregate", None)
        out.append(payload)
    return out


def _without_trace(payloads):
    out = []
    for payload in copy.deepcopy(payloads):
        payload.pop("debug_trace", None)
        # 実 log と同じく JSON を往復させる（tuple/list の差で一致しないことを防ぐ）。
        out.append(json.loads(json.dumps(payload, default=str)))
    return out


# ---------------------------------------------------------------------------
# B: lossless oracle
# ---------------------------------------------------------------------------

def test_aggregate_is_lossless_for_required_reporting():
    """B の oracle: 診断 surface を **別経路**で作って一致を要求する。

    * O -- final reason は canonical authority、診断は full `debug_trace` の
      従来経路。`unknown_cause_aggregate` は入力から外す。
    * R -- final reason は同じ canonical authority、診断は
      `unknown_cause_aggregate`。`debug_trace` は入力から外す。

    O と R が同じ aggregate 由来の view を共有しないので、aggregate の
    どこかが壊れれば必ず食い違う（`test_broken_aggregate_dimension_*` で固定）。
    """
    payloads = _fixture_payloads()

    oracle_inputs = _without_aggregate(payloads)
    replay_inputs = _without_trace(payloads)
    assert all("unknown_cause_aggregate" not in payload for payload in oracle_inputs)
    assert all("debug_trace" not in payload for payload in replay_inputs)
    assert all(
        payload["unknown_cause_aggregate"]["schema"] == UNKNOWN_CAUSE_AGGREGATE_SCHEMA
        for payload in replay_inputs
    )

    oracle_summary = summarize_validation_unknowns(oracle_inputs).to_dict()
    replay_summary = summarize_validation_unknowns(replay_inputs).to_dict()

    # 経路が本当に別であること（見かけの一致でない）。
    assert oracle_summary["diagnostic_sources"] == ["debug_trace"]
    assert replay_summary["diagnostic_sources"] == ["unknown_cause_aggregate"]
    # final reason は両方とも canonical authority から読む（A は同条件）。
    assert oracle_summary["final_reason_sources"] == ["canonical"]
    assert replay_summary["final_reason_sources"] == ["canonical"]

    oracle = _reporting_surface(oracle_inputs)
    replay = _reporting_surface(replay_inputs)
    mismatched = [name for name in oracle if oracle[name] != replay[name]]
    assert mismatched == [], {
        name: (oracle[name], replay[name]) for name in mismatched
    }

    # 一致が vacuous でないこと: 診断側が実際に中身を持っている。
    assert oracle["proof_action_multiset"]
    assert oracle["proof_backlog_by_proof_kind"]
    assert oracle["proof_backlog_by_recovery_action"]
    assert oracle["operational_unknown_by_reason"]
    assert oracle["root_active_count"] > 0
    assert oracle["root_required_unique_proofs"] > 0
    assert oracle["root_coverage"]["typed_cause_coverage"] > 0
    assert oracle["root_coverage"]["transition_emission_coverage"] > 0
    assert oracle["root_coverage"]["evidence_complete"] is True
    assert oracle["causal_evidence"]["proof_completions"]["total"] > 0
    assert oracle["causal_evidence"]["reason_completions"]["total"] > 0
    assert oracle["causal_evidence"]["causal_transitions"]["total"] > 0

    # aggregate も trace も無ければ root blocker は失われ、証拠も観測されない。
    starved_inputs = _without_aggregate(_without_trace(payloads))
    starved = _reporting_surface(starved_inputs)
    assert starved["root_active_count"] == 0
    assert starved["root_candidate_count"] == 0
    # 観測できなかった結果は counter にも diagnostics にも入れない。
    assert starved["root_diagnostics"] == {}
    assert starved["root_coverage"] is None
    assert summarize_validation_unknowns(starved_inputs).to_dict()[
        "root_blocker_summary"
    ]["coverage"] is None


@pytest.mark.parametrize(
    "mutate, label",
    [
        (
            lambda agg: agg["legacy_view"]["proof_action_multiset"].pop(),
            "legacy_view.proof_action_multiset",
        ),
        (
            lambda agg: agg["legacy_view"]["backlog"]["by_proof_kind"].clear(),
            "legacy_view.backlog",
        ),
        (
            lambda agg: agg["completions"]["proof_completions"].__setitem__("total", 99),
            "completions",
        ),
        (
            lambda agg: agg["root_causes"].pop(),
            "root_causes",
        ),
        (
            lambda agg: agg["root_cause_stats"].__setitem__("typed_reasons", 0),
            "root_cause_stats",
        ),
    ],
)
def test_broken_aggregate_dimension_is_detected_by_the_oracle(mutate, label):
    """aggregate の 1 次元を壊したら oracle が必ず気づく（tautological でない）。"""
    payloads = _fixture_payloads()
    oracle = _reporting_surface(_without_aggregate(payloads))

    broken = _without_trace(payloads)
    mutated = False
    for payload in broken:
        aggregate = payload["unknown_cause_aggregate"]
        try:
            mutate(aggregate)
        except (KeyError, TypeError, IndexError):
            continue
        mutated = True
    assert mutated, f"fixture does not exercise {label}"

    replay = _reporting_surface(broken)
    assert oracle != replay, label


def test_aggregate_preserves_legacy_view_separately_from_canonical_counts():
    """legacy 診断件数は legacy_view として保つ。canonical 件数と等値比較しない。"""
    payloads = _fixture_payloads()
    target = payloads[0]
    aggregate = target["unknown_cause_aggregate"]

    legacy_view = aggregate["legacy_view"]
    final_reasons = aggregate["final_reasons"]
    assert legacy_view is not None and final_reasons is not None

    # 従来の trace 集計（legacy 源）を、canonical を持たない payload として再現する。
    legacy_payload = copy.deepcopy(target)
    legacy_payload.pop("decision_receipt", None)
    legacy_payload.pop("final_outcome", None)
    legacy_payload.pop("unknown_cause_aggregate", None)
    legacy_summary = summarize_validation_unknowns([legacy_payload])

    assert legacy_summary.unknown_units == legacy_view["unit_count"]
    assert legacy_summary.unknown_by_reason == legacy_view["by_reason"]
    assert legacy_summary.proof_backlog_by_reason == legacy_view["backlog"]["by_reason"]
    # canonical 側とは別物（片方を他方の検算に使わない）。
    assert legacy_view["record_count"] != final_reasons["record_count"]


# ---------------------------------------------------------------------------
# A: canonical 化（意図的な語彙・件数の変化）
# ---------------------------------------------------------------------------

def test_final_unknown_reasons_prefer_canonical_payload():
    payloads = _fixture_payloads()
    target = payloads[0]
    canonical_ids = sorted(
        record.reason_id for record in _extract_final_unknown_reasons(target)
    )
    legacy_payload = copy.deepcopy(target)
    legacy_payload.pop("decision_receipt")
    legacy_payload.pop("final_outcome")
    legacy_ids = sorted(
        record.reason_id for record in _extract_final_unknown_reasons(legacy_payload)
    )
    trace_ids = sorted(
        str(reason["reason_id"])
        for reason in target["debug_trace"]["attempts"][-1]["unknown_reasons"]
    )
    payload_ids = sorted(str(reason["reason_id"]) for reason in target["unknown_reasons"])

    assert canonical_ids == payload_ids
    assert legacy_ids == trace_ids
    # 2 つの源は実際に違う内容を持っている（比較が vacuous でない）。
    assert canonical_ids != legacy_ids
    # legacy 経路へ回帰していないこと。
    assert canonical_ids != trace_ids


def test_canonical_source_change_is_measured_separately():
    """A の差は現 fixture で毎回測り直す（計画の参考値を転記しない）。"""
    payloads = _fixture_payloads()
    canonical_summary = summarize_validation_unknowns(_without_aggregate(payloads))

    legacy_inputs = []
    for payload in _without_aggregate(payloads):
        payload.pop("decision_receipt", None)
        payload.pop("final_outcome", None)
        legacy_inputs.append(payload)
    legacy_summary = summarize_validation_unknowns(legacy_inputs)

    # 差は「最終 reason をどの record 集合から数えるか」だけに現れる。
    assert canonical_summary.unknown_results == legacy_summary.unknown_results
    assert legacy_summary.unknown_units > canonical_summary.unknown_units
    assert canonical_summary.unknown_by_reason != legacy_summary.unknown_by_reason

    # root blocker は A では動かない（B の情報なので語彙変更の影響を受けない）。
    canonical_root = canonical_summary.root_blocker_summary
    legacy_root = legacy_summary.root_blocker_summary
    assert (
        canonical_root["active_root_blocker_count"]
        == legacy_root["active_root_blocker_count"]
    )
    assert (
        canonical_root["required_unique_proof_count"]
        == legacy_root["required_unique_proof_count"]
    )


def _legacy_payload(case, *, trace, unknown_reasons):
    """`decision_receipt` を持たない legacy payload（最終 reason は legacy 経路で決まる）。"""
    payload = _payload(
        case=case, outcome="UNKNOWN", trace=trace, unknown_reasons=unknown_reasons,
    )
    payload.pop("decision_receipt", None)
    payload.pop("final_outcome", None)
    return payload


def _empty_final_attempt_payload(case="empty_final_attempt"):
    """最終 UNKNOWN attempt はあるが record 0 件。top-level には別 reason を置く。

    誤って payload へ fall through すると `return_coverage_gap` が出るので、
    合成 `unknown` との差で必ず検出できる（fixture が vacuous にならない）。
    """
    top_level = _reason(
        "return_coverage_gap",
        cause=_v2_projection_cause("empty"),
        target="empty",
        action_status="pending_proof",
    )
    return _legacy_payload(
        case,
        trace=DebugTrace(attempts=[_attempt(0, "pairwise", [])]),
        unknown_reasons=[top_level],
    )


def _trace_only(payload):
    """O 側: aggregate を外し full `debug_trace` だけを残す。"""
    out = copy.deepcopy(payload)
    out.pop("unknown_cause_aggregate", None)
    return out


def _aggregate_only(payload):
    """R 側: `debug_trace` を外し aggregate だけを残す（JSON 往復込み）。"""
    out = copy.deepcopy(payload)
    out.pop("debug_trace", None)
    return json.loads(json.dumps(out, default=str))


def test_legacy_trace_with_empty_final_attempt_keeps_the_synthesized_record():
    """最終 attempt はあるが record が 0 件 -- 従来どおり合成 1 件にする。

    aggregate も payload の `unknown_reasons` も先回りして埋めない。「最終
    attempt が無い」(次の源を見る) と「あったが空だった」(結果単位の合成) は別。
    """
    payload = _empty_final_attempt_payload()
    summary = summarize_validation_unknowns([_trace_only(payload)])
    assert summary.final_reason_sources == ("synthesized",)
    assert summary.unknown_units == 1
    assert list(summary.unknown_by_reason) == ["unknown"]

    # canonical payload として読めば、同じ結果から本物の reason が出る（A の差）。
    canonical_payload = _payload(
        case="empty_final_attempt",
        outcome="UNKNOWN",
        trace=DebugTrace(attempts=[_attempt(0, "pairwise", [])]),
        unknown_reasons=[
            _reason(
                "return_coverage_gap",
                cause=_v2_projection_cause("empty"),
                target="empty",
                action_status="pending_proof",
            )
        ],
    )
    canonical_summary = summarize_validation_unknowns([canonical_payload])
    assert canonical_summary.final_reason_sources == ("canonical",)
    assert list(canonical_summary.unknown_by_reason) == ["return_coverage_gap"]


def test_empty_final_attempt_final_reason_is_identical_from_trace_and_aggregate():
    """観測して 0 件の最終 attempt は、trace でも aggregate でも同じ答えになる。"""
    payload = _empty_final_attempt_payload()
    aggregate = payload["unknown_cause_aggregate"]
    # producer は 3 状態を区別できる形で残している。
    assert aggregate["evidence_present"]["legacy_records"] is True
    assert aggregate["legacy_view"]["source"] == "final_attempt"
    assert aggregate["legacy_view"]["record_count"] == 0
    # fixture が vacuous でないこと: top-level には別の reason がある。
    assert [item["reason_id"] for item in payload["unknown_reasons"]] == [
        "return_coverage_gap"
    ]

    oracle_input, replay_input = _trace_only(payload), _aggregate_only(payload)
    oracle = summarize_validation_unknowns([oracle_input])
    replay = summarize_validation_unknowns([replay_input])

    # 経路は別（O は trace、R は aggregate）。
    assert oracle.diagnostic_sources == ("debug_trace",)
    assert replay.diagnostic_sources == ("unknown_cause_aggregate",)

    # final reason authority の答えが一致し、どちらも合成 `unknown`。
    assert oracle.final_reason_sources == replay.final_reason_sources == ("synthesized",)
    assert oracle.unknown_units == replay.unknown_units == 1
    assert oracle.unknown_by_reason == replay.unknown_by_reason == {"unknown": 1}
    # top-level の reason へ fall through していないこと。
    assert "return_coverage_gap" not in oracle.unknown_by_reason
    assert "return_coverage_gap" not in replay.unknown_by_reason

    # reporting surface 全体でも一致する。
    assert _reporting_surface([oracle_input]) == _reporting_surface([replay_input])


def test_final_reason_source_selection_matrix():
    """最終 attempt の 3 状態 x (trace のみ / aggregate のみ) を固定する。"""
    records_reason = _reason(
        "summary_effect_unmodeled", cause=_unary_cause("matrix"), target="matrix",
        action_status="pending_proof", requirement_kinds=("effect_summary_completion",),
    )
    top_level = _reason(
        "return_coverage_gap", cause=_v2_projection_cause("matrix"), target="matrix",
        action_status="pending_proof",
    )

    cases = {
        # 1. 最終 attempt 無し（SAT で終わった trace）-> 次の源（payload）へ進める
        "absent": (
            _legacy_payload(
                "absent",
                trace=DebugTrace(
                    attempts=[_attempt(0, "pairwise", [], result=False, transition="SAT")]
                ),
                unknown_reasons=[top_level],
            ),
            ("payload",),
            {"return_coverage_gap": 1},
        ),
        # 2. 最終 attempt あり・record > 0 -> その legacy record
        "records": (
            _legacy_payload(
                "records",
                trace=DebugTrace(attempts=[_attempt(0, "pairwise", [records_reason])]),
                unknown_reasons=[top_level],
            ),
            ("legacy_trace", "aggregate_legacy"),
            {"summary_effect_unmodeled": 1},
        ),
        # 3. 最終 attempt あり・record == 0 -> 合成 unknown、payload へ進まない
        "empty": (
            _empty_final_attempt_payload("empty"),
            ("synthesized",),
            {"unknown": 1},
        ),
    }
    for name, (payload, allowed_sources, expected_reasons) in cases.items():
        for label, view in (("trace", _trace_only(payload)), ("aggregate", _aggregate_only(payload))):
            summary = summarize_validation_unknowns([view])
            assert summary.unknown_by_reason == expected_reasons, (name, label)
            assert summary.final_reason_sources[0] in allowed_sources, (name, label)
        # 経路が違っても答えは同じ。
        assert (
            summarize_validation_unknowns([_trace_only(payload)]).unknown_by_reason
            == summarize_validation_unknowns([_aggregate_only(payload)]).unknown_by_reason
        ), name

    # 4. trace 無し + aggregate にも legacy evidence 無し -> payload fallback
    absent_evidence = _trace_absent_typed_cause_payload("matrix_absent")
    absent_summary = summarize_validation_unknowns([absent_evidence])
    assert absent_summary.diagnostic_sources == ("payload_fallback",)
    assert absent_summary.final_reason_sources == ("payload",)
    assert list(absent_summary.unknown_by_reason) == ["summary_effect_unmodeled"]

    # 5. 生成時に trace があり serialize 後に除去 -> aggregate だけで 1〜3 を再現
    for name, (payload, _sources, expected_reasons) in cases.items():
        replay = summarize_validation_unknowns([_aggregate_only(payload)])
        assert replay.unknown_by_reason == expected_reasons, name


def test_legacy_payload_without_aggregate_uses_full_trace():
    """aggregate の無い古い log は従来どおり trace から集計する（unknown に丸めない）。"""
    payloads = _fixture_payloads()
    legacy_inputs = []
    for payload in _without_aggregate(payloads):
        payload.pop("decision_receipt", None)
        payload.pop("final_outcome", None)
        legacy_inputs.append(payload)
    summary = summarize_validation_unknowns(legacy_inputs)

    assert summary.unknown_units > 0
    assert summary.proof_backlog_by_proof_kind
    assert summary.root_blocker_summary["active_root_blocker_count"] > 0
    assert summary.evidence_missing == ()
    assert "legacy_trace" in summary.final_reason_sources


# ---------------------------------------------------------------------------
# 情報保全（unknown / 0、identity ごとの status、completion と backlog の分離）
# ---------------------------------------------------------------------------

def test_aggregate_distinguishes_unknown_from_zero():
    with_trace = _fixture_payloads()[1]["unknown_cause_aggregate"]
    assert with_trace["completions"]["proof_completions"]["total"] == 0
    assert with_trace["transitions"]["causal_transitions"]["total"] == 0
    assert with_trace["evidence_present"]["completion_events"] is True
    assert with_trace["evidence_present"]["causal_transitions"] is True

    no_trace_result = EquivalenceResult(
        is_equivalent=None,
        function1_name="f",
        function2_name="f",
        binary1_name="left",
        binary2_name="right",
        solver_results=None,
    )
    without_trace = build_unknown_cause_aggregate(no_trace_result)
    assert without_trace["completions"] is None
    assert without_trace["transitions"] is None
    assert without_trace["attempts"] is None
    assert without_trace["evidence_present"]["completion_events"] is False
    assert without_trace["evidence_present"]["causal_transitions"] is False
    # canonical 確定値が無いので final_reasons も unknown（0 件だと書かない）。
    assert without_trace["final_reasons"] is None
    assert without_trace["evidence_present"]["canonical_reasons"] is False


def test_root_cause_status_resolved_per_identity():
    aggregate = _fixture_payloads()[0]["unknown_cause_aggregate"]
    by_reason = {}
    for cause in aggregate["root_causes"]:
        by_reason.setdefault(cause["reason_id"], []).append(cause)

    shared = by_reason["summary_effect_unmodeled"]
    # 同じ reason_id に 2 つの cause identity があり、status は別々に決まる。
    assert len(shared) == 2
    assert {cause["causal_status"] for cause in shared} == {"active", "completed"}
    completed = next(cause for cause in shared if cause["causal_status"] == "completed")
    active = next(cause for cause in shared if cause["causal_status"] == "active")
    assert completed["active"] is None
    assert completed["causal_status_counts"] == {"discharged": 1}
    assert active["active"]["occurrence_count"] == 1
    # active な cause は 2 occurrence のうち 1 件（superseded の方）を active に含めない。
    assert active["all"]["occurrence_count"] == 2
    assert active["causal_status_counts"] == {
        "superseded": 1, "active_final_blocker": 1,
    }
    # diagnostic_only の cause は「active でも completed でもない」= unknown。
    other = by_reason["return_width_bridge_missing"]
    assert {cause["causal_status"] for cause in other} == {"active"}


def test_completion_and_backlog_are_separate():
    """backlog は未完了 record から、completion は event から。差し引きで作らない。"""
    payloads = _fixture_payloads()
    with_completion = payloads[0]["unknown_cause_aggregate"]
    assert with_completion["completions"]["proof_completions"]["total"] == 1
    assert with_completion["completions"]["reason_completions"]["total"] == 1
    assert with_completion["completions"]["reason_completions"]["by_reason"] == {
        "summary_effect_unmodeled": 1
    }

    # completion event を取り除いても backlog は変わらない（推定していない証拠）。
    stripped = copy.deepcopy(payloads[0])
    trace = stripped["debug_trace"]
    trace["proof_completion_events"] = []
    trace["reason_completion_events"] = []
    rebuilt = summarize_validation_unknowns([stripped])
    original = summarize_validation_unknowns([payloads[0]])
    assert rebuilt.proof_backlog_by_reason == original.proof_backlog_by_reason
    assert rebuilt.proof_backlog_by_action_status == original.proof_backlog_by_action_status

    # completion が 0 件の結果でも backlog は独立に出る。
    no_completion = payloads[1]["unknown_cause_aggregate"]
    assert no_completion["completions"]["proof_completions"]["total"] == 0
    assert no_completion["backlog"]["by_reason"]


def test_aggregate_is_not_a_debug_trace_copy():
    payload = _fixture_payloads()[0]
    aggregate = payload["unknown_cause_aggregate"]

    def _keys(value):
        if isinstance(value, dict):
            for key, item in value.items():
                yield str(key)
                yield from _keys(item)
        elif isinstance(value, (list, tuple)):
            for item in value:
                yield from _keys(item)

    present = set(_keys(aggregate))
    for forbidden in (
        "reason_record",
        "reason_occurrences",
        "solver_results",
        "final_smt",
        "final_smt_excerpt",
        "counterexample",
        "object_evidence",
        "object_target_key",
        "typed_cause_key",
        "normalization_rules",
        "unknown_recovery_actions",
        "unknown_reasons",
        "detail",
    ):
        assert forbidden not in present, forbidden
    # `reason_id | detail` は `unknown_by_reason_detail` の集計キーなので残る
    # （reporting が要求する surface）。残らないのは record 本体・solver 行・SMT。
    blob = json.dumps(aggregate, default=str)
    trace_blob = json.dumps(payload["debug_trace"], default=str)
    assert len(blob) < len(trace_blob)


def test_reporting_does_not_double_count_when_both_present():
    payloads = _fixture_payloads()
    both = _reporting_surface(copy.deepcopy(payloads))
    aggregate_only = _reporting_surface(_without_trace(payloads))
    assert both == aggregate_only

    # trace のみ（aggregate 無し）と比べても occurrence が 2 倍にならない。
    trace_only = _reporting_surface(_without_aggregate(payloads))
    assert both["root_candidate_count"] == trace_only["root_candidate_count"]
    assert both["unknown_units"] == trace_only["unknown_units"]


def test_run_health_summary_parses_unknown_and_none_markers(tmp_path):
    from scripts.function_tracer_pcode.reporting.result_summary import (
        format_run_health_summary,
    )
    from scripts.function_tracer_pcode.reporting.run_health_summary import (
        parse_overall_summary_health,
    )

    # (1) health JSON -> text: 証拠の無い section だけ `(unknown)`。
    health = {
        "total_results": 1,
        "final_result_counts": {},
        "unknown_results": 1,
        "unknown_units": 1,
        "unknown_by_reason": {"summary_effect_unmodeled": 1},
        "proof_backlog_by_reason": {},
        "operational_unknown_by_reason": {},
        "evidence_missing_sections": ["proof_backlog_by_reason"],
    }
    rendered = format_run_health_summary(health)
    assert "  proof_backlog_by_reason:\n    (unknown)" in rendered
    assert "  operational_unknown_by_reason:\n    (none)" in rendered

    # (2) overall_summary.txt -> health: 源・観測件数・`(unknown)`/`(none)` が往復する。
    def _round_trip(summary, name):
        path = tmp_path / name
        path.write_text(format_validation_unknown_summary(summary) + "\n")
        return parse_overall_summary_health(path)

    missing = _round_trip(
        summarize_validation_unknowns([_no_source_payload()]),
        "missing.txt",
    )
    assert missing["diagnostic_sources"] == ["payload_fallback"]
    assert missing["diagnostic_evidence"] == {"observed": 0, "missing": 1}
    assert "proof_backlog_by_reason" in missing["evidence_missing_sections"]
    assert "proof_backlog_by_proof_kind" in missing["evidence_missing_sections"]
    assert missing["proof_backlog_by_reason"] == {}

    observed = _round_trip(
        summarize_validation_unknowns(_trace_removed_payloads()), "observed.txt"
    )
    assert observed["final_reason_sources"] == ["canonical"]
    assert observed["diagnostic_sources"] == ["unknown_cause_aggregate"]
    assert observed["diagnostic_evidence"] == {"observed": 3, "missing": 0}
    assert observed["evidence_missing_sections"] == []
    assert observed["unknown_by_reason"]

    mixed = _round_trip(
        summarize_validation_unknowns(
            _trace_removed_payloads()
            + [_no_source_payload("missing")]
        ),
        "mixed.txt",
    )
    assert sorted(mixed["diagnostic_sources"]) == ["payload_fallback", "unknown_cause_aggregate"]
    assert mixed["diagnostic_evidence"] == {"observed": 3, "missing": 1}
    assert mixed["causal_evidence_counts"]["proof_completions"] == {"observed": 3, "missing": 1}

    # 元から trace が無い run では causal block は unknown として往復する。
    absent = _round_trip(
        summarize_validation_unknowns([_trace_absent_payload()]), "absent.txt"
    )
    assert absent["diagnostic_sources"] == ["payload_fallback"]
    assert absent["causal_evidence_counts"]["causal_transitions"] == {"observed": 0, "missing": 1}


def _trace_absent_payload(case="trace_absent"):
    """ケース A: **もともと trace が無い**結果。aggregate は在る。

    `evidence_present.debug_trace` は False で、trace 由来の診断 block は
    観測できていない。これを「観測して 0 件」と読んではいけない。
    """
    payload = EquivalenceResult(
        is_equivalent=None,
        function1_name=case,
        function2_name=case,
        binary1_name="left",
        binary2_name="right",
        solver_results=None,
        binary1_content_identity=BIN1,
        binary2_content_identity=BIN2,
        function1_identity=("function", "left", case),
        function2_identity=("function", "right", case),
    ).to_dict()
    payload["case_id"] = case
    return payload


def _no_source_payload(case="no_source"):
    """診断源をどちらも持たない結果（aggregate も trace も無い）。"""
    payload = _trace_absent_payload(case)
    payload.pop("unknown_cause_aggregate")
    return payload


def _trace_removed_payloads():
    """ケース B: 生成時に trace があり、serialize 後に trace だけ取り除いた結果。"""
    return _without_trace(_fixture_payloads())


def _trace_absent_typed_cause_payload(case="trace_absent_typed"):
    """trace は無いが、top-level `unknown_reasons` に v1 typed cause を持つ結果。

    producer はこの record から root cause を作れてしまう。観測できていない値を
    observed 集計へ混ぜないことを確かめるための、空でない missing fixture。
    """
    reason = _reason(
        "summary_effect_unmodeled",
        cause=_unary_cause("callsite-absent"),
        target="absent",
        action_status="pending_proof",
        requirement_kinds=("effect_summary_completion",),
    )
    result = EquivalenceResult(
        is_equivalent=None,
        function1_name=case,
        function2_name=case,
        binary1_name="left",
        binary2_name="right",
        solver_results=None,
        unknown_reasons=[reason],
        binary1_content_identity=BIN1,
        binary2_content_identity=BIN2,
        function1_identity=("function", "left", case),
        function2_identity=("function", "right", case),
    )
    payload = result.to_dict()
    payload["case_id"] = case
    return payload


def test_trace_absent_typed_cause_is_missing_root_blocker_evidence():
    """trace 無しでも root cause は作れてしまうが、それは観測された証拠ではない。"""
    payload = _trace_absent_typed_cause_payload()
    aggregate = payload["unknown_cause_aggregate"]
    # producer: cause は作れている（= 空 payload では検出できない経路）。
    assert aggregate["root_causes"], "fixture must produce root causes"
    assert aggregate["root_cause_stats"]["typed_reasons"] > 0
    assert aggregate["evidence_present"]["debug_trace"] is False

    summary = summarize_root_blockers([payload])
    # consumer: observed 集計にも blocker にも入れない。
    assert summary.active_root_blocker_count == 0
    assert summary.candidate_root_blocker_count == 0
    assert summary.diagnostics == {}
    assert summary.coverage is None


def test_missing_typed_cause_payload_does_not_move_observed_root_blockers():
    """mixed run: missing 側を足しても observed の blocker 集計は 1 つも動かない。"""
    observed_inputs = _trace_removed_payloads()
    observed = summarize_root_blockers(observed_inputs).to_dict()
    mixed = summarize_root_blockers(
        observed_inputs + [_trace_absent_typed_cause_payload()]
    ).to_dict()

    for name in (
        "active_root_blocker_count",
        "candidate_root_blocker_count",
        "required_unique_proof_count",
        "diagnostics",
    ):
        assert observed[name] == mixed[name], name
    assert [item["blocker_id"] for item in observed["active_root_blockers"]] == [
        item["blocker_id"] for item in mixed["active_root_blockers"]
    ]
    # coverage の分母分子も観測できた結果だけから作る。
    ratios = (
        "typed_cause_coverage",
        "explicit_causal_status_coverage",
        "case_pair_identity_coverage",
        "transition_emission_coverage",
        "proof_completion_linkage_coverage",
    )
    for name in ratios:
        assert observed["coverage"][name] == mixed["coverage"][name], name
    # 変わるのは観測状況の表示だけ。
    assert observed["coverage"]["evidence_state"] == "complete"
    assert mixed["coverage"]["evidence_state"] == "partial"
    assert mixed["coverage"]["evidence_complete"] is False
    assert mixed["coverage"]["results_without_evidence"] == 1
    assert (
        mixed["coverage"]["results_with_evidence"]
        == observed["coverage"]["results_with_evidence"]
    )


def test_attempts_evidence_separates_absent_from_observed_zero():
    """`attempts` も「観測できなかった」と「観測して 0 件」を分ける。"""
    absent = _trace_absent_payload()["unknown_cause_aggregate"]
    assert absent["attempts"] is None
    assert absent["evidence_present"]["attempts"] is False

    empty_trace = _payload(
        case="empty_trace", outcome="UNKNOWN", trace=DebugTrace(attempts=[]),
    )["unknown_cause_aggregate"]
    assert empty_trace["attempts"]["count"] == 0
    assert empty_trace["evidence_present"]["attempts"] is True

    with_attempts = _trace_removed_payloads()[0]["unknown_cause_aggregate"]
    assert with_attempts["attempts"]["count"] > 0
    assert with_attempts["evidence_present"]["attempts"] is True

    # completion / transition / legacy_records / debug_trace も同じ意味体系。
    for name in ("debug_trace", "completion_events", "causal_transitions", "legacy_records"):
        assert absent["evidence_present"][name] is False, name
        assert empty_trace["evidence_present"][name] is True, name


def test_case_a_trace_originally_absent_is_unknown_not_observed_zero():
    payload = _trace_absent_payload()
    aggregate = payload["unknown_cause_aggregate"]
    # producer: trace を観測していないことを証言する。
    assert aggregate["evidence_present"]["debug_trace"] is False
    assert aggregate["evidence_present"]["completion_events"] is False
    assert aggregate["evidence_present"]["causal_transitions"] is False
    assert aggregate["legacy_view"] is None
    assert aggregate["completions"] is None
    assert aggregate["transitions"] is None

    summary = summarize_validation_unknowns([payload])
    # consumer: aggregate が在るだけでは観測済みにしない。
    assert summary.diagnostic_sources == ("payload_fallback",)
    assert summary.diagnostic_evidence == {"observed": 0, "missing": 1}
    assert summary.evidence_missing
    for name in ("proof_completions", "reason_completions", "causal_transitions"):
        assert summary.causal_evidence[name] is None, name
        assert summary.causal_evidence_counts[name] == {"observed": 0, "missing": 1}
    assert summary.root_blocker_summary["coverage"] is None


def test_case_b_trace_removed_after_serialization_is_fully_observed():
    payloads = _trace_removed_payloads()
    assert all("debug_trace" not in payload for payload in payloads)
    for payload in payloads:
        aggregate = payload["unknown_cause_aggregate"]
        # producer: trace を観測した上で畳んだので、診断の材料が残っている。
        assert aggregate["evidence_present"]["debug_trace"] is True
        assert aggregate["legacy_view"] is not None
        assert aggregate["completions"] is not None
        assert aggregate["transitions"] is not None

    summary = summarize_validation_unknowns(payloads)
    assert summary.diagnostic_sources == ("unknown_cause_aggregate",)
    assert summary.diagnostic_evidence == {"observed": 3, "missing": 0}
    assert summary.evidence_missing == ()
    for name in ("proof_completions", "reason_completions", "causal_transitions"):
        assert summary.causal_evidence[name] is not None, name
        assert summary.causal_evidence_counts[name]["missing"] == 0
    coverage = summary.root_blocker_summary["coverage"]
    assert coverage["evidence_state"] == "complete"
    assert coverage["evidence_complete"] is True
    assert coverage["results_without_evidence"] == 0
    # PR-128-B で trace を省いても root blocker を再構成できる。
    assert summary.root_blocker_summary["active_root_blocker_count"] > 0


def test_completion_and_transition_observed_zero_differs_from_unknown():
    """観測して 0 件（`total: 0`）と、観測できなかった（`None`）を分ける。"""
    # 観測済み 0 件: trace はあるが completion も transition も 1 件も無い結果。
    zero = [
        payload
        for payload in _trace_removed_payloads()
        if payload["case_id"] == "no_completions"
    ]
    assert len(zero) == 1
    observed = summarize_validation_unknowns(zero)
    assert observed.causal_evidence["proof_completions"] == {
        "total": 0, "by_proof_kind": {}, "by_proof_status": {}, "by_reason": {},
    }
    assert observed.causal_evidence["causal_transitions"] == {
        "total": 0, "by_transition_kind": {}, "by_status_pair": {},
    }
    assert observed.causal_evidence_counts["proof_completions"] == {"observed": 1, "missing": 0}

    # unknown: 観測できていない結果。`{}` や 0 に潰さない。
    unknown = summarize_validation_unknowns([_trace_absent_payload()])
    assert unknown.causal_evidence["proof_completions"] is None
    assert unknown.causal_evidence["causal_transitions"] is None
    assert unknown.causal_evidence_counts["causal_transitions"] == {"observed": 0, "missing": 1}


def test_partial_evidence_all_observed_reports_a_real_zero():
    """全件に診断源がある run では、空の集計は本当に 0 件（`(none)`）。"""
    summary = summarize_validation_unknowns(_trace_removed_payloads())
    assert summary.diagnostic_evidence == {"observed": 3, "missing": 0}
    assert summary.evidence_missing == ()
    assert summary.diagnostic_sources == ("unknown_cause_aggregate",)
    rendered = format_validation_unknown_summary(summary)
    assert "(observed 3 / missing 0)" in rendered

    # 診断源はあるが backlog が 0 件、というケースも `(none)` のまま。
    zero = summarize_validation_unknowns([
        payload
        for payload in _trace_removed_payloads()
        if payload["case_id"] == "timeout_case"
    ])
    assert zero.diagnostic_evidence == {"observed": 1, "missing": 0}
    assert zero.evidence_missing == ()
    assert zero.proof_backlog_by_proof_kind == {}
    assert "Proof backlog by proof_kind:\n    (none)" in format_validation_unknown_summary(zero)


def test_partial_evidence_all_missing_is_unknown_not_zero():
    """診断源がどこにも無い run は、空の集計を `(unknown)` として出す。"""
    summary = summarize_validation_unknowns([_no_source_payload()])
    assert summary.diagnostic_evidence == {"observed": 0, "missing": 1}
    assert summary.diagnostic_sources == ("payload_fallback",)
    assert "proof_backlog_by_proof_kind" in summary.evidence_missing
    rendered = format_validation_unknown_summary(summary)
    assert "Proof backlog by proof_kind:\n    (unknown)" in rendered
    assert "(observed 0 / missing 1)" in rendered
    assert summary.root_blocker_summary["coverage"] is None


def test_partial_evidence_mixed_does_not_collapse_to_a_known_zero():
    """1 件でも診断源が欠けたら、run 全体を完全観測済みとして扱わない。"""
    observed = _trace_removed_payloads()
    summary = summarize_validation_unknowns(observed + [_no_source_payload("missing")])

    assert summary.diagnostic_evidence == {"observed": 3, "missing": 1}
    assert set(summary.diagnostic_sources) == {"unknown_cause_aggregate", "payload_fallback"}
    # 観測できた分の件数は残る（欠測で全部 0 にはしない）。
    assert summary.proof_action_multiset
    # しかし run 全体は partial なので、空の集計は `(unknown)` 側に倒す。
    assert summary.evidence_missing
    rendered = format_validation_unknown_summary(summary)
    assert "(observed 3 / missing 1)" in rendered

    # causal block も partial（観測できた 3 件分の値 + 欠測 1 件）。
    for name in ("proof_completions", "reason_completions", "causal_transitions"):
        assert summary.causal_evidence[name] is not None, name
        assert summary.causal_evidence_counts[name] == {"observed": 3, "missing": 1}

    # root blocker の coverage も「完全観測」と言わない。
    coverage = summary.root_blocker_summary["coverage"]
    assert coverage["evidence_state"] == "partial"
    assert coverage["evidence_complete"] is False
    assert coverage["results_with_evidence"] == len(_fixture_payloads())
    assert coverage["results_without_evidence"] == 1


def test_root_blocker_coverage_is_unknown_without_causal_evidence():
    payload = EquivalenceResult(
        is_equivalent=None,
        function1_name="f",
        function2_name="f",
        binary1_name="left",
        binary2_name="right",
        solver_results=None,
        binary1_content_identity=BIN1,
        binary2_content_identity=BIN2,
        function1_identity=("function", "left", "f"),
        function2_identity=("function", "right", "f"),
    ).to_dict()
    payload.pop("unknown_cause_aggregate")
    assert summarize_root_blockers([payload]).coverage is None
    with_trace = _fixture_payloads()[1]
    assert summarize_root_blockers([with_trace]).coverage is not None


def test_to_dict_always_emits_unknown_cause_aggregate():
    result = EquivalenceResult(
        is_equivalent=True,
        function1_name="f",
        function2_name="f",
        binary1_name="left",
        binary2_name="right",
        solver_results=None,
    )
    payload = result.to_dict()
    assert payload["unknown_cause_aggregate"]["schema"] == UNKNOWN_CAUSE_AGGREGATE_SCHEMA
    # 一度確定した aggregate は to_dict で作り直さない（preimage 固定のため）。
    marker = {"schema": UNKNOWN_CAUSE_AGGREGATE_SCHEMA, "marker": True}
    result.unknown_cause_aggregate = marker
    assert result.to_dict()["unknown_cause_aggregate"] is marker


def test_identity_pool_round_trips_required_proof_ids():
    aggregate = _fixture_payloads()[0]["unknown_cause_aggregate"]
    pool = aggregate["identity_pool"]
    assert pool, "identity pool should hold the repeated identities"
    for cause in aggregate["root_causes"]:
        resolved = resolve_pool_refs(pool, cause["all"]["required_proof_id_refs"])
        assert len(resolved) == len(set(map(repr, resolved)))
        if cause["active"]:
            active = resolve_pool_refs(pool, cause["active"]["required_proof_id_refs"])
            assert set(map(repr, active)) <= set(map(repr, resolved))


# ---------------------------------------------------------------------------
# digest 契約（独立 finalization 2 本）
# ---------------------------------------------------------------------------

def test_aggregate_changes_preimage_but_no_semantic_field(tmp_path, monkeypatch):
    from scripts.function_tracer_pcode.authority.decision.canonical_result import (
        validate_canonical_result_finalization_bundle,
    )
    from scripts.function_tracer_pcode.tests.unit._finalization_support import (
        _independent_finalization,
    )

    bundle_key = tmp_path / "canonical-bundle.key"
    bundle_key.write_bytes(b"k" * 32)
    monkeypatch.setenv("UNKNOWN_TAXONOMY_V2_SUPERVISOR_KEY_ID", "issue128-test-key")
    monkeypatch.setenv("UNKNOWN_TAXONOMY_V2_SUPERVISOR_KEY_FILE", str(bundle_key))
    monkeypatch.setenv(
        "UNKNOWN_TAXONOMY_V2_RESULT_ENTRY_OCCURRENCE_NONCE", "issue128-occurrence"
    )

    def _result():
        return EquivalenceResult(
            is_equivalent=True,
            function1_name="f",
            function2_name="f",
            binary1_name="left",
            binary2_name="right",
            solver_results=None,
        )

    payload_with = _result().to_dict()
    payload_without = _result().to_dict()
    payload_without.pop("unknown_cause_aggregate")

    assert payload_with != payload_without
    assert {k: v for k, v in payload_with.items() if k != "unknown_cause_aggregate"} == (
        payload_without
    )

    bundle_without, session_a, evidence_a = _independent_finalization(
        tmp_path, monkeypatch,
        case_id="issue128-without-aggregate", result_payload_preimage=payload_without,
    )
    bundle_with, session_b, evidence_b = _independent_finalization(
        tmp_path, monkeypatch,
        case_id="issue128-with-aggregate", result_payload_preimage=payload_with,
    )
    # 2 本は独立: session / evidence / bundle のどれも共有していない。
    assert session_a is not session_b
    assert evidence_a is not evidence_b
    assert evidence_a.pilot_result is not evidence_b.pilot_result
    assert bundle_without is not bundle_with

    for bundle, preimage in ((bundle_without, payload_without), (bundle_with, payload_with)):
        validated = validate_canonical_result_finalization_bundle(
            bundle,
            result_payload_preimage=preimage,
            bundle_verification_key_id="issue128-test-key",
            bundle_verification_key=b"k" * 32, work=SealWorkBudget.for_result()
        )
        assert validated["outcome"] == "EQUIVALENT"

    # serialization surface が変わるので preimage digest は変わる（意図どおり）。
    assert (
        bundle_without["canonical_result_payload_preimage_digest"]
        != bundle_with["canonical_result_payload_preimage_digest"]
    )
    # semantic projection は診断を読まないので 1 field も変わらない。
    assert (
        bundle_without["canonical_semantic_result_projection"]["payload"]
        == bundle_with["canonical_semantic_result_projection"]["payload"]
    )
    assert (
        bundle_without["canonical_semantic_result_projection"]["semantic_projection_digest"]
        == bundle_with["canonical_semantic_result_projection"]["semantic_projection_digest"]
    )
    projection = bundle_with["canonical_semantic_result_projection"]["payload"]
    assert projection["canonical_outcome"] == "EQUIVALENT"
    assert "unknown_cause_aggregate" not in projection

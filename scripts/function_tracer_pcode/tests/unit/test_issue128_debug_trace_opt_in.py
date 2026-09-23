# -*- coding: utf-8 -*-
"""Issue #128 PR-128-B: `debug_trace` の **serialize だけ** を debug 指定で条件化する。

この file が固定する契約は 3 本ある。

* **serialize の条件化**: `to_dict()` は `emit_debug_trace` が True のときだけ
  `debug_trace` key を出す。既定は True なので `EquivalenceResult` を直接組む
  呼び出し元の挙動は変わらない。production では `checker/workflow.py` が既存の
  debug 伝播（`--debug` / `-d` / `EQBENCH_DEBUG=1`）をそのまま入れる。
* **生成停止ではない**: trace object は常に作られ、結果に残る。object 読者
  （diagnostics / attempts / `LegacyExecutionSnapshot` の event surface /
  `to_string(show_phase_usage)` / `unknown_cause_aggregate` の生成）は従来どおり
  full trace を読める。`evidence_present.debug_trace` は「JSON に出したか」では
  なく「aggregate 生成時に trace を観測できたか」なので、添付を止めても True。
* **canonical 契約は無変更**: `debug_trace` key の有無は serialization surface
  なので preimage digest は変わるが、semantic projection は 1 field も変わらず、
  trace 無しの payload でも bundle の validate / replay が通る。

PR-128-A の lossless oracle（`test_issue128_cause_aggregate.py`）が「trace を
省いても reporting が失われない」ことを保証しているので、ここでは
**実際の serialization 経路** がその oracle と同じ payload を作ることを固定する。
"""

import copy
import inspect
import json
import re
from pathlib import Path

import pytest

from scripts.function_tracer_pcode.checker.cause_aggregate import (
    UNKNOWN_CAUSE_AGGREGATE_SCHEMA,
    attach_cause_aggregate,
)
from scripts.function_tracer_pcode.checker.debug_trace import (
    AttemptIdentity,
    DebugTrace,
    ProofCompletionEvent,
    ReasonCausalTransition,
)
from scripts.function_tracer_pcode.checker.result import EquivalenceResult
from scripts.function_tracer_pcode.proof.obligations.shadow import LegacyExecutionSnapshot

# PR-128-A の fixture / 比較面をそのまま使う（重複実装しない）。
from scripts.function_tracer_pcode.tests.unit.test_issue128_cause_aggregate import (
    BIN1,
    BIN2,
    _attempt,
    _fixture_payloads,
    _occurrence_id,
    _reason,
    _reason_completion,
    _relational_cause,
    _reporting_surface,
    _requirement,
    _unary_cause,
    _without_trace,
)

REPO_ROOT = Path(__file__).resolve().parents[4]


# ---------------------------------------------------------------------------
# fixture: 中身の在る trace を持つ結果
# ---------------------------------------------------------------------------

def _rich_trace():
    """attempt / completion / transition を全部持つ trace（空 trace で誤魔化さない）。"""
    cause_x = _unary_cause("callsite-x")
    cause_z = _relational_cause("ret-z")
    r_x = _reason(
        "summary_effect_unmodeled", cause=cause_x, target="x",
        action_status="pending_proof", requirement_kinds=("effect_summary_completion",),
        pair_or_case=("case-l", "case-r"),
    )
    r_z = _reason(
        "return_width_bridge_missing", cause=cause_z, target="z", action_status="planned",
    )
    trace = DebugTrace(attempts=[
        _attempt(0, "pairwise", [r_x, r_z]),
        _attempt(1, "monolithic", [r_x]),
    ])
    trace.reason_completion_events.append(
        _reason_completion(
            r_z,
            occurrence_id=_occurrence_id("pairwise", 0, 1),
            at_attempt=AttemptIdentity("monolithic", 1),
            proof_kind="return_width_bridge",
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
    return trace, r_x


def _result(trace, reason, *, emit=True):
    result = EquivalenceResult(
        is_equivalent=None,
        function1_name="f",
        function2_name="f",
        binary1_name="left",
        binary2_name="right",
        solver_results=None,
        debug_trace=trace,
        unknown_reasons=[reason],
        binary1_content_identity=BIN1,
        binary2_content_identity=BIN2,
        emit_debug_trace=emit,
    )
    attach_cause_aggregate(result)
    return result


# ---------------------------------------------------------------------------
# 1. serialize の条件化
# ---------------------------------------------------------------------------

def _canonical(trace):
    from scripts.function_tracer_pcode.core.json_encoding import RESULT_JSON_POLICY

    return RESULT_JSON_POLICY.prepare(trace).value()


def test_to_dict_omits_debug_trace_unless_emit_flag():
    """既定（True）では従来どおり出て、False では **key だけ** が消える。"""
    trace, reason = _rich_trace()
    emitted = _result(trace, reason).to_dict()
    # 既定 True: 従来の出力そのまま。しかも emit 経路で内容を削っていない。
    # 出力は trace の canonical な表現（Issue #22 PR-22-D: 出力の準備が作る JSON 値）
    assert emitted["debug_trace"] == _canonical(trace)
    assert emitted["debug_trace"]["attempts"], "fixture が空 trace では条件化を測れない"

    trace2, reason2 = _rich_trace()
    withheld_result = _result(trace2, reason2, emit=False)
    withheld = withheld_result.to_dict()

    # (a) 消えるのは `debug_trace` key だけ。他の key は 1 つも変わらない。
    assert "debug_trace" not in withheld
    assert set(emitted) - set(withheld) == {"debug_trace"}
    assert {k: v for k, v in emitted.items() if k != "debug_trace"} == withheld

    # (b) object 上の trace は残る（生成停止ではない）。
    assert withheld_result.debug_trace is trace2
    assert trace2.to_dict() == trace.to_dict()

    # (c) aggregate は emit flag に関係なく常時出る。
    assert withheld["unknown_cause_aggregate"]["schema"] == UNKNOWN_CAUSE_AGGREGATE_SCHEMA
    assert withheld["unknown_cause_aggregate"] == emitted["unknown_cause_aggregate"]
    # `evidence_present.debug_trace` は「trace を観測できたか」。添付の有無で変えない。
    assert withheld["unknown_cause_aggregate"]["evidence_present"]["debug_trace"] is True


def test_emit_flag_default_keeps_direct_callers_unchanged():
    """直接生成する既存 caller（emit を渡さない）は従来どおり trace を出す。"""
    trace, reason = _rich_trace()
    result = EquivalenceResult(
        is_equivalent=None,
        function1_name="f",
        function2_name="f",
        binary1_name="left",
        binary2_name="right",
        solver_results=None,
        debug_trace=trace,
        unknown_reasons=[reason],
    )
    assert result.emit_debug_trace is True
    assert result.to_dict()["debug_trace"] == _canonical(trace)


def test_emit_flag_is_the_last_dataclass_field():
    """末尾追加であること（positional 互換）。

    Issue #22 PR-22-D が後ろに `prepared_semantic_payload` を足した。emit flag の
    位置は変わらず、その後ろにあるのは既定値付きの field だけ（positional で
    渡す既存の呼び出し側は影響を受けない）。
    """
    import dataclasses

    fields = dataclasses.fields(EquivalenceResult)
    names = [f.name for f in fields]
    position = names.index("emit_debug_trace")
    assert names[position + 1:] == ["prepared_semantic_payload"]
    assert all(
        f.default is not dataclasses.MISSING
        or f.default_factory is not dataclasses.MISSING
        for f in fields[position:]
    )


# ---------------------------------------------------------------------------
# 2. workflow が既存の debug 伝播から emit を決める
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("debug", [False, True])
def test_workflow_sets_emit_from_checker_debug(monkeypatch, debug):
    """`checker.debug` が emit を決める。新しい flag / env / config は読まない。"""
    from scripts.function_tracer_pcode.checker import workflow
    from scripts.function_tracer_pcode.checker.checker import EquivalenceChecker

    trace, reason = _rich_trace()
    planned = _result(trace, reason)
    # phase plan は走らせない（emit の決定だけを測る）。
    monkeypatch.setattr(workflow, "_run_phase_plan", lambda *a, **k: planned)

    # `--debug` / `-d` / `EQBENCH_DEBUG=1` はすべて CLI の `args.debug` へ集約され、
    # checker の `debug=` に入る。ここでもその同じ経路を使う。
    checker = EquivalenceChecker(
        strategy="monolithic", timeout=5, monolithic_timeout=5,
        canonical_decision_cutover=False, debug=debug,
    )
    assert checker.debug is debug

    returned = workflow.run_check_from_binaries(
        checker, object(), object(), "f", "f",
    )
    assert returned is planned
    assert returned.emit_debug_trace is debug
    assert ("debug_trace" in returned.to_dict()) is debug
    # どちらの場合も trace object は残る。
    assert returned.debug_trace is trace


def test_workflow_emits_for_a_checker_without_a_debug_attribute(monkeypatch):
    """`debug` を持たない checker stub でも落ちず、添付しない側へ倒れる。"""
    from scripts.function_tracer_pcode.checker import workflow

    trace, reason = _rich_trace()
    planned = _result(trace, reason)
    monkeypatch.setattr(workflow, "_run_phase_plan", lambda *a, **k: planned)

    class _NoDebug:
        pass

    returned = workflow.run_check_from_binaries(_NoDebug(), object(), object(), "f", "f")
    assert returned.emit_debug_trace is False


def test_workflow_still_attaches_phase_timings_when_setting_emit(monkeypatch):
    """emit の設定が既存の control flow（診断の添付・timeline の後片付け）を壊さない。"""
    from scripts.function_tracer_pcode.checker import workflow
    from scripts.function_tracer_pcode.checker.checker import EquivalenceChecker

    trace, reason = _rich_trace()
    planned = _result(trace, reason)
    monkeypatch.setattr(workflow, "_run_phase_plan", lambda *a, **k: planned)
    attached = []
    real_attach = workflow.attach_phase_timings
    monkeypatch.setattr(
        workflow,
        "attach_phase_timings",
        lambda result, timeline: (attached.append(result), real_attach(result, timeline))[1],
    )
    checker = EquivalenceChecker(
        strategy="monolithic", timeout=5, monolithic_timeout=5,
        canonical_decision_cutover=False, debug=False,
    )
    returned = workflow.run_check_from_binaries(checker, object(), object(), "f", "f")

    # emit を入れても既存の診断添付は 1 回そのまま走り、timeline は片付く。
    assert attached == [returned]
    assert returned.emit_debug_trace is False
    assert not hasattr(checker, "_phase_timeline")

    # 例外で抜けても timeline は片付き、result が無いときは emit を触らない。
    def _raise(*a, **k):
        raise RuntimeError("phase plan failed")

    monkeypatch.setattr(workflow, "_run_phase_plan", _raise)
    with pytest.raises(RuntimeError):
        workflow.run_check_from_binaries(checker, object(), object(), "f", "f")
    assert attached == [returned, None]
    assert not hasattr(checker, "_phase_timeline")


def test_debug_propagation_uses_the_existing_entry_points():
    """emit の入力は既存の debug 指定だけ。新しい flag / env を作っていない。"""
    from scripts.function_tracer_pcode.checker import workflow
    from scripts.function_tracer_pcode.cli import args as cli_args
    from scripts.function_tracer_pcode.cli.commands import equivalence

    # (1) `--debug` / `-d` は同じ CLI 引数。
    args_source = inspect.getsource(cli_args)
    assert '"--debug",' in args_source and '"-d",' in args_source
    # (2) CLI はそれを checker の `debug=` に渡す。
    assert "debug=args.debug," in inspect.getsource(equivalence.run_equivalence_check)
    # (3) runner は `EQBENCH_DEBUG=1` を CLI の `-d` に落とす（runner は変更していない）。
    debug_branch = re.compile(
        r'if \[\[ "\$EQBENCH_DEBUG" == "1" \]\]; then\s*\n?\s*\w+\+=\( -d \)'
    )
    for runner in ("eqbench_run_all_32jobs.sh", "neqbench_run_all_32jobs.sh"):
        source = (REPO_ROOT / runner).read_text(encoding="utf-8")
        assert debug_branch.search(source), runner
    # (4) workflow が読むのは `checker.debug` だけ。env / config は読まない。
    workflow_source = inspect.getsource(workflow.run_check_from_binaries)
    assert 'getattr(checker, "debug", False)' in workflow_source
    code_only = "\n".join(
        line for line in inspect.getsource(workflow).splitlines()
        if not line.lstrip().startswith("#")
    )
    for forbidden in ("environ", "getenv", "EQBENCH_DEBUG"):
        assert forbidden not in code_only, forbidden
    # config 層（tunable の読み出し）も引き込んでいない。
    assert "function_tracer_pcode.config" not in code_only


# ---------------------------------------------------------------------------
# 3. 生成停止ではない: object 読者が残る
# ---------------------------------------------------------------------------

def test_diagnostics_and_shadow_fingerprint_survive_without_emission():
    """serialize から trace を省いても object 読者の診断 / fingerprint が変わらない。"""
    trace_on, reason_on = _rich_trace()
    trace_off, reason_off = _rich_trace()
    emitting = _result(trace_on, reason_on)
    withholding = _result(trace_off, reason_off, emit=False)

    payload_on = emitting.to_dict()
    payload_off = withholding.to_dict()
    assert "debug_trace" in payload_on and "debug_trace" not in payload_off

    # (a) diagnostics payload は trace 由来の値を含めて同一。
    assert payload_off["diagnostics"] == payload_on["diagnostics"]

    # (b) attempts / completion / transition event は object 上に残っている。
    assert len(withholding.debug_trace.attempts) == len(trace_on.attempts) == 2
    assert withholding.debug_trace.proof_completion_events
    assert withholding.debug_trace.reason_completion_events
    assert withholding.debug_trace.causal_transitions

    # (c) `LegacyExecutionSnapshot`: trace 由来の fingerprint 入力（event_surface）と
    #     判定系の field は不変。`schema` だけは to_dict の key 集合そのものなので
    #     `debug_trace` の分だけ差が出る（= 宣言済みの serialization surface）。
    snap_on = LegacyExecutionSnapshot.from_result(emitting)
    snap_off = LegacyExecutionSnapshot.from_result(withholding)
    assert snap_off.proof_event_surface == snap_on.proof_event_surface
    assert snap_off.proof_action_surface == snap_on.proof_action_surface
    assert snap_off.unknown_reason_keys == snap_on.unknown_reason_keys
    assert snap_off.root_blocker_keys == snap_on.root_blocker_keys
    assert snap_off.decisiveness_surface == snap_on.decisiveness_surface
    assert snap_off.semantic_result == snap_on.semantic_result
    assert snap_off.legacy_timeout == snap_on.legacy_timeout
    assert snap_off.stage_path == snap_on.stage_path
    assert snap_off.decisive_counterexample == snap_on.decisive_counterexample
    assert set(snap_on.public_schema) - set(snap_off.public_schema) == {"debug_trace"}

    # (d) `to_string(show_phase_usage=True)` は従来どおり trace を読める。
    rendered = withholding.to_string(show_phase_usage=True)
    assert trace_off.format_phase_usage_summary() in rendered

    # (e) aggregate は同じ（trace を観測して作られている）。
    assert payload_off["unknown_cause_aggregate"] == payload_on["unknown_cause_aggregate"]
    assert payload_off["unknown_cause_aggregate"]["attempts"]["count"] == 2


def test_generation_is_not_stopped_in_the_workflow_source():
    """workflow / result のどこでも trace の生成・削除・pop を行っていない。"""
    from scripts.function_tracer_pcode.checker import result as result_module
    from scripts.function_tracer_pcode.checker import workflow

    workflow_source = inspect.getsource(workflow)
    # trace は常に作られ、常に結果へ添付される。
    assert "debug_trace = DebugTrace(" in workflow_source
    assert "result.debug_trace = debug_trace" in workflow_source
    for forbidden in (
        "result.debug_trace = None",
        "debug_trace.clear()",
        'pop("debug_trace"',
        "del result.debug_trace",
    ):
        assert forbidden not in workflow_source, forbidden

    result_source = inspect.getsource(result_module)
    assert 'pop("debug_trace"' not in result_source
    assert "self.debug_trace = None" not in result_source
    # Issue #22 PR-22-D: JSON の field 表は `checker.output_preparation` が持つ。
    # aggregate は条件化されていない（emit flag と別の行で常に出す）。trace は
    # object 上に在るものを、emit flag が真のときだけ添付する。
    from scripts.function_tracer_pcode.checker import output_preparation

    preparation_source = inspect.getsource(output_preparation)
    assert "self.debug_trace = None" not in preparation_source
    assert "result.debug_trace = None" not in preparation_source
    assert (
        'OutputField("unknown_cause_aggregate", _C, _unknown_cause_aggregate, _TRUNC)'
        in preparation_source
    )
    # 添付するかは準備時に 1 回だけ決める（`OutputOptions`）。合成は live な
    # flag を読まない。
    assert "if trace and o.include_debug_trace:" in preparation_source
    assert preparation_source.count("emit_debug_trace") == 1


# ---------------------------------------------------------------------------
# 4. reporting: 実際の serialization 経路が PR-128-A の oracle と一致する
# ---------------------------------------------------------------------------

def _round_trip(payloads):
    """実 log と同じく JSON を往復させる（tuple/list の差で一致しないことを防ぐ）。"""
    return [json.loads(json.dumps(payload, default=str)) for payload in copy.deepcopy(payloads)]


def test_unemitted_payloads_match_the_trace_removal_oracle():
    """emit=False の payload は「trace key を抜いた payload」と同じ reporting を出す。

    PR-128-A の lossless oracle が後者で成立しているので、これが成り立てば
    通常 run の reporting 情報は失われていない。
    """
    emitted = _fixture_payloads()
    withheld = _fixture_payloads(emit_debug_trace=False)

    # 非 vacuous であることの確認: 片方だけが trace を持つ。
    assert [p for p in emitted if "debug_trace" in p], "fixture に trace 付きが無い"
    assert not [p for p in withheld if "debug_trace" in p]
    assert len(emitted) == len(withheld) == 6

    # payload の差は `debug_trace` key だけ。
    for on, off in zip(emitted, withheld):
        assert set(on) - set(off) == {"debug_trace"}
        assert {k: v for k, v in on.items() if k != "debug_trace"} == off

    assert _reporting_surface(_round_trip(withheld)) == _reporting_surface(_without_trace(emitted))


def test_old_logs_with_full_trace_still_report_from_the_trace():
    """既存 log（trace 付き・aggregate 無し）は従来どおり trace から集計できる。"""
    emitted = _fixture_payloads()
    legacy_logs = []
    for payload in copy.deepcopy(emitted):
        payload.pop("unknown_cause_aggregate", None)
        legacy_logs.append(payload)
    surface = _reporting_surface(_round_trip(legacy_logs))
    # 「aggregate 無し -> unknown」に丸めていない（診断が観測済みとして出ている）。
    assert surface["reason_record_multiset"]
    # coverage は「1 件も観測できていない」なら None。trace から観測できている。
    assert surface["root_coverage"] is not None
    assert surface["root_coverage"]["evidence_state"] == "complete"
    assert surface["root_coverage"]["results_without_evidence"] == 0
    assert surface["root_active_count"] > 0
    # completion / transition も trace から観測できている（unknown へ落ちない）。
    for block in ("proof_completions", "reason_completions", "causal_transitions"):
        assert surface["causal_evidence"][block]["total"] > 0, block


# ---------------------------------------------------------------------------
# 5. canonical 契約: trace 無しで validate / replay、semantic は不変
# ---------------------------------------------------------------------------

def _finalization_env(tmp_path, monkeypatch):
    bundle_key = tmp_path / "canonical-bundle.key"
    bundle_key.write_bytes(b"k" * 32)
    monkeypatch.setenv("UNKNOWN_TAXONOMY_V2_SUPERVISOR_KEY_ID", "issue128b-test-key")
    monkeypatch.setenv("UNKNOWN_TAXONOMY_V2_SUPERVISOR_KEY_FILE", str(bundle_key))
    monkeypatch.setenv(
        "UNKNOWN_TAXONOMY_V2_RESULT_ENTRY_OCCURRENCE_NONCE", "issue128b-occurrence"
    )


def _emit_variants():
    """同じ入力から emit True / False の payload を独立に作る。"""
    trace_on, reason_on = _rich_trace()
    trace_off, reason_off = _rich_trace()
    return (
        _result(trace_on, reason_on).to_dict(),
        _result(trace_off, reason_off, emit=False).to_dict(),
    )


def test_canonical_result_validates_and_replays_without_debug_trace(tmp_path, monkeypatch):
    """`debug_trace` key の無い payload でも bundle の validate / replay が成立する。"""
    from scripts.function_tracer_pcode.authority.decision.canonical_result import (
        validate_canonical_result_finalization_bundle,
    )
    from scripts.function_tracer_pcode.tests.unit._finalization_support import (
        _independent_finalization,
    )

    _finalization_env(tmp_path, monkeypatch)
    _, payload_without = _emit_variants()
    assert "debug_trace" not in payload_without
    assert payload_without["unknown_cause_aggregate"]["evidence_present"]["debug_trace"] is True

    bundle, _, _ = _independent_finalization(
        tmp_path, monkeypatch,
        case_id="issue128b-without-trace", result_payload_preimage=payload_without,
    )
    validated = validate_canonical_result_finalization_bundle(
        bundle,
        result_payload_preimage=payload_without,
        bundle_verification_key_id="issue128b-test-key",
        bundle_verification_key=b"k" * 32,
    )
    assert validated["outcome"] == "EQUIVALENT"


def test_omitting_debug_trace_changes_preimage_but_no_semantic_field(tmp_path, monkeypatch):
    """独立 finalization 2 本: preimage digest は変わるが semantic は 1 field も変わらない。"""
    from scripts.function_tracer_pcode.authority.decision.canonical_result import (
        validate_canonical_result_finalization_bundle,
    )
    from scripts.function_tracer_pcode.tests.unit._finalization_support import (
        _independent_finalization,
    )

    _finalization_env(tmp_path, monkeypatch)
    payload_with, payload_without = _emit_variants()
    assert payload_with != payload_without
    assert {k: v for k, v in payload_with.items() if k != "debug_trace"} == payload_without

    bundle_with, session_a, evidence_a = _independent_finalization(
        tmp_path, monkeypatch,
        case_id="issue128b-with-trace", result_payload_preimage=payload_with,
    )
    bundle_without, session_b, evidence_b = _independent_finalization(
        tmp_path, monkeypatch,
        case_id="issue128b-without-trace", result_payload_preimage=payload_without,
    )
    # 2 本は独立（片方を加工して他方を作っていない）。
    assert session_a is not session_b
    assert evidence_a is not evidence_b
    assert evidence_a.pilot_result is not evidence_b.pilot_result
    assert bundle_with is not bundle_without

    for bundle, preimage in ((bundle_with, payload_with), (bundle_without, payload_without)):
        validated = validate_canonical_result_finalization_bundle(
            bundle,
            result_payload_preimage=preimage,
            bundle_verification_key_id="issue128b-test-key",
            bundle_verification_key=b"k" * 32,
        )
        assert validated["outcome"] == "EQUIVALENT"

    # serialization surface が変わるので preimage digest は変わる（意図どおり）。
    # これ自体を semantic 変更の根拠にはしない。
    assert (
        bundle_with["canonical_result_payload_preimage_digest"]
        != bundle_without["canonical_result_payload_preimage_digest"]
    )
    projection_with = bundle_with["canonical_semantic_result_projection"]
    projection_without = bundle_without["canonical_semantic_result_projection"]
    assert projection_without["payload"] == projection_with["payload"]
    assert (
        projection_without["semantic_projection_digest"]
        == projection_with["semantic_projection_digest"]
    )
    assert "debug_trace" not in projection_with["payload"]


def test_semantic_surface_of_the_payload_is_unchanged_by_emission():
    """判定・reason・診断の semantic field が emit の有無で 1 つも変わらない。"""
    payload_with, payload_without = _emit_variants()
    for name in (
        "is_equivalent",
        "unknown_reasons",
        "unknown_recovery_actions",
        "unknown_recovery_backlog",
        "decision_gated_by_pending_proof",
        "error_message",
        "failure_status",
        "stage_path",
        "c_active_base",
        "q_open_base",
        "diagnostics",
        "unknown_cause_aggregate",
    ):
        assert payload_without[name] == payload_with[name], name

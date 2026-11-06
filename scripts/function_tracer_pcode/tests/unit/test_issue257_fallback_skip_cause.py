# -*- coding: utf-8 -*-
"""Issue #257: monolithic fallback を止めた比較は、止めた理由に対応する authority の cause で UNKNOWN になる。

制御フローが不完全で戻り値が未解決の側があると runner は fallback を止める。その比較の UNKNOWN を説明する cause が
無く、終了処理（``InconclusiveComparisonAuthority``）が ERROR にしていた（Neq 正式評価 4285315a の tcas 108 件）。
止める理由と cause の owner の対応は ``return_coverage.MONOLITHIC_FALLBACK_SKIP_CAUSE_OWNERS`` の 1 つの表。
"""

from __future__ import annotations

from types import SimpleNamespace

import pytest

from scripts.function_tracer_pcode.authority.domains import return_coverage as domain
from scripts.function_tracer_pcode.authority.domains.return_coverage import (
    MONOLITHIC_FALLBACK_SKIP_CAUSE_OWNERS,
    OUTCOME_PARTITION_STAGE_OWNER,
    RETURN_COVERAGE_DOMAIN_REASON_IDS,
    RETURN_COVERAGE_GAP_REASON_ID,
    RETURN_PARTITION_CONTROL_FLOW_REASON_ID,
)
from scripts.function_tracer_pcode.core import Expression, ReturnInfo
from scripts.function_tracer_pcode.core.analysis import (
    FALLBACK_SKIP_INCOMPLETE_CONTROL_FLOW,
    FALLBACK_SKIP_RETURN_COVERAGE_GAP,
    MONOLITHIC_FALLBACK_SKIP_REASONS,
)
from scripts.function_tracer_pcode.proof.obligations import stage_runner


def _int_param():
    return Expression.parameter("param_1", 0, data_type="int", size=4)


def _template(name: str, shape: str):
    """``cf``: 制御フローが不完全で戻り値が未解決（#257 (a)）。``full``: ``x`` を返す完全な解析。"""

    from scripts.function_tracer_pcode.tests.unit.test_issue185_type_hypothesis_domain import _analysis, _descriptor

    if shape == "cf":
        analysis = _analysis(
            name, [_descriptor("param_1", 4, "int", True)],
            [ReturnInfo("0x10", Expression.unknown("unresolved_ret"), [])],
        )
        analysis.incomplete_control_flow = True
        return analysis
    return _analysis(name, [_descriptor("param_1", 4, "int", True)], [ReturnInfo("0x10", _int_param(), [])])


def _active(result: dict) -> list:
    return sorted(str(row.get("reason_id")) for row in result.get("c_active_base") or ())


# ---------------------------------------------------------------------------
# 表: 止める理由ごとに cause の owner がある（AC 3）
# ---------------------------------------------------------------------------


def test_every_fallback_skip_reason_has_a_cause_owner():
    assert set(MONOLITHIC_FALLBACK_SKIP_CAUSE_OWNERS) == set(MONOLITHIC_FALLBACK_SKIP_REASONS)
    for owner in MONOLITHIC_FALLBACK_SKIP_CAUSE_OWNERS.values():
        assert owner == OUTCOME_PARTITION_STAGE_OWNER or owner in RETURN_COVERAGE_DOMAIN_REASON_IDS


def test_the_skip_predicate_is_the_presence_of_a_skip_reason():
    complete = _template("l", "full")
    assert complete.monolithic_fallback_skip_reasons() == ()
    assert not complete.should_skip_monolithic_fallback()

    incomplete = _template("l", "cf")
    assert incomplete.monolithic_fallback_skip_reasons() == (FALLBACK_SKIP_INCOMPLETE_CONTROL_FLOW,)
    assert incomplete.should_skip_monolithic_fallback()

    incomplete.analysis_notes.append(FALLBACK_SKIP_RETURN_COVERAGE_GAP)
    assert incomplete.monolithic_fallback_skip_reasons() == (
        FALLBACK_SKIP_RETURN_COVERAGE_GAP, FALLBACK_SKIP_INCOMPLETE_CONTROL_FLOW,
    )

    recovered = _template("l", "cf")
    recovered.recovered_from_decompiler = True
    assert recovered.monolithic_fallback_skip_reasons() == ()


def test_the_new_reason_is_a_sealed_relational_equivalence_blocker_of_the_domain():
    from scripts.function_tracer_pcode.authority.lifecycle.pilot import PILOT_TYPED_CAUSE_KINDS
    from scripts.function_tracer_pcode.authority.process.supervisor import PROCESS_DURABLE_REASON_REGISTRY

    definition = domain.RETURN_COVERAGE_REASON_REGISTRY.get(RETURN_PARTITION_CONTROL_FLOW_REASON_ID)
    assert definition.decision_effect == "blocks_equivalence"
    assert definition.domain == "return_coverage"
    assert RETURN_PARTITION_CONTROL_FLOW_REASON_ID in PILOT_TYPED_CAUSE_KINDS
    assert PROCESS_DURABLE_REASON_REGISTRY.get(RETURN_PARTITION_CONTROL_FLOW_REASON_ID).domain == "return_coverage"


# ---------------------------------------------------------------------------
# 記録: runner は止めた理由から、runner の raw pair の比較の観測として記録する
# ---------------------------------------------------------------------------


_RAW = ("raw-pair", "S_PAIRWISE", "1")


def test_the_control_flow_observation_names_the_incomplete_side():
    observations = domain.control_flow_skip_observations(_template("l", "full"), _template("r", "cf"))
    assert [(item.label, item.reason_id) for item in observations] == [
        ("function2", RETURN_PARTITION_CONTROL_FLOW_REASON_ID),
    ]


def test_the_runner_prefers_the_coverage_verdict_and_falls_back_to_the_control_flow_reason():
    coverage = SimpleNamespace(coverage_verdict=(_RAW, (("function1", RETURN_COVERAGE_GAP_REASON_ID),)))
    seedless = lambda name, shape: _template(name, shape)  # noqa: E731  (_analysis は seed を持たない)
    ((observed, observations),) = stage_runner._skipped_fallback_observations(
        coverage, _RAW, seedless("l", "cf"), seedless("r", "cf"),
    )
    assert [item.reason_id for item in observations] == [RETURN_COVERAGE_GAP_REASON_ID]

    nothing_judged = SimpleNamespace(coverage_verdict=None)
    ((observed, observations),) = stage_runner._skipped_fallback_observations(
        nothing_judged, _RAW, seedless("l", "cf"), seedless("r", "full"),
    )
    assert observed == _RAW
    assert [(item.label, item.reason_id) for item in observations] == [
        ("function1", RETURN_PARTITION_CONTROL_FLOW_REASON_ID),
    ]


def test_the_runner_records_nothing_without_its_raw_comparison():
    assert stage_runner._skipped_fallback_observations(
        SimpleNamespace(coverage_verdict=None), (), _template("l", "cf"), _template("r", "cf"),
    ) == []


# ---------------------------------------------------------------------------
# production: 本物の checker（AC 1・2）
# ---------------------------------------------------------------------------


def test_a_comparison_whose_fallback_stopped_on_incomplete_control_flow_is_a_reasoned_unknown():
    """#257 (a): seed の無い raw pair、制御フローが不完全で戻り値が未解決。main 4285315a では ERROR
    （``inconclusive comparison receipt join is not canonical``）。"""

    from scripts.function_tracer_pcode.tests.unit._production_check_harness import run_production_check

    result = run_production_check("issue257-a", _template("l", "cf"), _template("r", "cf"))

    assert result["final_outcome"] == "UNKNOWN", (result.get("failure_message"), _active(result))
    assert _active(result) == [RETURN_PARTITION_CONTROL_FLOW_REASON_ID] * 2


def _run_with_a_p1_reanalysis(monkeypatch, case_id: str, p0: tuple, p1: tuple) -> dict:
    """P0 は ``p0`` の形、P1 は両側を再解析させて ``p1`` の形の解析を返す。"""

    from scripts.function_tracer_pcode.checker.phases import handler
    from scripts.function_tracer_pcode.tests.unit._analyzer_pipeline_harness import analyze_through_pipeline
    from scripts.function_tracer_pcode.tests.unit._production_check_harness import run_production_check

    shapes = {"l": (p0[0], p1[0]), "r": (p0[1], p1[1])}
    calls = {"l": 0, "r": 0}

    def analyze(template):
        name = template.function_name
        calls[name] += 1
        analysis = analyze_through_pipeline(_template(name, shapes[name][0 if calls[name] == 1 else 1]))
        if shapes[name][0 if calls[name] == 1 else 1] == "cf":
            analysis.incomplete_control_flow = True
        return analysis

    def execute_phase(self, spec, _ctx, *_args, **_kwargs):
        if spec.phase_id == handler.PhaseID.P1_SIGNEDNESS:
            return handler.PhaseResult(
                spec.phase_id, applied=True, retry_name="p1-reanalysis",
                changed_binary1=True, changed_binary2=True,
            )
        return handler.PhaseResult(spec.phase_id, applied=False, retry_name="none")

    monkeypatch.setattr(handler.PhaseHandler, "execute_phase", execute_phase)
    result = run_production_check(case_id, _template("l", p0[0]), _template("r", p0[1]), analyze=analyze)
    assert calls == {"l": 2, "r": 2}, calls
    return result


@pytest.mark.parametrize(
    "case_id, p1, outcome, active",
    (
        # P1 の再解析で不完全さが解消し、本物の比較が EQ を示す: 前の段の記録は最終の EQ を止めない（AC 2）。
        ("p1-recovered", ("full", "full"), "EQUIVALENT", []),
        # P1 でも不完全なまま: 最終の比較（P1）の cause が UNKNOWN を保つ。
        ("p1-still-incomplete", ("cf", "cf"), "UNKNOWN", [RETURN_PARTITION_CONTROL_FLOW_REASON_ID] * 2),
        # 片側だけ回復: 回復しなかった側の cause だけが残る。
        ("p1-one-side-recovered", ("full", "cf"), "UNKNOWN", [RETURN_PARTITION_CONTROL_FLOW_REASON_ID]),
    ),
)
def test_a_retry_phase_adopts_only_the_record_of_its_own_comparison(monkeypatch, case_id, p1, outcome, active):
    result = _run_with_a_p1_reanalysis(monkeypatch, "issue257-" + case_id, ("cf", "cf"), p1)

    assert result["final_outcome"] == outcome, (result.get("failure_message"), _active(result))
    assert _active(result) == active

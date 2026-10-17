# -*- coding: utf-8 -*-
"""plan v4 PR-C: 最終の比較が seed の無い解析の被覆の欠けで終わったときだけ、``return_coverage`` の cause にする。

責務は 3 つに分かれ、それぞれをここで固定する。

* 判定: return-coverage gate（この file の対象外）が raw analysis に被覆の印を残す。
* 記録: runner が monolithic fallback を止めたとき、seed の無い側の印を ``UnsealedCoverageObservation`` にし、
  runner の結果の比較（dispatch frame）に束縛した ``UnsealedCoverageTerminal`` を結果に付ける（cause にしない）。
* 採用: authority の終了処理が、最終の結果の記録だけを、最終の比較の frame と照合して cause にする
  （``observe_final_unsealed_coverage``）。

production（本物の checker）で、型の再試行の段が被覆を回復したら EQ を採用し、回復しなければ UNKNOWN を保つ
（review: P0 の cause が P1 の EQ を塞いだ反例）。cause の identity は比較（raw pair・comparison receipt）を含み、
別の比較の同じ関数の不足は別の cause。
"""

from __future__ import annotations

from types import SimpleNamespace
from typing import Any, List

import pytest

from scripts.function_tracer_pcode.authority.contracts import IdentityScope
from scripts.function_tracer_pcode.authority.domains import return_coverage as domain
from scripts.function_tracer_pcode.authority.domains.return_coverage import (
    RETURN_COVERAGE_GAP_REASON_ID,
    RETURN_COVERAGE_IDENTITY_SCOPE,
    RETURN_COVERAGE_INCONCLUSIVE_REASON_ID,
    RETURN_COVERAGE_REASON_IDS,
    RETURN_COVERAGE_REASON_REGISTRY,
    RETURN_COVERAGE_SITE_ID,
    ReturnCoverageBlockerSignal,
    ReturnCoveragePilotEncoder,
    UnsealedCoverageObservation,
    UnsealedCoverageTerminal,
    observe_final_unsealed_coverage,
    unsealed_coverage_observations,
)
from scripts.function_tracer_pcode.proof.obligations import stage_runner


_IDENTITY = ("function_identity_v1", "bin-f", None, "0x1000")
_COMPARISON = ("raw-pair-a", "S_PAIRWISE", "1")


def _signal(reason_id: str = RETURN_COVERAGE_GAP_REASON_ID, identity: Any = _IDENTITY,
            comparison: tuple = _COMPARISON) -> ReturnCoverageBlockerSignal:
    return ReturnCoverageBlockerSignal(
        declared_reason_id=reason_id, function_identity=identity, coverage_check="return_case_coverage_gap",
        comparison_identity=comparison, evidence_refs=("coverage_label:function1",),
    )


# ---------------------------------------------------------------------------
# domain
# ---------------------------------------------------------------------------


def test_the_two_reasons_are_sealed_relational_equivalence_blockers():
    definitions = {item.reason_id: item for item in RETURN_COVERAGE_REASON_REGISTRY.snapshot()}
    assert set(definitions) == {RETURN_COVERAGE_GAP_REASON_ID, RETURN_COVERAGE_INCONCLUSIVE_REASON_ID}
    for definition in definitions.values():
        assert definition.decision_effect == "blocks_equivalence"
        assert definition.domain == "return_coverage"
    assert RETURN_COVERAGE_IDENTITY_SCOPE is IdentityScope.RELATIONAL


def test_the_reasons_are_registered_where_the_authority_reads_them():
    from scripts.function_tracer_pcode.authority.lifecycle.pilot import PILOT_TYPED_CAUSE_KINDS
    from scripts.function_tracer_pcode.authority.process.supervisor import PROCESS_DURABLE_REASON_REGISTRY

    for reason_id in RETURN_COVERAGE_REASON_IDS:
        assert reason_id in PILOT_TYPED_CAUSE_KINDS
        assert PROCESS_DURABLE_REASON_REGISTRY.get(reason_id).domain == "return_coverage"


def test_the_producer_site_is_the_final_terminal_adoption_in_the_tracked_manifest():
    import json
    from pathlib import Path

    manifest = json.loads(
        (Path(__file__).resolve().parents[4] / "artifacts/unknown_taxonomy_v2/phase7/producer-sites.json").read_text()
    )
    (site,) = [item for item in manifest["sites"] if item["producer_site_manifest_id"] == RETURN_COVERAGE_SITE_ID]
    assert site["enclosing_function"] == "observe_final_unsealed_coverage"
    assert site["path"].endswith("authority/domains/return_coverage.py")
    assert sorted(
        reason for slot in site["expected_cause_slots"] for reason in slot["allowed_reason_ids"]
    ) == sorted(RETURN_COVERAGE_REASON_IDS)
    assert {slot["expected_identity_scope"] for slot in site["expected_cause_slots"]} == {"RELATIONAL"}


def test_a_signal_refuses_a_foreign_reason_and_an_unbound_comparison():
    with pytest.raises(ValueError):
        _signal("outcome_cfg_reachability_unproven")
    with pytest.raises(TypeError):
        _signal(comparison=())
    with pytest.raises(TypeError):
        ReturnCoverageBlockerSignal(
            declared_reason_id=RETURN_COVERAGE_GAP_REASON_ID, function_identity=_IDENTITY, coverage_check="",
            comparison_identity=_COMPARISON,
        )


class _Session:
    def __init__(self) -> None:
        self.domain_signal_state = {}
        self.identity = SimpleNamespace(
            result_occurrence_id="occ-1", source_snapshot_fingerprint="fp", execution_identity_digest="d" * 64,
        )


def test_the_encoder_observes_one_cause_per_comparison_side_and_reason():
    encoder = ReturnCoveragePilotEncoder()
    session = _Session()

    first = encoder(session, _signal())
    assert len(first) == 1
    encoder.commit_emitted_signal(session, _signal(), first)

    assert encoder.has_observed(session, _signal())
    assert encoder(session, _signal()) == ()
    # 別の reason・別の関数・別の比較（同じ関数でも）は別の cause。
    assert len(encoder(session, _signal(RETURN_COVERAGE_INCONCLUSIVE_REASON_ID))) == 1
    assert len(encoder(session, _signal(identity=("function_identity_v1", "bin-g", None, "0x2000")))) == 1
    other = ("raw-pair-b", "S_PAIRWISE", "1")
    assert not encoder.has_observed(session, _signal(comparison=other))
    assert (
        encoder.authority_for_signal(session, _signal()).occurrence.occurrence_id
        != encoder.authority_for_signal(session, _signal(comparison=other)).occurrence.occurrence_id
    )


def test_the_cause_carries_the_domain_reason_and_relational_scope():
    occurrence = ReturnCoveragePilotEncoder().authority_for_signal(_Session(), _signal()).occurrence
    assert occurrence.reason_id == RETURN_COVERAGE_GAP_REASON_ID
    assert occurrence.identity_scope is IdentityScope.RELATIONAL


# ---------------------------------------------------------------------------
# 記録: どの側の不足か（seed の無い側の印だけ）
# ---------------------------------------------------------------------------


def _analysis(*, seeded: bool, notes=(), identity=_IDENTITY) -> Any:
    return SimpleNamespace(
        outcome_seed=object() if seeded else None,
        analysis_notes=list(notes),
        outcome_function_identity=lambda: identity,
    )


def test_observations_are_the_seedless_sides_coverage_notes():
    both = ("return_case_coverage_gap", "return_case_coverage_inconclusive")
    observed = unsealed_coverage_observations(
        _analysis(seeded=False, notes=both), _analysis(seeded=False, notes=both[:1], identity=("right",)),
    )
    assert [(item.label, item.reason_id, item.function_identity) for item in observed] == [
        ("function1", RETURN_COVERAGE_GAP_REASON_ID, _IDENTITY),
        ("function1", RETURN_COVERAGE_INCONCLUSIVE_REASON_ID, _IDENTITY),
        ("function2", RETURN_COVERAGE_GAP_REASON_ID, ("right",)),
    ]


def test_a_seeded_side_or_a_side_without_a_note_is_not_observed():
    assert unsealed_coverage_observations(
        _analysis(seeded=True, notes=("return_case_coverage_gap",)),
        _analysis(seeded=False, notes=("bounded_call_refinement",)),
    ) == ()


def test_the_coverage_notes_are_the_registered_comparison_annotations():
    from scripts.function_tracer_pcode.proof.obligations.snapshot import COMPARISON_ANNOTATION_NOTES

    assert {note for note, _reason in domain.COVERAGE_NOTE_REASONS} == set(COMPARISON_ANNOTATION_NOTES)
    assert tuple(reason for _note, reason in domain.COVERAGE_NOTE_REASONS) == RETURN_COVERAGE_REASON_IDS


# ---------------------------------------------------------------------------
# 記録の束縛と採用
# ---------------------------------------------------------------------------


def _frame(raw_pair: Any = "raw-pair-a", branch: Any = "S_PAIRWISE", generation: Any = 1) -> Any:
    return SimpleNamespace(
        comparison_binding=SimpleNamespace(raw_pair_digest=raw_pair), branch_id=branch, generation=generation,
    )


def _observation(label: str = "function1") -> UnsealedCoverageObservation:
    return UnsealedCoverageObservation(label, RETURN_COVERAGE_GAP_REASON_ID, "return_case_coverage_gap", _IDENTITY)


def test_a_terminal_binds_only_the_comparison_it_was_issued_for():
    frame = _frame()
    terminal = UnsealedCoverageTerminal.issue(frame, (_observation(),))

    assert terminal.binds(frame)
    assert not terminal.binds(None)
    assert not terminal.binds(_frame())  # 同じ値の別の比較の frame
    frame.generation = 2  # 同じ frame の比較が変わった
    assert not terminal.binds(frame)


@pytest.mark.parametrize(
    "frame", (_frame(raw_pair=None), _frame(branch=""), _frame(generation="1"), SimpleNamespace()),
    ids=("no-raw-pair", "no-branch", "inexact-generation", "not-a-frame"),
)
def test_a_terminal_needs_a_comparison_identity(frame):
    with pytest.raises(ValueError):
        UnsealedCoverageTerminal.issue(frame, (_observation(),))


def test_a_terminal_needs_observations():
    with pytest.raises(ValueError):
        UnsealedCoverageTerminal.issue(_frame(), ())


def test_the_signals_are_bound_to_the_terminal_comparison():
    (signal,) = UnsealedCoverageTerminal.issue(_frame(), (_observation(),)).signals()
    assert signal.comparison_identity == ("raw-pair-a", "S_PAIRWISE", "1")
    assert signal.declared_reason_id == RETURN_COVERAGE_GAP_REASON_ID
    assert signal.evidence_refs == ("coverage_label:function1", "monolithic_fallback_skipped")


@pytest.fixture
def emitted(monkeypatch):
    from scripts.function_tracer_pcode.authority.lifecycle import production_signals

    signals: List[Any] = []

    def emit(signal, *, producer_site_manifest_id=None):
        assert producer_site_manifest_id == RETURN_COVERAGE_SITE_ID
        signals.append(signal)
        return 1

    monkeypatch.setattr(production_signals, "emit_return_coverage_signal", emit)
    return signals


def test_adoption_emits_the_final_comparisons_record(emitted):
    frame = _frame()
    terminal = UnsealedCoverageTerminal.issue(frame, (_observation("function1"), _observation("function2")))

    assert observe_final_unsealed_coverage(terminal, frame) == 2
    assert [item.comparison_identity for item in emitted] == [("raw-pair-a", "S_PAIRWISE", "1")] * 2


def test_adoption_refuses_a_record_of_another_comparison(emitted):
    terminal = UnsealedCoverageTerminal.issue(_frame(), (_observation(),))

    with pytest.raises(ValueError):
        observe_final_unsealed_coverage(terminal, _frame())
    with pytest.raises(ValueError):
        observe_final_unsealed_coverage(object(), _frame())
    assert emitted == []


def test_the_runner_attaches_the_record_to_its_result_and_emits_nothing(emitted):
    result = SimpleNamespace(_prepared_dispatch_frame=_frame())

    stage_runner._attach_unsealed_coverage_terminal(result, (_observation(),))

    assert type(result._unsealed_coverage_terminal) is UnsealedCoverageTerminal
    assert result._unsealed_coverage_terminal.binds(result._prepared_dispatch_frame)
    assert emitted == []


def test_the_runner_records_nothing_without_a_comparison_frame():
    result = SimpleNamespace(_prepared_dispatch_frame=None)
    stage_runner._attach_unsealed_coverage_terminal(result, (_observation(),))
    assert not hasattr(result, "_unsealed_coverage_terminal")


def test_the_runner_records_nothing_without_observations():
    result = SimpleNamespace(_prepared_dispatch_frame=_frame())
    stage_runner._attach_unsealed_coverage_terminal(result, ())
    assert not hasattr(result, "_unsealed_coverage_terminal")


# ---------------------------------------------------------------------------
# production: 型の再試行の段（P1）が被覆を回復したら EQ、回復しなければ UNKNOWN
# ---------------------------------------------------------------------------


def _int_param():
    from scripts.function_tracer_pcode.core import Expression

    return Expression.parameter("param_1", 0, data_type="int", size=4)


def _positive(negated: bool = False):
    from scripts.function_tracer_pcode.core import Condition, Expression

    return Condition(Expression.binary_op("INT_SLESS", Expression.constant(0, 4), _int_param()), negated)


def _indirect_guard(negated: bool = False):
    from scripts.function_tracer_pcode.core import Condition, Expression
    from scripts.function_tracer_pcode.tests.unit.test_stack_protector_conditions_kept import _indirect_read

    return Condition(Expression.binary_op("INT_NOTEQUAL", _indirect_read(), _int_param()), negated)


def _template(name: str, shape: str):
    """``x > 0`` だけ ``x`` を返す（partial）、``x <= 0`` は 0 も返す（full）、条件に INDIRECT（inconclusive）。"""

    from scripts.function_tracer_pcode.core import Expression, ReturnInfo
    from scripts.function_tracer_pcode.tests.unit.test_issue185_type_hypothesis_domain import _analysis, _descriptor

    returns = {
        "partial": lambda: [ReturnInfo("0x10", _int_param(), [_positive()])],
        "full": lambda: [
            ReturnInfo("0x10", _int_param(), [_positive()]),
            ReturnInfo("0x20", Expression.constant(0, 4), [_positive(True)]),
        ],
        "inconclusive": lambda: [
            ReturnInfo("0x10", _int_param(), [_indirect_guard()]),
            ReturnInfo("0x20", Expression.constant(0, 4), [_indirect_guard(True)]),
        ],
    }[shape]()
    return _analysis(name, [_descriptor("param_1", 4, "int", True)], returns)


def _run_with_a_p1_reanalysis(monkeypatch, case_id: str, p0: tuple, p1: tuple) -> dict:
    """P0 は ``p0`` の形、P1 の再解析（両側とも変更ありとして再解析させる）は ``p1`` の形の解析を返す。"""

    from scripts.function_tracer_pcode.checker.phases import handler
    from scripts.function_tracer_pcode.tests.unit._analyzer_pipeline_harness import analyze_through_pipeline
    from scripts.function_tracer_pcode.tests.unit._production_check_harness import run_production_check

    shapes = {"l": (p0[0], p1[0]), "r": (p0[1], p1[1])}
    calls = {"l": 0, "r": 0}

    def analyze(template):
        name = template.function_name
        calls[name] += 1
        return analyze_through_pipeline(_template(name, shapes[name][0 if calls[name] == 1 else 1]))

    def execute_phase(self, spec, _ctx, *_args, **_kwargs):
        if spec.phase_id == handler.PhaseID.P1_SIGNEDNESS:
            return handler.PhaseResult(
                spec.phase_id, applied=True, retry_name="p1-reanalysis", changed_binary1=True, changed_binary2=True,
            )
        return handler.PhaseResult(spec.phase_id, applied=False, retry_name="none")

    monkeypatch.setattr(handler.PhaseHandler, "execute_phase", execute_phase)
    result = run_production_check(case_id, _template("l", p0[0]), _template("r", p0[1]), analyze=analyze)
    assert calls == {"l": 2, "r": 2}, calls
    assert result.get("retry_count") == 1
    return result


def _active(result: dict) -> list:
    return sorted(str(row.get("reason_id")) for row in result.get("c_active_base") or ())


@pytest.mark.parametrize(
    "case_id, p0, p1, outcome, active",
    (
        # review の反例: P0 は両側 partial（gap）、P1 は両側 full。P1 の本物の比較が EQ を示す。
        ("p0-gap-p1-recovered", ("partial", "partial"), ("full", "full"), "EQUIVALENT", []),
        # P0 は条件を SMT へ訳せない（inconclusive）、P1 は訳せる full。
        ("p0-inconclusive-p1-recovered", ("inconclusive", "inconclusive"), ("full", "full"), "EQUIVALENT", []),
        # P1 でも不足が残る（同じ不足の再観測）: 最終の比較（P1）の cause が UNKNOWN を保つ。
        ("p1-still-partial", ("partial", "partial"), ("partial", "partial"), "UNKNOWN",
         [RETURN_COVERAGE_GAP_REASON_ID] * 2),
        # 片側だけ回復: 回復しなかった側の cause だけが残る。
        ("p1-one-side-recovered", ("partial", "partial"), ("full", "partial"), "UNKNOWN",
         [RETURN_COVERAGE_GAP_REASON_ID]),
        # P1 で inconclusive に変わる: 最終の比較の不足（inconclusive）だけが cause。
        ("p1-turns-inconclusive", ("partial", "partial"), ("inconclusive", "inconclusive"), "UNKNOWN",
         [RETURN_COVERAGE_INCONCLUSIVE_REASON_ID] * 2),
    ),
    ids=lambda value: value if isinstance(value, str) and value.startswith("p") else None,
)
def test_a_retry_phase_adopts_the_coverage_of_its_own_comparison(monkeypatch, case_id, p0, p1, outcome, active):
    result = _run_with_a_p1_reanalysis(monkeypatch, "pr-c-" + case_id, p0, p1)

    assert result["final_outcome"] == outcome, (result.get("error_message"), result.get("failure_message"), _active(result))
    assert _active(result) == active


# ---------------------------------------------------------------------------
# 採用の規則: 最終の結果が判定を持たないときだけ
# ---------------------------------------------------------------------------


@pytest.mark.parametrize(
    "outcome, adopted",
    (("UNKNOWN", 1), ("TIMEOUT", 1), ("ERROR", 0), ("EQUIVALENT", 0), ("NOT_EQ", 0)),
)
def test_only_an_undecided_final_result_adopts_its_record(emitted, outcome, adopted):
    from scripts.function_tracer_pcode.authority.contracts import Outcome
    from scripts.function_tracer_pcode.authority.domains.return_coverage import adopt_final_unsealed_coverage

    frame = _frame()
    result = SimpleNamespace(_prepared_dispatch_frame=frame)
    stage_runner._attach_unsealed_coverage_terminal(result, (_observation(),))

    assert adopt_final_unsealed_coverage(result, Outcome(outcome)) == adopted
    assert len(emitted) == adopted


def test_a_final_result_without_a_record_adopts_nothing(emitted):
    from scripts.function_tracer_pcode.authority.contracts import Outcome
    from scripts.function_tracer_pcode.authority.domains.return_coverage import adopt_final_unsealed_coverage

    assert adopt_final_unsealed_coverage(SimpleNamespace(_prepared_dispatch_frame=_frame()), Outcome.UNKNOWN) == 0
    assert emitted == []


def test_a_record_moved_onto_another_final_result_is_refused(emitted):
    """記録は作った比較の frame にしか使えない（別の結果へ写しても最終の判定に使わない）。"""

    from scripts.function_tracer_pcode.authority.contracts import Outcome
    from scripts.function_tracer_pcode.authority.domains.return_coverage import adopt_final_unsealed_coverage

    earlier = SimpleNamespace(_prepared_dispatch_frame=_frame())
    stage_runner._attach_unsealed_coverage_terminal(earlier, (_observation(),))
    final = SimpleNamespace(
        _prepared_dispatch_frame=_frame(raw_pair="raw-pair-p1"),
        _unsealed_coverage_terminal=earlier._unsealed_coverage_terminal,
    )

    with pytest.raises(ValueError):
        adopt_final_unsealed_coverage(final, Outcome.UNKNOWN)
    assert emitted == []

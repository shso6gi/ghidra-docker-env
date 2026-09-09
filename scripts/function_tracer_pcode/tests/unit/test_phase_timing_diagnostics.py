# -*- coding: utf-8 -*-
"""Issue #107 (PR-A): phase ごとの内訳時間と reason 遷移の診断。

判定にも最終 UNKNOWN reason 集合にも関与しない観測専用ブロックなので、
「記録が残ること」と「記録が壊れても判定へ伝播しないこと」を固定する。
"""

from types import SimpleNamespace
from unittest.mock import Mock, patch

import pytest

from scripts.function_tracer_pcode.checker.checker import EquivalenceChecker
from scripts.function_tracer_pcode.checker.debug_trace import Attempt
from scripts.function_tracer_pcode.checker.diagnostics import (
    PHASE_SKIPPED_NO_CHANGES,
    PHASE_TIMING_SCHEMA,
    PHASE_TIMING_SEGMENTS,
    PhaseTimeline,
    attach_phase_timings,
    phase_timeline_of,
    result_diagnostics_payload,
    unknown_reason_ids,
)
from scripts.function_tracer_pcode.checker.phases.handler import (
    PhaseHandler,
    PhaseID,
    PhaseResult,
)
from scripts.function_tracer_pcode.checker.unknown_reason import (
    UnknownReasonId,
    make_unknown_reason,
)
from scripts.function_tracer_pcode.core import SignatureHypothesis
from scripts.function_tracer_pcode.smt import SolverStatus

from conftest import MockProgram, create_mock_analysis, create_mock_result


def _reason(reason_id):
    return make_unknown_reason(reason_id, stage="S_PAIRWISE")


class TestPhaseTimeline:
    """記録単体の契約（phase / applied / 変更側 / 内訳時間 / reason 前後）"""

    def test_record_carries_every_phase_field_required_by_issue_107(self):
        timeline = PhaseTimeline()
        timeline.begin("P1_SIGNEDNESS", reason_before=["reason_a"])
        timeline.record_phase_result(
            PhaseResult(
                PhaseID.P1_SIGNEDNESS,
                applied=True,
                retry_name="signedness_fix",
                changed_binary1=True,
                changed_binary2=False,
            )
        )
        timeline.record_reanalyzed_side("function1")
        with timeline.measure("phase_fix"):
            pass
        with timeline.measure("analysis", side="function1"):
            pass
        with timeline.measure("hypothesis_replay"):
            pass
        with timeline.measure("recurrence_refresh"):
            pass
        with timeline.measure("stage_plan"):
            pass
        timeline.end(reason_after=["reason_b"])

        (record,) = timeline.snapshot()
        assert record["schema"] == PHASE_TIMING_SCHEMA
        assert record["phase"] == "P1_SIGNEDNESS"
        assert record["retry_name"] == "signedness_fix"
        assert record["applied"] is True
        assert record["changed_sides"] == ["function1"]
        assert record["reanalyzed_sides"] == ["function1"]
        assert set(record["seconds"]) == set(PHASE_TIMING_SEGMENTS) | {"total"}
        assert all(value >= 0.0 for value in record["seconds"].values())
        assert record["analysis_seconds_by_side"]["function1"] >= 0.0
        assert record["reason_before"] == ["reason_a"]
        assert record["reason_after"] == ["reason_b"]

    def test_same_segment_measured_twice_is_summed(self):
        timeline = PhaseTimeline()
        timeline.begin("P2_PATTERN_INT")
        timeline.add("analysis", 1.5, side="function2")
        timeline.add("analysis", 2.5, side="function2")
        timeline.add("stage_plan", 0.25)
        timeline.end()

        (record,) = timeline.snapshot()
        assert record["seconds"]["analysis"] == 4.0
        assert record["analysis_seconds_by_side"] == {"function2": 4.0}
        assert record["seconds"]["stage_plan"] == 0.25

    def test_records_outside_a_phase_are_dropped_instead_of_raising(self):
        timeline = PhaseTimeline()
        # begin() 前の記録は捨てる（phase を跨いだ混入を作らない）。
        timeline.add("analysis", 3.0, side="function1")
        timeline.record_reanalyzed_side("function1")
        timeline.record_applied(True, True, True)
        with timeline.measure("stage_plan"):
            pass
        timeline.end(reason_after=["reason_a"])
        assert timeline.snapshot() == []

    def test_begin_closes_a_record_that_was_left_open(self):
        timeline = PhaseTimeline()
        timeline.begin("P0_BASE", retry_name="initial")
        timeline.begin("P1_SIGNEDNESS")
        timeline.end()
        assert [record["phase"] for record in timeline.snapshot()] == [
            "P0_BASE",
            "P1_SIGNEDNESS",
        ]

    def test_negative_and_non_numeric_seconds_never_reach_the_record(self):
        timeline = PhaseTimeline()
        timeline.begin("P0_BASE")
        timeline.add("analysis", -5.0, side="function1")
        timeline.add("analysis", "not-a-number", side="function1")
        timeline.end()
        (record,) = timeline.snapshot()
        assert record["seconds"]["analysis"] == 0.0
        assert record["analysis_seconds_by_side"] == {"function1": 0.0}


class TestPhaseTimelineAttachment:
    """診断ブロックへの添付と、失敗しても判定へ伝播しないこと"""

    def test_attach_merges_into_the_existing_diagnostics_block(self):
        timeline = PhaseTimeline()
        timeline.begin("P0_BASE", retry_name="initial")
        timeline.end()
        result = SimpleNamespace(diagnostics={"analysis_seconds": {"function1": 1.0}})

        attach_phase_timings(result, timeline)

        assert result.diagnostics["analysis_seconds"] == {"function1": 1.0}
        assert [row["phase"] for row in result.diagnostics["phases"]] == ["P0_BASE"]

    def test_attach_is_a_no_op_without_a_result_or_a_phase(self):
        timeline = PhaseTimeline()
        attach_phase_timings(None, timeline)
        attach_phase_timings(SimpleNamespace(diagnostics=None), None)

        result = SimpleNamespace(diagnostics=None)
        attach_phase_timings(result, timeline)
        assert result.diagnostics is None

    def test_attach_swallows_a_result_that_rejects_the_assignment(self):
        class _Frozen:
            diagnostics = {}

            def __setattr__(self, name, value):
                raise AttributeError(name)

        timeline = PhaseTimeline()
        timeline.begin("P0_BASE")
        timeline.end()
        attach_phase_timings(_Frozen(), timeline)  # 例外を外へ出さない

    def test_payload_exposes_the_phase_rows_under_timings(self):
        payload = result_diagnostics_payload(
            SimpleNamespace(
                diagnostics={"phases": [{"phase": "P0_BASE", "applied": False}]},
                debug_trace=None,
                total_time=1.0,
                pairwise_stats={},
                stage_path=[],
                solver_results=None,
            )
        )
        assert payload["timings"]["phases"] == [{"phase": "P0_BASE", "applied": False}]

    def test_payload_keeps_an_empty_phase_list_when_nothing_was_recorded(self):
        payload = result_diagnostics_payload(
            SimpleNamespace(
                diagnostics={},
                debug_trace=None,
                total_time=1.0,
                pairwise_stats={},
                stage_path=[],
                solver_results=None,
            )
        )
        assert payload["timings"]["phases"] == []

    def test_timeline_of_a_checker_without_a_run_records_nowhere(self):
        detached = phase_timeline_of(SimpleNamespace())
        assert isinstance(detached, PhaseTimeline)
        assert detached.snapshot() == []


class TestUnknownReasonIds:
    """phase 前後で比べる reason 集合の取り出し"""

    def test_reason_ids_are_deduplicated_and_sorted(self):
        result = SimpleNamespace(
            unknown_reasons=[
                _reason(UnknownReasonId.SAT_COUNTEREXAMPLE_AMBIGUOUS),
                _reason(UnknownReasonId.SOLVER_UNKNOWN_TIMEOUT),
                _reason(UnknownReasonId.SAT_COUNTEREXAMPLE_AMBIGUOUS),
            ]
        )
        assert unknown_reason_ids(result) == sorted(
            {
                UnknownReasonId.SAT_COUNTEREXAMPLE_AMBIGUOUS.value,
                UnknownReasonId.SOLVER_UNKNOWN_TIMEOUT.value,
            }
        )

    def test_missing_or_broken_reasons_yield_an_empty_set(self):
        assert unknown_reason_ids(None) == []
        assert unknown_reason_ids(SimpleNamespace(unknown_reasons=None)) == []
        assert unknown_reason_ids(SimpleNamespace()) == []
        assert unknown_reason_ids(SimpleNamespace(unknown_reasons=[{"reason_id": "x"}])) == ["x"]


class TestPhaseTimingThroughTheWorkflow:
    """workflow を通した実際の phase 記録"""

    @pytest.fixture
    def checker(self):
        return EquivalenceChecker(
            timeout=5,
            debug=False,
            strategy="pairwise",
            canonical_decision_cutover=False,
        )

    @pytest.fixture
    def program(self):
        return MockProgram(name="binary1.exe", architecture="x86:LE:64:default")

    @pytest.fixture
    def program2(self):
        # 左右で別 object にしないと、再解析した側の識別（`program is ctx.program1`）を
        # テストできない。
        return MockProgram(name="binary2.exe", architecture="x86:LE:64:default")

    def _run(self, checker, program, program2, *, phase_result, stage_results):
        """P0 → P1 を 1 回だけ回し、phase 記録つきの結果を返す。"""
        analysis1 = create_mock_analysis("func1", return_type="ulong")
        analysis2 = create_mock_analysis("func2", return_type="int")
        analysis1_fixed = create_mock_analysis(
            "func1", return_type="long"
        ).with_signature_hypothesis(
            SignatureHypothesis(
                return_type_override="long",
                phase="P1_SIGNEDNESS",
                reason="phase_timing_test",
            )
        )
        analyze_calls = {"func1": 0, "func2": 0}

        def _analyze(self, function_name, timeout):
            analyze_calls[function_name] += 1
            if function_name == "func1":
                return analysis1 if analyze_calls["func1"] == 1 else analysis1_fixed
            return analysis2

        def _refresh(self, analysis, timeout=60):
            return analysis

        stage_calls = []

        def _stage_plan(*args, **kwargs):
            stage_calls.append(kwargs.get("retry_count"))
            return stage_results[len(stage_calls) - 1]()

        phase_handler = Mock(spec=PhaseHandler)
        phase_handler.execute_phase.return_value = phase_result
        phase_handler.should_retry.side_effect = [True, False]
        phase_handler.get_retry_reason.side_effect = ["UNKNOWN", "UNKNOWN"]
        phase_handler.run_phase4_mips64_retry.return_value = None
        checker.phase_handler = phase_handler

        with patch(
            "scripts.function_tracer_pcode.analysis.returns.analyzer."
            "ReturnAnalyzer.analyze_function_by_name",
            _analyze,
        ):
            with patch(
                "scripts.function_tracer_pcode.analysis.returns.analyzer."
                "ReturnAnalyzer.refresh_structural_recurrence_summary",
                _refresh,
            ):
                with patch.object(checker, "_run_stage_plan", side_effect=_stage_plan):
                    with patch(
                        "scripts.function_tracer_pcode.checker.checker.TypeFixer"
                    ) as fixer:
                        fixer.side_effect = lambda *args, **kwargs: Mock()
                        result = checker.check_from_binaries(
                            program1=program,
                            program2=program2,
                            function_name1="func1",
                            function_name2="func2",
                            decompile_timeout=60,
                            save_formula=False,
                            retry_with_type_fix=True,
                        )
        return result, analyze_calls

    @staticmethod
    def _unknown_result(reason_ids=()):
        def _make():
            result = create_mock_result(
                is_equivalent=None, solver_status=SolverStatus.UNKNOWN
            )
            result.unknown_reasons = [_reason(reason_id) for reason_id in reason_ids]
            return result

        return _make

    def test_applied_phase_records_its_cost_breakdown_and_reason_transition(
        self, checker, program, program2
    ):
        result, analyze_calls = self._run(
            checker,
            program,
            program2,
            phase_result=PhaseResult(
                PhaseID.P1_SIGNEDNESS,
                applied=True,
                retry_name="signedness_fix",
                changed_binary1=True,
                changed_binary2=False,
            ),
            stage_results=[
                self._unknown_result([UnknownReasonId.SOLVER_UNKNOWN_TIMEOUT]),
                self._unknown_result([UnknownReasonId.SAT_COUNTEREXAMPLE_AMBIGUOUS]),
            ],
        )

        phases = result.to_dict()["diagnostics"]["timings"]["phases"]
        assert [row["phase"] for row in phases] == ["P0_BASE", "P1_SIGNEDNESS"]

        base = phases[0]
        assert base["retry_name"] == "initial"
        # P0 には「型修正の適用」という概念が無いので False ではなく None。
        assert base["applied"] is None
        assert base["skipped_reason"] is None
        assert base["changed_sides"] == []
        # P0 は両側を解析するので、両側が analysis 側の内訳に出る。
        assert base["reanalyzed_sides"] == ["function1", "function2"]
        assert set(base["analysis_seconds_by_side"]) == {"function1", "function2"}
        assert base["reason_before"] == []
        assert base["reason_after"] == [UnknownReasonId.SOLVER_UNKNOWN_TIMEOUT.value]

        retry = phases[1]
        assert retry["applied"] is True
        assert retry["retry_name"] == "signedness_fix"
        # 変更側だけを再解析する現在の不変条件が phase 記録に出る。
        assert retry["changed_sides"] == ["function1"]
        assert retry["reanalyzed_sides"] == ["function1"]
        assert set(retry["analysis_seconds_by_side"]) == {"function1"}
        assert retry["reason_before"] == [UnknownReasonId.SOLVER_UNKNOWN_TIMEOUT.value]
        assert retry["reason_after"] == [
            UnknownReasonId.SAT_COUNTEREXAMPLE_AMBIGUOUS.value
        ]
        # 内訳は phase 全体の時間に含まれる。
        assert retry["seconds"]["total"] >= retry["seconds"]["stage_plan"] >= 0.0
        assert retry["seconds"]["hypothesis_replay"] >= 0.0
        assert retry["seconds"]["recurrence_refresh"] >= 0.0
        assert analyze_calls == {"func1": 2, "func2": 1}

        # 同じ観測が attempt 側にも残り、対応は attempt_id で固定される。
        attempts = result.to_dict()["debug_trace"]["attempts"]
        assert [row["attempt_id"] for row in phases] == [0, 1]
        assert [attempt["attempt_id"] for attempt in attempts] == [0, 1]
        base_attempt, retry_attempt = attempts
        assert base_attempt["phase"] == "P0_BASE"
        assert base_attempt["applied"] is None
        assert base_attempt["reanalyzed_sides"] == ["function1", "function2"]
        assert base_attempt["reason_before"] == []
        assert base_attempt["reason_after"] == [UnknownReasonId.SOLVER_UNKNOWN_TIMEOUT.value]
        assert retry_attempt["phase"] == "P1_SIGNEDNESS"
        assert retry_attempt["applied"] is True
        assert retry_attempt["skipped_reason"] is None
        # 実際に fresh 解析した側が changed side と一致する。
        assert retry_attempt["reanalyzed_sides"] == retry["changed_sides"] == ["function1"]
        assert retry_attempt["reason_before"] == [UnknownReasonId.SOLVER_UNKNOWN_TIMEOUT.value]
        assert retry_attempt["reason_after"] == [
            UnknownReasonId.SAT_COUNTEREXAMPLE_AMBIGUOUS.value
        ]

    def test_unapplied_phase_records_that_it_did_not_reanalyze(
        self, checker, program, program2
    ):
        result, analyze_calls = self._run(
            checker,
            program,
            program2,
            phase_result=PhaseResult(
                PhaseID.P1_SIGNEDNESS,
                applied=False,
                retry_name="signedness_fix",
                changed_binary1=False,
                changed_binary2=False,
            ),
            stage_results=[self._unknown_result([UnknownReasonId.SOLVER_UNKNOWN_TIMEOUT])],
        )

        phases = result.to_dict()["diagnostics"]["timings"]["phases"]
        # 適用できなかった phase は主経路の残りと P4-A の末尾まで進み、
        # そのすべてが「適用なし」として記録される。
        assert [row["phase"] for row in phases] == [
            "P0_BASE",
            "P1_SIGNEDNESS",
            "P2_PATTERN_INT",
            "P4A_MIPS64_ABI",
        ]
        skipped = phases[1]
        assert skipped["applied"] is False
        assert skipped["changed_sides"] == []
        # applied=False の phase は再解析も stage plan もしない（現在の不変条件）。
        assert skipped["reanalyzed_sides"] == []
        assert skipped["analysis_seconds_by_side"] == {}
        assert skipped["seconds"]["stage_plan"] == 0.0
        assert skipped["reason_before"] == skipped["reason_after"]
        assert skipped["skipped_reason"] == PHASE_SKIPPED_NO_CHANGES
        assert all(row["reanalyzed_sides"] == [] for row in phases[1:])
        assert analyze_calls == {"func1": 1, "func2": 1}

        # applied=False の phase も attempt として残り、その時点の reason を失わない。
        attempts = result.to_dict()["debug_trace"]["attempts"]
        assert [attempt["phase"] for attempt in attempts] == ["P0_BASE", "P1_SIGNEDNESS", "P2_PATTERN_INT"]
        for attempt in attempts[1:]:
            assert attempt["applied"] is False
            assert attempt["skipped_reason"] == PHASE_SKIPPED_NO_CHANGES
            assert attempt["reanalyzed_sides"] == []
            assert attempt["reason_before"] == attempt["reason_after"] == [
                UnknownReasonId.SOLVER_UNKNOWN_TIMEOUT.value
            ]
            # この attempt は判定を実行していないので、reason occurrence は作らない
            # （作ると proof completion / reason completion の対象が増えてしまう）。
            assert attempt["unknown_reasons"] == []
            assert attempt["reason_occurrences"] == []
        # phase 行と attempt は attempt_id で 1 対 1 に対応する。
        assert [row["attempt_id"] for row in phases[:3]] == [0, 1, 2]

    def test_phase_records_do_not_change_the_outcome_or_the_reason_set(
        self, checker, program, program2
    ):
        result, _ = self._run(
            checker,
            program,
            program2,
            phase_result=PhaseResult(
                PhaseID.P1_SIGNEDNESS,
                applied=True,
                retry_name="signedness_fix",
                changed_binary1=True,
                changed_binary2=False,
            ),
            stage_results=[
                self._unknown_result([UnknownReasonId.SOLVER_UNKNOWN_TIMEOUT]),
                self._unknown_result([UnknownReasonId.SAT_COUNTEREXAMPLE_AMBIGUOUS]),
            ],
        )
        assert result.is_equivalent is None
        assert unknown_reason_ids(result) == [
            UnknownReasonId.SAT_COUNTEREXAMPLE_AMBIGUOUS.value
        ]

    def test_sat_tail_records_the_p4c_and_p4a_phases(self, checker, program, program2):
        """SAT が残る経路で P4-C / P4-A の phase 行と attempt が閉じられる。"""
        analysis1 = create_mock_analysis("func1", return_type="ulong")
        analysis2 = create_mock_analysis("func2", return_type="int")
        analyze_calls = {"func1": 0, "func2": 0}

        def _analyze(self, function_name, timeout):
            analyze_calls[function_name] += 1
            return analysis1 if function_name == "func1" else analysis2

        stage_calls = []

        def _stage_plan(*args, **kwargs):
            stage_calls.append(kwargs.get("retry_count"))
            result = create_mock_result(is_equivalent=False, solver_status=SolverStatus.SAT)
            result.unknown_reasons = []
            return result

        phase_handler = Mock(spec=PhaseHandler)
        # P4-C（戻り値型リトライ）は binary2、P4-A（MIPS64 ABI）は binary1 を変更する。
        phase_handler.should_fix_return_type.return_value = True
        phase_handler.run_phase2_return_type_fix.return_value = (True, False, True)
        phase_handler.execute_phase.return_value = PhaseResult(
            PhaseID.P4A_MIPS64_ABI,
            applied=True,
            retry_name="mips64_abi_fix",
            changed_binary1=True,
            changed_binary2=False,
        )
        phase_handler.run_phase4_mips64_retry.return_value = None
        checker.phase_handler = phase_handler

        with patch(
            "scripts.function_tracer_pcode.analysis.returns.analyzer."
            "ReturnAnalyzer.analyze_function_by_name",
            _analyze,
        ):
            with patch.object(checker, "_run_stage_plan", side_effect=_stage_plan):
                with patch("scripts.function_tracer_pcode.checker.checker.TypeFixer") as fixer:
                    fixer.side_effect = lambda *args, **kwargs: Mock()
                    result = checker.check_from_binaries(
                        program1=program,
                        program2=program2,
                        function_name1="func1",
                        function_name2="func2",
                        decompile_timeout=60,
                        save_formula=False,
                        retry_with_type_fix=True,
                    )

        phases = result.to_dict()["diagnostics"]["timings"]["phases"]
        attempts = result.to_dict()["debug_trace"]["attempts"]
        assert [row["phase"] for row in phases] == [
            "P0_BASE",
            "P4C_RETURN_TYPE_FIX",
            "P4A_MIPS64_ABI",
        ]
        assert [attempt["phase"] for attempt in attempts] == [
            "P0_BASE",
            "P4C_RETURN_TYPE_FIX",
            "P4A_MIPS64_ABI",
        ]
        # phase 行 → attempt の対応は attempt_id で固定。
        assert [row["attempt_id"] for row in phases] == [
            attempt["attempt_id"] for attempt in attempts
        ]

        p4c_row, p4a_row = phases[1], phases[2]
        assert p4c_row["applied"] is True and p4c_row["retry_name"] == "sat_return_type_fix"
        assert p4c_row["changed_sides"] == p4c_row["reanalyzed_sides"] == ["function2"]
        assert p4c_row["seconds"]["total"] >= p4c_row["seconds"]["stage_plan"] >= 0.0
        assert p4a_row["applied"] is True and p4a_row["retry_name"] == "mips64_abi_fix"
        assert p4a_row["changed_sides"] == p4a_row["reanalyzed_sides"] == ["function1"]

        assert attempts[1]["applied"] is True
        assert attempts[1]["reanalyzed_sides"] == ["function2"]
        assert attempts[2]["applied"] is True
        assert attempts[2]["reanalyzed_sides"] == ["function1"]
        for attempt in attempts:
            assert attempt["reason_before"] == attempt["reason_after"] == []
        # P0 が両側、P4-C が binary2、P4-A が binary1 を fresh 解析している。
        assert analyze_calls == {"func1": 2, "func2": 2}
        assert len(stage_calls) == 3


class TestPhaseTimelineLifecycle:
    """`checker._phase_timeline` は 1 run の間だけ存在する"""

    @pytest.fixture
    def checker(self):
        return EquivalenceChecker(
            timeout=5,
            debug=False,
            strategy="pairwise",
            canonical_decision_cutover=False,
        )

    @pytest.fixture
    def program(self):
        return MockProgram(name="test_binary.exe", architecture="x86:LE:64:default")

    @staticmethod
    def _run(checker, program):
        def _analyze(self, function_name, timeout):
            return create_mock_analysis(function_name)

        with patch(
            "scripts.function_tracer_pcode.analysis.returns.analyzer."
            "ReturnAnalyzer.analyze_function_by_name",
            _analyze,
        ):
            with patch.object(
                checker,
                "_run_stage_plan",
                side_effect=lambda *a, **k: create_mock_result(
                    is_equivalent=None, solver_status=SolverStatus.UNKNOWN
                ),
            ):
                return checker.check_from_binaries(
                    program1=program,
                    program2=program,
                    function_name1="func1",
                    function_name2="func2",
                    decompile_timeout=60,
                    save_formula=False,
                    retry_with_type_fix=False,
                )

    def test_run_does_not_leave_its_timeline_on_the_checker(self, checker, program):
        result = self._run(checker, program)
        assert result.to_dict()["diagnostics"]["timings"]["phases"]

        assert not hasattr(checker, "_phase_timeline")
        # workflow 外の呼び出しは前 run の記録先を掴まない。
        detached = phase_timeline_of(checker)
        detached.begin("P0_BASE")
        detached.end()
        assert len(detached.snapshot()) == 1
        assert len(result.to_dict()["diagnostics"]["timings"]["phases"]) == 1

    def test_an_existing_attribute_is_restored_after_the_run(self, checker, program):
        outer = PhaseTimeline()
        checker._phase_timeline = outer

        self._run(checker, program)

        assert checker._phase_timeline is outer
        assert outer.snapshot() == []

    def test_the_attribute_is_restored_when_the_run_raises(self, checker, program):
        with patch.object(
            checker, "_analyze_and_check_with_analysis", side_effect=RuntimeError("boom")
        ):
            with pytest.raises(RuntimeError):
                self._run(checker, program)
        assert not hasattr(checker, "_phase_timeline")

        outer = PhaseTimeline()
        checker._phase_timeline = outer
        with patch.object(
            checker, "_analyze_and_check_with_analysis", side_effect=RuntimeError("boom")
        ):
            with pytest.raises(RuntimeError):
                self._run(checker, program)
        assert checker._phase_timeline is outer


class TestAttemptSerializationCompatibility:
    """新 field は既定値を持ち、既存形式の payload を壊さない"""

    def test_attempt_without_the_new_fields_serializes_with_neutral_defaults(self):
        attempt = Attempt(
            attempt_id=0,
            retry_count=0,
            phase="P0_BASE",
            stage_path=[],
            strategy="pairwise",
            result=None,
            transition_reason="UNKNOWN",
        )
        payload = attempt.to_dict()
        assert payload["applied"] is None
        assert payload["reanalyzed_sides"] == []
        assert payload["skipped_reason"] is None
        assert payload["reason_before"] == []
        assert payload["reason_after"] == []

    def test_legacy_attempt_payload_without_the_new_keys_still_aggregates(self):
        from scripts.function_tracer_pcode.reporting.root_blocker_summary import (
            summarize_root_blockers,
        )

        legacy_attempt = {
            "attempt_id": 0,
            "retry_count": 0,
            "phase": "P0_BASE",
            "strategy": "pairwise",
            "result": None,
            "transition_reason": "UNKNOWN",
            "unknown_reasons": [_reason(UnknownReasonId.SOLVER_UNKNOWN_TIMEOUT).to_dict()],
        }
        payload = {
            "is_equivalent": None,
            "case_id": "f",
            "function1_name": "f",
            "function2_name": "f",
            "function1_identity": ("function", "left", "f", 0x1000, "sig-left"),
            "function2_identity": ("function", "right", "f", 0x2000, "sig-right"),
            "run_identity": "run-1",
            "artifact_identity": ("run-1", "f"),
            "binary1_content_identity": ("sha256", "left"),
            "binary2_content_identity": ("sha256", "right"),
            "debug_trace": {"final_result": None, "attempts": [legacy_attempt]},
        }
        summary = summarize_root_blockers([payload])
        assert summary is not None

    def test_legacy_diagnostics_without_the_phase_block_still_summarizes(self):
        from scripts.function_tracer_pcode.reporting.unknown_reason_summary import (
            summarize_validation_unknowns,
        )

        summary = summarize_validation_unknowns([
            {
                "final_outcome": "UNKNOWN",
                "is_equivalent": None,
                "unknown_reasons": [_reason(UnknownReasonId.SOLVER_UNKNOWN_TIMEOUT).to_dict()],
                "diagnostics": {
                    "timings": {
                        "total_seconds": 2.0,
                        "analysis_seconds": {"function1": 0.5},
                        "solver_seconds": 0.3,
                    }
                },
            }
        ])
        assert summary.diagnostics_stats["results_with_diagnostics"] == 1

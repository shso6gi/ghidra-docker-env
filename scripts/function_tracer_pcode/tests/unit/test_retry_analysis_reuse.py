# -*- coding: utf-8 -*-
"""Issue #107 (PR-B): retry phase の変更側再解析を base snapshot の再利用へ置き換える。

再利用は「速いから」ではなく「fresh 再解析と同じ semantic 入力になると確認できるから」
採用する。したがってここで固定するのは主に **再利用しない条件** と、
**再利用しないと決めたときに必ず fresh へ倒れること**である。
"""

from dataclasses import replace
from types import SimpleNamespace
from unittest.mock import Mock, patch

import pytest

from scripts.function_tracer_pcode.checker.checker import EquivalenceChecker
from scripts.function_tracer_pcode.checker.diagnostics import (
    ANALYSIS_SOURCE_FRESH,
    ANALYSIS_SOURCE_REUSE,
    REUSE_FALLBACK_BASE_SNAPSHOT_MUTATED,
    REUSE_FALLBACK_FINGERPRINT_UNAVAILABLE,
    REUSE_FALLBACK_MODIFICATION_NUMBER_CHANGED,
    REUSE_FALLBACK_MODIFICATION_NUMBER_UNAVAILABLE,
    REUSE_FALLBACK_NO_SNAPSHOT,
    REUSE_FALLBACK_PROGRAM_IDENTITY_CHANGED,
    REUSE_FALLBACK_SHADOW_MISMATCH,
    PhaseTimeline,
)
from scripts.function_tracer_pcode.checker.phases.handler import (
    PhaseContext,
    PhaseHandler,
    PhaseID,
    PhaseResult,
    RetryAnalysisBase,
)
from scripts.function_tracer_pcode.checker.reanalysis import (
    build_retry_analysis_base,
    program_modification_number,
    reuse_equivalence_key,
    reuse_equivalence_mismatch_kind,
    runtime_type_projection,
    selective_reanalysis_and_check,
    semantic_fingerprint_of,
)
from scripts.function_tracer_pcode.core import SignatureHypothesis
from scripts.function_tracer_pcode.semantics.typing.fixer import TypeFixResult
from scripts.function_tracer_pcode.smt import SolverStatus

from conftest import (
    MockDataType,
    MockProgram,
    create_mock_analysis,
    create_mock_result,
)

_ANALYZER = "scripts.function_tracer_pcode.analysis.returns.analyzer.ReturnAnalyzer"


class VersionedMockProgram(MockProgram):
    """``getModificationNumber()`` を持つ Program。

    conftest の ``MockProgram`` は Ghidra の ``DomainObject`` API を持たないので、
    このテストの中だけで足す（production API も共有 fixture も広げない）。
    """

    def __post_init__(self):
        super().__post_init__()
        self.modification_number = 1

    def getModificationNumber(self):
        return self.modification_number


def _hypothesis(type_name="long", phase="P1_SIGNEDNESS"):
    return SignatureHypothesis(
        return_type_override=type_name,
        phase=phase,
        reason="retry_analysis_reuse_test",
    )


def _make_ctx(program1, program2, analysis1, analysis2):
    return PhaseContext(
        program1=program1,
        program2=program2,
        function_name1="func1",
        function_name2="func2",
        binary1_name="binary1.exe",
        binary2_name="binary2.exe",
        decompile_timeout=60,
        save_formula=False,
        type_fix_result=TypeFixResult(),
        original_signature1=None,
        original_signature2=None,
        analysis1=analysis1,
        analysis2=analysis2,
    )


def _run_selective(
    *,
    ctx,
    changed1=False,
    changed2=False,
    fresh_by_name=None,
    refresh_hook=None,
    fingerprint_hook=None,
):
    """`selective_reanalysis_and_check()` を production の呼ばれ方で 1 回動かす。"""
    checker = EquivalenceChecker(
        timeout=5, debug=False, strategy="pairwise", canonical_decision_cutover=False
    )
    timeline = PhaseTimeline()
    checker._phase_timeline = timeline
    timeline.begin("P1_SIGNEDNESS", retry_name="signedness_fix")

    analyze_calls = []
    refresh_calls = []
    stage_inputs = {}

    def _analyze(self, function_name, timeout):
        analyze_calls.append(function_name)
        return (fresh_by_name or {}).get(function_name)

    def _refresh(self, analysis, timeout=60):
        refresh_calls.append(
            (analysis.function_name, len(analysis.signature_hypotheses or ()))
        )
        if refresh_hook is not None:
            return refresh_hook(analysis)
        return analysis

    def _stage_plan(analysis1, analysis2, *args, **kwargs):
        stage_inputs["analysis1"] = analysis1
        stage_inputs["analysis2"] = analysis2
        return create_mock_result(is_equivalent=None, solver_status=SolverStatus.UNKNOWN)

    phase_result = PhaseResult(
        PhaseID.P1_SIGNEDNESS,
        applied=True,
        retry_name="signedness_fix",
        changed_binary1=changed1,
        changed_binary2=changed2,
    )

    patches = [
        patch(f"{_ANALYZER}.analyze_function_by_name", _analyze),
        patch(f"{_ANALYZER}.refresh_structural_recurrence_summary", _refresh),
        patch.object(checker, "_run_stage_plan", side_effect=_stage_plan),
    ]
    if fingerprint_hook is not None:
        patches.append(
            patch(
                "scripts.function_tracer_pcode.checker.reanalysis.semantic_fingerprint_of",
                fingerprint_hook,
            )
        )
    for entered in patches:
        entered.__enter__()
    try:
        analysis1, analysis2, result = selective_reanalysis_and_check(
            checker, ctx, phase_result, 1
        )
    finally:
        for entered in reversed(patches):
            entered.__exit__(None, None, None)

    row = timeline.end()
    return SimpleNamespace(
        row=row,
        analysis1=analysis1,
        analysis2=analysis2,
        result=result,
        analyze_calls=analyze_calls,
        refresh_calls=refresh_calls,
        stage_inputs=stage_inputs,
        ctx=ctx,
    )


@pytest.fixture
def reuse_mode(monkeypatch):
    """再利用のみを構成するモード（fresh 再解析を行わない）。"""
    from scripts.function_tracer_pcode.config import settings

    monkeypatch.setattr(settings, "RETRY_ANALYSIS_REUSE_ENABLED", True, raising=False)
    monkeypatch.setattr(settings, "RETRY_ANALYSIS_REUSE_SHADOW", False, raising=False)


@pytest.fixture
def shadow_mode(monkeypatch):
    """fresh と reuse を両方構成し、fresh を authoritative にする既定モード。"""
    from scripts.function_tracer_pcode.config import settings

    monkeypatch.setattr(settings, "RETRY_ANALYSIS_REUSE_ENABLED", True, raising=False)
    monkeypatch.setattr(settings, "RETRY_ANALYSIS_REUSE_SHADOW", True, raising=False)


class _Fixture:
    """base を seed 済みの 2 side ぶんの材料。"""

    def __init__(self, *, program1=None, program2=None, seed1=True, seed2=True):
        self.program1 = program1 or VersionedMockProgram(name="binary1.exe")
        self.program2 = program2 or VersionedMockProgram(name="binary2.exe")
        self.raw1 = create_mock_analysis("func1", return_type="ulong")
        self.raw2 = create_mock_analysis("func2", return_type="uint")
        self.cached1 = self.raw1.with_signature_hypothesis(_hypothesis("long"))
        self.cached2 = self.raw2.with_signature_hypothesis(_hypothesis("int"))
        self.ctx = _make_ctx(self.program1, self.program2, self.cached1, self.cached2)
        if seed1:
            self.ctx.retry_analysis_base1 = build_retry_analysis_base(
                self.program1, self.raw1
            )
        if seed2:
            self.ctx.retry_analysis_base2 = build_retry_analysis_base(
                self.program2, self.raw2
            )

    def run(self, **kwargs):
        kwargs.setdefault(
            "fresh_by_name", {"func1": self.raw1, "func2": self.raw2}
        )
        return _run_selective(ctx=self.ctx, **kwargs)


class TestProgramModificationNumber:
    """Program の世代読み取り（判定不能は必ず None）"""

    def test_missing_api_is_unavailable(self):
        assert program_modification_number(MockProgram(name="b.exe")) is None

    def test_none_program_is_unavailable(self):
        assert program_modification_number(None) is None

    def test_raising_api_is_unavailable(self):
        class _Raising:
            def getModificationNumber(self):
                raise RuntimeError("boom")

        assert program_modification_number(_Raising()) is None

    def test_bool_is_not_accepted_as_a_generation(self):
        class _Bool:
            def getModificationNumber(self):
                return True

        assert program_modification_number(_Bool()) is None

    def test_non_numeric_is_unavailable(self):
        class _Text:
            def getModificationNumber(self):
                return "seven"

        assert program_modification_number(_Text()) is None

    def test_numeric_generation_is_read(self):
        program = VersionedMockProgram(name="b.exe")
        program.modification_number = 42
        assert program_modification_number(program) == 42


class TestBaseSnapshotConstruction:
    """base state の 3 要素は一体でしか作られない"""

    def test_base_holds_a_copy_and_its_generation_and_equivalence_key(self):
        program = VersionedMockProgram(name="b.exe")
        program.modification_number = 5
        analysis = create_mock_analysis("func1", return_type="ulong")

        base = build_retry_analysis_base(program, analysis)

        assert isinstance(base, RetryAnalysisBase)
        assert base.analysis is not analysis  # 複製であって参照ではない
        assert base.program is program
        assert base.modification_number == 5
        assert base.equivalence_key == reuse_equivalence_key(analysis)

    def test_no_base_when_the_generation_cannot_be_read(self):
        analysis = create_mock_analysis("func1")
        assert build_retry_analysis_base(MockProgram(name="b.exe"), analysis) is None

    def test_no_base_when_the_equivalence_key_cannot_be_built(self):
        program = VersionedMockProgram(name="b.exe")
        analysis = create_mock_analysis("func1")
        with patch(
            "scripts.function_tracer_pcode.checker.reanalysis.reuse_equivalence_key",
            lambda _analysis: None,
        ):
            assert build_retry_analysis_base(program, analysis) is None

    def test_no_base_without_an_analysis(self):
        assert build_retry_analysis_base(VersionedMockProgram(name="b.exe"), None) is None

    def test_fingerprint_of_an_unserializable_analysis_is_none_instead_of_raising(self):
        analysis = create_mock_analysis("func1")
        with patch(
            "scripts.function_tracer_pcode.proof.obligations.snapshot."
            "AnalysisSnapshot.from_function_analysis",
            side_effect=TypeError("opaque object"),
        ):
            assert semantic_fingerprint_of(analysis) is None


class TestReuseEquivalenceContract:
    """再利用等価キー: runtime 型意味と完了済み proof まで含める

    `dart/test/Eq/newV` の `snippet` B4_B16 / B6_B14 / B13_B15 は、
    `AnalysisSnapshot` の semantic fingerprint が一致していたのに P4-A の適用可否が変わり、
    最終 UNKNOWN reason から `outcome_same_kind_consistency_unproven` が消えた。原因は
    `to_dict()` が `parameters_without_runtime_objects()` を通って `data_type_obj` を落とす
    一方、P4-A（`checker/arch/mips64.py`）はその object から型名とサイズを読むこと。
    ここではその条件を単体で再現し、強化後の等価キーが mismatch として捕まえることを固定する。
    """

    @staticmethod
    def _with_param_type(analysis, data_type_obj, data_type_name, declared_size=8):
        """parameter 1 件だけ持つ解析ビューにする（runtime object だけ差し替える）。

        ``to_dict()`` に載る記述（型名・サイズ）は固定し、runtime の ``data_type_obj``
        だけを変える。これが実測で起きていた条件そのもの。
        """
        return replace(
            analysis,
            parameters=[
                {
                    "name": "param_1",
                    "index": 0,
                    "data_type": data_type_name,
                    "data_type_obj": data_type_obj,
                    "size": declared_size,
                    "is_signed": True,
                }
            ],
        )

    def test_same_declared_name_but_different_runtime_width_is_a_mismatch(self):
        # `to_dict()` に載る文字列は同じで、runtime DataType のサイズだけ違う状況。
        base = create_mock_analysis("func1")
        four_byte = MockDataType("long", 4, True)
        eight_byte = MockDataType("long", 8, True)
        left = self._with_param_type(base, four_byte, "long")
        right = self._with_param_type(base, eight_byte, "long")

        assert semantic_fingerprint_of(left) == semantic_fingerprint_of(right)
        assert reuse_equivalence_key(left) != reuse_equivalence_key(right)
        assert (
            reuse_equivalence_mismatch_kind(
                reuse_equivalence_key(left), reuse_equivalence_key(right)
            )
            == "runtime_type_semantics"
        )

    def test_same_declared_name_but_different_runtime_signedness_is_a_mismatch(self):
        base = create_mock_analysis("func1")
        signed = MockDataType("int", 4, True)
        unsigned = MockDataType("int", 4, False)
        left = self._with_param_type(base, signed, "int")
        right = self._with_param_type(base, unsigned, "int")

        assert reuse_equivalence_key(left) != reuse_equivalence_key(right)

    def test_distinct_runtime_objects_with_the_same_semantics_still_match(self):
        # object identity は比較条件にしない（複製が別 object になっても mismatch にしない）。
        base = create_mock_analysis("func1")
        left = self._with_param_type(base, MockDataType("int", 4, True), "int")
        right = self._with_param_type(base, MockDataType("int", 4, True), "int")

        assert left.parameters[0]["data_type_obj"] is not right.parameters[0]["data_type_obj"]
        assert reuse_equivalence_key(left) == reuse_equivalence_key(right)
        assert (
            reuse_equivalence_mismatch_kind(
                reuse_equivalence_key(left), reuse_equivalence_key(right)
            )
            is None
        )

    def test_return_type_runtime_semantics_are_covered(self):
        base = create_mock_analysis("func1")
        left = replace(base, return_type="long", return_type_obj=MockDataType("long", 8, True))
        right = replace(base, return_type="long", return_type_obj=MockDataType("long", 4, True))

        assert reuse_equivalence_key(left) != reuse_equivalence_key(right)

    def test_completed_recovery_proof_carry_over_is_a_mismatch(self):
        # `AnalysisSnapshot` は proof state を除外するので、指紋は一致してしまう。
        base = create_mock_analysis("func1")
        carried = replace(
            base,
            completed_recovery_proof_ids=(("recovery_proof_v1", "func1", 1),),
        )

        assert semantic_fingerprint_of(base) == semantic_fingerprint_of(carried)
        assert reuse_equivalence_key(base) != reuse_equivalence_key(carried)
        assert (
            reuse_equivalence_mismatch_kind(
                reuse_equivalence_key(base), reuse_equivalence_key(carried)
            )
            == "completed_recovery_proofs"
        )

    def test_unbuildable_projection_yields_no_key(self):
        analysis = create_mock_analysis("func1")
        with patch(
            "scripts.function_tracer_pcode.checker.reanalysis._analysis_runtime_type_projection",
            side_effect=TypeError("opaque runtime type"),
        ):
            assert reuse_equivalence_key(analysis) is None

    def test_projection_reads_the_runtime_object_before_the_declared_name(self):
        # P4-A と同じ読み方（object を先に見る）になっていること。
        projected = runtime_type_projection(MockDataType("int", 4, True), "long", 8)
        assert projected[0] == "int"
        assert projected[2] == 4


class TestReuseModeAcceptsAValidBase:
    """再利用が成立する経路（fresh 再解析を行わない）"""

    def test_changed_side_is_rebuilt_from_the_base_without_a_fresh_analysis(
        self, reuse_mode
    ):
        fixture = _Fixture()
        run = fixture.run(changed1=True)

        assert run.analyze_calls == []  # fresh 再解析が消えている
        assert run.row["reuse_eligible_by_side"] == {"function1": True}
        assert run.row["analysis_source_by_side"] == {"function1": ANALYSIS_SOURCE_REUSE}
        assert run.row["reanalyzed_sides"] == ["function1"]
        assert run.row["seconds"]["analysis"] == 0.0

    def test_reused_view_carries_the_same_hypotheses_in_the_same_order(self, reuse_mode):
        fixture = _Fixture()
        fixture.cached1 = fixture.cached1.with_signature_hypothesis(
            _hypothesis("longlong", phase="P2_PATTERN_INT")
        )
        fixture.ctx.analysis1 = fixture.cached1
        run = fixture.run(changed1=True)

        replayed = [
            payload.get("return_type_override")
            for payload in run.analysis1.signature_hypotheses
        ]
        expected = [
            payload.get("return_type_override")
            for payload in fixture.cached1.signature_hypotheses
        ]
        assert replayed == expected == ["long", "longlong"]

    def test_both_sides_are_rebuilt_when_both_changed(self, reuse_mode):
        fixture = _Fixture()
        run = fixture.run(changed1=True, changed2=True)

        assert run.analyze_calls == []
        assert run.row["reuse_eligible_by_side"] == {"function1": True, "function2": True}
        assert run.row["analysis_source_by_side"] == {
            "function1": ANALYSIS_SOURCE_REUSE,
            "function2": ANALYSIS_SOURCE_REUSE,
        }

    def test_recurrence_summary_is_refreshed_once_per_changed_side_with_hypotheses(
        self, reuse_mode
    ):
        fixture = _Fixture()
        run = fixture.run(changed1=True, changed2=True)

        # 仮説を重ねた側だけ、その側の関数について 1 回ずつ張り直す（削らない）。
        assert run.refresh_calls == [("func1", 1), ("func2", 1)]

    def test_unchanged_sides_are_neither_reused_nor_reanalyzed(self, reuse_mode):
        fixture = _Fixture()
        run = fixture.run()

        assert run.analyze_calls == []
        assert run.refresh_calls == []
        assert run.row["reuse_eligible_by_side"] == {}
        assert run.row["analysis_source_by_side"] == {}
        assert run.row["reanalyzed_sides"] == []


class TestReuseIsRefusedAndFallsBackToFresh:
    """validity 条件が欠けたら必ず fresh 再解析へ倒れる"""

    @staticmethod
    def _assert_fell_back(run, reason, *, side="function1"):
        assert run.analyze_calls == ["func1" if side == "function1" else "func2"]
        assert run.row["reuse_eligible_by_side"][side] is False
        assert run.row["analysis_source_by_side"][side] == reason

    def test_missing_base_snapshot(self, reuse_mode):
        fixture = _Fixture(seed1=False)
        run = fixture.run(changed1=True)
        self._assert_fell_back(run, REUSE_FALLBACK_NO_SNAPSHOT)

    def test_program_identity_changed(self, reuse_mode):
        fixture = _Fixture()
        fixture.ctx.retry_analysis_base1 = build_retry_analysis_base(
            VersionedMockProgram(name="other.exe"), fixture.raw1
        )
        run = fixture.run(changed1=True)
        self._assert_fell_back(run, REUSE_FALLBACK_PROGRAM_IDENTITY_CHANGED)

    def test_modification_number_unavailable(self, reuse_mode):
        fixture = _Fixture()
        base = fixture.ctx.retry_analysis_base1
        # seed 後に世代を読めなくなった Program（判定不能は「無効」と同じ扱い）。
        plain = MockProgram(name="binary1.exe")
        fixture.ctx.program1 = plain
        fixture.ctx.retry_analysis_base1 = RetryAnalysisBase(
            analysis=base.analysis,
            program=plain,
            modification_number=base.modification_number,
            equivalence_key=base.equivalence_key,
        )
        run = fixture.run(changed1=True)
        self._assert_fell_back(run, REUSE_FALLBACK_MODIFICATION_NUMBER_UNAVAILABLE)

    def test_program_was_modified_after_the_base_was_taken(self, reuse_mode):
        fixture = _Fixture()
        fixture.program1.modification_number += 1
        run = fixture.run(changed1=True)
        self._assert_fell_back(run, REUSE_FALLBACK_MODIFICATION_NUMBER_CHANGED)

    def test_base_snapshot_mutated_before_the_reuse_is_built(self, reuse_mode):
        fixture = _Fixture()
        # 共有された field が書き換えられた状態を作る（semantic な note は指紋に入る）。
        fixture.ctx.retry_analysis_base1.analysis.analysis_notes.append("mutated base")
        run = fixture.run(changed1=True)
        self._assert_fell_back(run, REUSE_FALLBACK_BASE_SNAPSHOT_MUTATED)

    def test_base_snapshot_mutated_while_the_reuse_is_being_built(self, reuse_mode):
        fixture = _Fixture()
        base_analysis = fixture.ctx.retry_analysis_base1.analysis

        def _refresh(analysis):
            # recurrence refresh には入力へ in-place 追記する経路が実在する。
            base_analysis.analysis_notes.append("mutated during refresh")
            return analysis

        run = fixture.run(changed1=True, refresh_hook=_refresh)
        self._assert_fell_back(run, REUSE_FALLBACK_BASE_SNAPSHOT_MUTATED)

    def test_diagnostic_notes_do_not_trip_the_base_integrity_gate(self, reuse_mode):
        fixture = _Fixture()
        # `diagnostic:` 接頭辞の note は semantic fingerprint に入らないので誤検知しない。
        fixture.ctx.retry_analysis_base1.analysis.analysis_notes.append(
            "diagnostic:subordinate_parent_binding_required:deadbeef"
        )
        run = fixture.run(changed1=True)

        assert run.analyze_calls == []
        assert run.row["analysis_source_by_side"]["function1"] == ANALYSIS_SOURCE_REUSE

    def test_fingerprint_generation_failure_falls_back_without_failing_the_check(
        self, reuse_mode
    ):
        fixture = _Fixture()
        run = fixture.run(changed1=True, fingerprint_hook=lambda _analysis: None)

        self._assert_fell_back(run, REUSE_FALLBACK_FINGERPRINT_UNAVAILABLE)
        # 診断のための指紋生成が失敗しても判定は壊さない。
        assert run.result.error_message is None
        assert run.result.is_equivalent is None

    def test_reuse_can_be_disabled_entirely(self, monkeypatch):
        from scripts.function_tracer_pcode.config import settings

        monkeypatch.setattr(settings, "RETRY_ANALYSIS_REUSE_ENABLED", False, raising=False)
        fixture = _Fixture()
        run = fixture.run(changed1=True)

        assert run.analyze_calls == ["func1"]
        assert run.row["reuse_eligible_by_side"] == {}
        assert run.row["analysis_source_by_side"] == {"function1": ANALYSIS_SOURCE_FRESH}

    def test_one_side_reuses_while_the_other_falls_back(self, reuse_mode):
        fixture = _Fixture()
        fixture.program2.modification_number += 1
        run = fixture.run(changed1=True, changed2=True)

        assert run.analyze_calls == ["func2"]
        assert run.row["reuse_eligible_by_side"] == {
            "function1": True,
            "function2": False,
        }
        assert run.row["analysis_source_by_side"] == {
            "function1": ANALYSIS_SOURCE_REUSE,
            "function2": REUSE_FALLBACK_MODIFICATION_NUMBER_CHANGED,
        }

    def test_eligibility_and_source_never_disagree(self, reuse_mode):
        fixture = _Fixture()
        fixture.program2.modification_number += 1
        run = fixture.run(changed1=True, changed2=True)

        for side, eligible in run.row["reuse_eligible_by_side"].items():
            source = run.row["analysis_source_by_side"][side]
            assert eligible is (source == ANALYSIS_SOURCE_REUSE)


class TestFallbackReSeed:
    """fallback で得た raw 解析からだけ base を張り直す"""

    def test_re_seed_stores_the_raw_analysis_and_the_new_generation(self, reuse_mode):
        fixture = _Fixture()
        fixture.program1.modification_number = 9
        run = fixture.run(changed1=True)

        base = run.ctx.retry_analysis_base1
        assert base.modification_number == 9
        # 仮説を重ねる前の raw だけを base にする（派生ビューを次の base にしない）。
        assert list(base.analysis.signature_hypotheses or ()) == []
        assert base.equivalence_key == reuse_equivalence_key(fixture.raw1)
        assert base.analysis is not fixture.raw1

    def test_re_seeded_base_is_reusable_on_the_next_retry(self, reuse_mode):
        fixture = _Fixture()
        fixture.program1.modification_number = 9
        fixture.run(changed1=True)
        second = fixture.run(changed1=True)

        assert second.analyze_calls == []
        assert second.row["analysis_source_by_side"]["function1"] == ANALYSIS_SOURCE_REUSE

    def test_base_is_left_untouched_when_the_three_parts_cannot_be_rebuilt(
        self, reuse_mode
    ):
        fixture = _Fixture()
        original = fixture.ctx.retry_analysis_base1
        fixture.program1.modification_number += 1

        real_fingerprint = semantic_fingerprint_of

        def _fingerprint(analysis):
            # 再 seed で作る複製の指紋だけ作れない状況（3 要素が揃わない）。
            if analysis is original.analysis:
                return real_fingerprint(analysis)
            return None

        run = fixture.run(changed1=True, fingerprint_hook=_fingerprint)

        assert run.ctx.retry_analysis_base1 is original
        assert run.analyze_calls == ["func1"]

    def test_no_re_seed_when_the_fresh_analysis_fails(self, reuse_mode):
        fixture = _Fixture(seed1=False)
        run = fixture.run(changed1=True, fresh_by_name={"func1": None})

        # raw 解析が無いので base は作らない（作れない state を残さない）。
        assert run.ctx.retry_analysis_base1 is None
        assert run.row["reuse_eligible_by_side"]["function1"] is False
        assert run.row["analysis_source_by_side"]["function1"] == REUSE_FALLBACK_NO_SNAPSHOT


class TestShadowValidationMode:
    """既定モード: fresh と reuse を両方構成し、fresh を authoritative にする"""

    def test_matching_views_are_recorded_and_fresh_stays_authoritative(self, shadow_mode):
        fixture = _Fixture()
        run = fixture.run(changed1=True)

        assert run.analyze_calls == ["func1"]  # fresh は必ず走る
        assert run.row["reuse_eligible_by_side"] == {"function1": True}
        assert run.row["analysis_source_by_side"] == {"function1": ANALYSIS_SOURCE_FRESH}
        shadow = run.row["shadow_fingerprints_by_side"]["function1"]
        assert shadow["matched"] is True
        assert shadow["fresh"] == shadow["reuse"]
        assert run.stage_inputs["analysis1"] is run.analysis1

    def test_shadow_construction_does_not_inflate_the_phase_segments(self, shadow_mode):
        fixture = _Fixture()
        run = fixture.run(changed1=True)

        # 比較用の構築は fresh 側の内訳時間を汚さない。
        assert run.refresh_calls == [("func1", 1), ("func1", 1)]
        assert run.row["seconds"]["analysis"] >= 0.0

    def test_mismatch_keeps_the_fresh_view_and_records_the_fallback(self, shadow_mode):
        fixture = _Fixture()
        # base とは異なる解析が返る = 再利用ビューが fresh と一致しない状況。
        divergent = create_mock_analysis("func1", return_type="ulong")
        divergent.analysis_notes.append("divergent fresh analysis")
        run = fixture.run(changed1=True, fresh_by_name={"func1": divergent})

        shadow = run.row["shadow_fingerprints_by_side"]["function1"]
        assert shadow["matched"] is False
        assert shadow["fresh"] != shadow["reuse"]
        # mismatch でも eligibility は validity 条件の判定結果のまま（観測を空振りさせない）。
        assert run.row["reuse_eligible_by_side"]["function1"] is True
        assert run.row["analysis_source_by_side"]["function1"] == REUSE_FALLBACK_SHADOW_MISMATCH
        # stage plan に渡るのは fresh 側のビュー。
        assert "divergent fresh analysis" in run.stage_inputs["analysis1"].analysis_notes
        assert run.result.error_message is None

    def test_unbuildable_comparison_fingerprint_falls_back_without_failing(
        self, shadow_mode
    ):
        fixture = _Fixture()
        real_fingerprint = semantic_fingerprint_of

        def _fingerprint(analysis):
            # 完成ビュー（仮説つき）の指紋だけ作れない状況。
            if getattr(analysis, "signature_hypotheses", None):
                return None
            return real_fingerprint(analysis)

        run = fixture.run(changed1=True, fingerprint_hook=_fingerprint)

        assert (
            run.row["analysis_source_by_side"]["function1"]
            == REUSE_FALLBACK_FINGERPRINT_UNAVAILABLE
        )
        assert run.row["shadow_fingerprints_by_side"]["function1"]["matched"] is False
        assert run.result.error_message is None

    def test_ineligible_sides_report_the_reason_without_a_shadow_comparison(
        self, shadow_mode
    ):
        fixture = _Fixture(seed1=False)
        run = fixture.run(changed1=True)

        assert run.analyze_calls == ["func1"]
        assert run.row["reuse_eligible_by_side"]["function1"] is False
        assert run.row["analysis_source_by_side"]["function1"] == REUSE_FALLBACK_NO_SNAPSHOT
        assert run.row["shadow_fingerprints_by_side"] == {}


class TestAuxiliaryPhasesUseTheSameReusePath:
    """P4-C / P4-A も同じ selective reanalysis を通る（実バイナリ target は探索しない）"""

    @pytest.fixture
    def checker(self):
        return EquivalenceChecker(
            timeout=5, debug=False, strategy="pairwise", canonical_decision_cutover=False
        )

    def _run_sat_tail(self, checker, *, programs, return_type_fix, p4a_result):
        """SAT が残る経路（P0 → P4-C → P4-A）を実際の workflow で流す。"""
        program1, program2 = programs
        analysis1 = create_mock_analysis("func1", return_type="ulong")
        analysis2 = create_mock_analysis("func2", return_type="uint")
        analyze_calls = []

        def _analyze(self, function_name, timeout):
            analyze_calls.append(function_name)
            return analysis1 if function_name == "func1" else analysis2

        def _refresh(self, analysis, timeout=60):
            return analysis

        def _stage_plan(*args, **kwargs):
            result = create_mock_result(
                is_equivalent=False, solver_status=SolverStatus.SAT
            )
            return result

        phase_handler = Mock(spec=PhaseHandler)
        phase_handler.should_fix_return_type.return_value = True
        phase_handler.run_phase2_return_type_fix.return_value = return_type_fix
        phase_handler.execute_phase.return_value = p4a_result
        phase_handler.run_phase4_mips64_retry.return_value = None
        checker.phase_handler = phase_handler

        with patch(f"{_ANALYZER}.analyze_function_by_name", _analyze):
            with patch(f"{_ANALYZER}.refresh_structural_recurrence_summary", _refresh):
                with patch.object(checker, "_run_stage_plan", side_effect=_stage_plan):
                    with patch(
                        "scripts.function_tracer_pcode.checker.checker.TypeFixer"
                    ) as fixer:
                        fixer.side_effect = lambda *args, **kwargs: Mock()
                        result = checker.check_from_binaries(
                            program1=program1,
                            program2=program2,
                            function_name1="func1",
                            function_name2="func2",
                            decompile_timeout=60,
                            save_formula=False,
                            retry_with_type_fix=True,
                        )
        return result.to_dict()["diagnostics"]["timings"]["phases"], analyze_calls

    def test_p4c_and_p4a_reuse_the_base_snapshot(self, checker, reuse_mode):
        programs = (
            VersionedMockProgram(name="binary1.exe"),
            VersionedMockProgram(name="binary2.exe"),
        )
        phases, analyze_calls = self._run_sat_tail(
            checker,
            programs=programs,
            # P4-C は binary2、P4-A は binary1 を変更する。
            return_type_fix=(True, False, True),
            p4a_result=PhaseResult(
                PhaseID.P4A_MIPS64_ABI,
                applied=True,
                retry_name="mips64_abi_fix",
                changed_binary1=True,
                changed_binary2=False,
            ),
        )

        by_phase = {row["phase"]: row for row in phases}
        assert set(by_phase) == {"P0_BASE", "P4C_RETURN_TYPE_FIX", "P4A_MIPS64_ABI"}
        assert by_phase["P4C_RETURN_TYPE_FIX"]["analysis_source_by_side"] == {
            "function2": ANALYSIS_SOURCE_REUSE
        }
        assert by_phase["P4A_MIPS64_ABI"]["analysis_source_by_side"] == {
            "function1": ANALYSIS_SOURCE_REUSE
        }
        # P0 の 2 回だけ。auxiliary phase も fresh 再解析を行っていない。
        assert analyze_calls == ["func1", "func2"]

    def test_p4c_and_p4a_fall_back_through_the_same_validity_gate(
        self, checker, reuse_mode
    ):
        # 世代を読めない Program では base を作れないので、auxiliary phase も fresh に倒れる。
        programs = (MockProgram(name="binary1.exe"), MockProgram(name="binary2.exe"))
        phases, analyze_calls = self._run_sat_tail(
            checker,
            programs=programs,
            return_type_fix=(True, False, True),
            p4a_result=PhaseResult(
                PhaseID.P4A_MIPS64_ABI,
                applied=True,
                retry_name="mips64_abi_fix",
                changed_binary1=True,
                changed_binary2=False,
            ),
        )

        by_phase = {row["phase"]: row for row in phases}
        assert by_phase["P4C_RETURN_TYPE_FIX"]["analysis_source_by_side"] == {
            "function2": REUSE_FALLBACK_NO_SNAPSHOT
        }
        assert by_phase["P4A_MIPS64_ABI"]["analysis_source_by_side"] == {
            "function1": REUSE_FALLBACK_NO_SNAPSHOT
        }
        assert analyze_calls == ["func1", "func2", "func2", "func1"]


class TestReuseDisabledCostsNothing:
    """kill switch: 無効なら base snapshot も再利用処理も作らない"""

    @pytest.fixture
    def disabled(self, monkeypatch):
        from scripts.function_tracer_pcode.config import settings

        monkeypatch.setattr(
            settings, "RETRY_ANALYSIS_REUSE_ENABLED", False, raising=False
        )

    def test_p0_does_not_build_a_base_snapshot(self, disabled):
        from scripts.function_tracer_pcode.checker.reanalysis import (
            _seed_retry_analysis_base,
        )

        program = VersionedMockProgram(name="binary1.exe")
        ctx = _make_ctx(program, VersionedMockProgram(name="binary2.exe"), None, None)
        with patch(
            "scripts.function_tracer_pcode.checker.reanalysis.build_retry_analysis_base"
        ) as build:
            _seed_retry_analysis_base(
                ctx, "function1", program, create_mock_analysis("func1")
            )
        assert build.call_count == 0
        assert ctx.retry_analysis_base1 is None

    def test_retry_runs_the_plain_fresh_path(self, disabled):
        fixture = _Fixture(seed1=False, seed2=False)
        run = fixture.run(changed1=True)

        assert run.analyze_calls == ["func1"]
        # 再利用専用の観測も残さない（無効時は従来処理と実質同じ）。
        assert run.row["reuse_eligible_by_side"] == {}
        assert run.row["analysis_source_by_side"] == {"function1": ANALYSIS_SOURCE_FRESH}
        assert run.row["shadow_fingerprints_by_side"] == {}

    def test_missing_setting_does_not_enable_reuse(self, monkeypatch):
        from scripts.function_tracer_pcode.checker import reanalysis
        from scripts.function_tracer_pcode.config import settings

        monkeypatch.delattr(settings, "RETRY_ANALYSIS_REUSE_ENABLED", raising=False)
        monkeypatch.delattr(settings, "RETRY_ANALYSIS_REUSE_SHADOW", raising=False)

        # 設定が欠けたら未検証の再利用を暗黙に有効化せず、fresh 側へ倒す。
        assert reanalysis._retry_reuse_enabled() is False
        assert reanalysis._retry_reuse_shadow_enabled() is True


class TestShadowCatchesRuntimeTypeDivergence:
    """強化した等価キーが shadow 比較で効くこと"""

    def test_runtime_type_divergence_is_reported_and_fresh_wins(self, shadow_mode):
        fixture = _Fixture()
        # fresh 側だけ runtime DataType のサイズが違う（記述文字列は同じ）状況。
        divergent = replace(
            fixture.raw1,
            parameters=[
                {
                    "name": "param_1",
                    "index": 0,
                    "data_type": "long",
                    "data_type_obj": MockDataType("long", 4, True),
                    "size": 8,
                    "is_signed": True,
                }
            ],
        )
        fixture.ctx.retry_analysis_base1 = build_retry_analysis_base(
            fixture.program1,
            replace(
                fixture.raw1,
                parameters=[
                    {
                        "name": "param_1",
                        "index": 0,
                        "data_type": "long",
                        "data_type_obj": MockDataType("long", 8, True),
                        "size": 8,
                        "is_signed": True,
                    }
                ],
            ),
        )
        run = fixture.run(changed1=True, fresh_by_name={"func1": divergent})

        shadow = run.row["shadow_fingerprints_by_side"]["function1"]
        assert shadow["matched"] is False
        assert shadow["mismatch_kind"] == "runtime_type_semantics"
        assert (
            run.row["analysis_source_by_side"]["function1"]
            == REUSE_FALLBACK_SHADOW_MISMATCH
        )
        # stage plan には fresh 側が渡る。
        assert run.stage_inputs["analysis1"].parameters[0]["data_type_obj"].getLength() == 4
        assert run.result.error_message is None

    def test_completed_recovery_proof_divergence_is_reported(self, shadow_mode):
        fixture = _Fixture()
        # fresh 側が retry 時に proof を作り直し、base は P0 時点のものを持つ状況。
        divergent = replace(
            fixture.raw1,
            completed_recovery_proof_ids=(("recovery_proof_v1", "func1", 7),),
        )
        run = fixture.run(changed1=True, fresh_by_name={"func1": divergent})

        shadow = run.row["shadow_fingerprints_by_side"]["function1"]
        assert shadow["matched"] is False
        assert shadow["mismatch_kind"] == "completed_recovery_proofs"
        assert (
            run.row["analysis_source_by_side"]["function1"]
            == REUSE_FALLBACK_SHADOW_MISMATCH
        )

    def test_matching_views_still_report_no_mismatch_kind(self, shadow_mode):
        fixture = _Fixture()
        run = fixture.run(changed1=True)

        shadow = run.row["shadow_fingerprints_by_side"]["function1"]
        assert shadow["matched"] is True
        assert shadow["mismatch_kind"] is None


class TestBaseSeedingThroughTheWorkflow:
    """P0 の raw 解析が base になり、retry で再利用されるまで"""

    @pytest.fixture
    def checker(self):
        return EquivalenceChecker(
            timeout=5, debug=False, strategy="pairwise", canonical_decision_cutover=False
        )

    def _run(self, checker, *, programs, analyses):
        program1, program2 = programs
        analysis1, analysis2 = analyses
        analyze_calls = []

        def _analyze(self, function_name, timeout):
            analyze_calls.append(function_name)
            return analysis1 if function_name == "func1" else analysis2

        def _refresh(self, analysis, timeout=60):
            return analysis

        def _execute_phase(spec, ctx, fixer1, fixer2, params_func):
            if spec.phase_id is PhaseID.P1_SIGNEDNESS:
                ctx.analysis1 = ctx.analysis1.with_signature_hypothesis(_hypothesis())
                return PhaseResult(
                    spec.phase_id,
                    applied=True,
                    retry_name="signedness_fix",
                    changed_binary1=True,
                )
            return PhaseResult(spec.phase_id, applied=False, retry_name="")

        def _stage_plan(*args, **kwargs):
            return create_mock_result(
                is_equivalent=None, solver_status=SolverStatus.UNKNOWN
            )

        phase_handler = Mock(spec=PhaseHandler)
        phase_handler.execute_phase.side_effect = _execute_phase
        phase_handler.should_retry.side_effect = [True, False]
        phase_handler.get_retry_reason.side_effect = ["UNKNOWN", "UNKNOWN"]
        phase_handler.run_phase4_mips64_retry.return_value = None
        checker.phase_handler = phase_handler

        with patch(f"{_ANALYZER}.analyze_function_by_name", _analyze):
            with patch(f"{_ANALYZER}.refresh_structural_recurrence_summary", _refresh):
                with patch.object(checker, "_run_stage_plan", side_effect=_stage_plan):
                    with patch(
                        "scripts.function_tracer_pcode.checker.checker.TypeFixer"
                    ) as fixer:
                        fixer.side_effect = lambda *args, **kwargs: Mock()
                        result = checker.check_from_binaries(
                            program1=program1,
                            program2=program2,
                            function_name1="func1",
                            function_name2="func2",
                            decompile_timeout=60,
                            save_formula=False,
                            retry_with_type_fix=True,
                        )
        return result, analyze_calls

    def test_retry_reuses_the_p0_base_instead_of_reanalysing(self, checker, reuse_mode):
        programs = (
            VersionedMockProgram(name="binary1.exe"),
            VersionedMockProgram(name="binary2.exe"),
        )
        analyses = (
            create_mock_analysis("func1", return_type="ulong"),
            create_mock_analysis("func2", return_type="uint"),
        )
        result, analyze_calls = self._run(checker, programs=programs, analyses=analyses)

        # P0 の 2 回だけ。P1 の変更側は base から作り直している。
        assert analyze_calls == ["func1", "func2"]
        rows = result.diagnostics["phases"]
        retry_rows = [row for row in rows if row["phase"] == "P1_SIGNEDNESS"]
        assert retry_rows[0]["analysis_source_by_side"] == {
            "function1": ANALYSIS_SOURCE_REUSE
        }
        assert retry_rows[0]["reuse_eligible_by_side"] == {"function1": True}

    def test_shadow_mode_keeps_the_fresh_reanalysis(self, checker, shadow_mode):
        programs = (
            VersionedMockProgram(name="binary1.exe"),
            VersionedMockProgram(name="binary2.exe"),
        )
        analyses = (
            create_mock_analysis("func1", return_type="ulong"),
            create_mock_analysis("func2", return_type="uint"),
        )
        result, analyze_calls = self._run(checker, programs=programs, analyses=analyses)

        assert analyze_calls == ["func1", "func2", "func1"]
        rows = result.diagnostics["phases"]
        retry_rows = [row for row in rows if row["phase"] == "P1_SIGNEDNESS"]
        assert retry_rows[0]["analysis_source_by_side"] == {
            "function1": ANALYSIS_SOURCE_FRESH
        }
        assert (
            retry_rows[0]["shadow_fingerprints_by_side"]["function1"]["matched"] is True
        )

    def test_programs_without_the_generation_api_keep_the_current_behaviour(
        self, checker, reuse_mode
    ):
        programs = (MockProgram(name="binary1.exe"), MockProgram(name="binary2.exe"))
        analyses = (
            create_mock_analysis("func1", return_type="ulong"),
            create_mock_analysis("func2", return_type="uint"),
        )
        result, analyze_calls = self._run(checker, programs=programs, analyses=analyses)

        # 世代を読めない Program では base 自体を作らないので、従来どおり毎回 fresh。
        assert analyze_calls == ["func1", "func2", "func1"]
        rows = result.diagnostics["phases"]
        retry_rows = [row for row in rows if row["phase"] == "P1_SIGNEDNESS"]
        assert retry_rows[0]["analysis_source_by_side"] == {
            "function1": REUSE_FALLBACK_NO_SNAPSHOT
        }
        assert retry_rows[0]["reuse_eligible_by_side"] == {"function1": False}

    def test_phase_rows_keep_the_pr_107_a_contract(self, checker, reuse_mode):
        programs = (
            VersionedMockProgram(name="binary1.exe"),
            VersionedMockProgram(name="binary2.exe"),
        )
        analyses = (
            create_mock_analysis("func1", return_type="ulong"),
            create_mock_analysis("func2", return_type="uint"),
        )
        result, _ = self._run(checker, programs=programs, analyses=analyses)

        rows = result.diagnostics["phases"]
        attempts = result.debug_trace.to_dict()["attempts"]
        by_attempt = {row["attempt_id"] for row in rows if row["attempt_id"] is not None}
        assert by_attempt == {attempt["attempt_id"] for attempt in attempts}
        for row in rows:
            # 新しい観測は追加であって、既存 field を置き換えない。
            assert set(row) >= {
                "schema",
                "phase",
                "attempt_id",
                "applied",
                "changed_sides",
                "reanalyzed_sides",
                "seconds",
                "reason_before",
                "reason_after",
                "reuse_eligible_by_side",
                "analysis_source_by_side",
                "shadow_fingerprints_by_side",
            }

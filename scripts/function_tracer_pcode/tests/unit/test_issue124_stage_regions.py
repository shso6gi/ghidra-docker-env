# -*- coding: utf-8 -*-
"""Issue #124 PR-124-A: `check` 内 sub-stage の計測契約。

M-107（#107）が stage plan の 637.05s のうち 415.76s を帰属できなかったのは、
`run_obligation_branch_plan` が branch ごとに `check()` を呼ぶのに、記録が最後の
1 回分しか残らなかったため。ここで固定するのは「その残差が機械的に閉じること」で、
判定の意味は 1 つも変えない:

* region 階層の `seconds_inclusive` / `seconds_exclusive` / `calls`
* `obligation_build` が check の内側と外側の両方で起きること（両配置で恒等式が閉じる）
* solver の 4 counter が入れ子で二重計上されないこと
* `boundary_seconds.finish` の内訳（authority finalize / conditional lane / 残差）
* diagnostics が上書きではなく merge されること
* 診断を足しても semantic projection は変わらないこと（独立 finalization 2 本）
"""
import concurrent.futures
import gc
import time
from types import SimpleNamespace

import pytest

from scripts.function_tracer_pcode.checker.diagnostics import (
    AnalysisTimer,
    StageClock,
    attach_stage_timing,
    result_diagnostics_payload,
)
from scripts.function_tracer_pcode.checker.reanalysis import _attach_analysis_diagnostics
from scripts.function_tracer_pcode.core.stage_clock import (
    identity_tolerance,
    open_stage_region,
    region_identity_rows,
    split_region_by_ancestor,
    stage_region,
)
from scripts.function_tracer_pcode.authority.seal_work import SealWorkBudget

# 計測の分解能に依存しない程度に長い区間（合計しても 1 秒未満）。
TICK = 0.02


def _burn(seconds: float = TICK) -> None:
    """monotonic に必ず進む区間を作る（sleep はスケジューラに返す）。"""
    time.sleep(seconds)


def _node(regions, *path):
    node = regions[path[0]]
    for name in path[1:]:
        node = node["children"][name]
    return node


# --------------------------------------------------------------------------
# 1. region の inclusive / exclusive / calls
# --------------------------------------------------------------------------

def test_stage_clock_regions_exclusive_inclusive_calls():
    clock = StageClock()
    with clock.scope():
        with stage_region("outer"):
            _burn()
            with stage_region("inner"):
                _burn()
                # 同名 region への再入: 時間は最外の区間が持ち、回数だけ増える。
                with stage_region("inner"):
                    _burn()
            # 例外で抜けても区間は閉じる。
            with pytest.raises(RuntimeError):
                with stage_region("raiser"):
                    _burn()
                    raise RuntimeError("boom")
        # 同じ名前をもう一度開けば合算される（並びであって入れ子ではない）。
        with stage_region("outer"):
            _burn()

    regions = clock.snapshot()["regions"]
    outer = _node(regions, "outer")
    inner = _node(regions, "outer", "inner")
    raiser = _node(regions, "outer", "raiser")

    assert outer["calls"] == 2 and outer["reentrant_calls"] == 0
    # inner は 2 回入ったが独立区間は 1 本（再入分は最外に含む）。
    assert inner["calls"] == 2 and inner["reentrant_calls"] == 1
    assert raiser["calls"] == 1
    assert raiser["seconds_inclusive"] >= TICK

    # 再入分を二重計上していない: inner の inclusive は 2 tick 程度で、
    # 3 tick（再入を別区間として数えた場合）にはならない。
    assert 2 * TICK <= inner["seconds_inclusive"] < 3 * TICK
    # exclusive = inclusive − 直接子の inclusive 合計。
    assert outer["seconds_exclusive"] == pytest.approx(
        outer["seconds_inclusive"]
        - inner["seconds_inclusive"]
        - raiser["seconds_inclusive"],
        abs=1e-5,
    )
    assert outer["seconds_inclusive"] >= 5 * TICK


def test_stage_region_is_a_noop_without_an_active_clock():
    clock = StageClock()
    # scope の外なので、どこにも記録されない（例外も出ない）。
    with stage_region("orphan"):
        _burn(0.001)
    handle = open_stage_region("orphan")
    handle.close()
    assert clock.snapshot().get("regions") is None


def test_worker_thread_regions_do_not_leak_into_parent():
    clock = StageClock()

    def worker():
        # worker は空 context で始まるので clock が見えない = no-op。
        with stage_region("worker_only"):
            _burn()
        return "done"

    with clock.scope():
        with stage_region("parent"):
            with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
                assert [f.result() for f in [pool.submit(worker), pool.submit(worker)]] == [
                    "done",
                    "done",
                ]

    regions = clock.snapshot()["regions"]
    assert set(regions) == {"parent"}
    assert "children" not in regions["parent"]
    assert regions["parent"]["seconds_exclusive"] == regions["parent"]["seconds_inclusive"]


# --------------------------------------------------------------------------
# 2. 恒等式 A / B / C（obligation_build の両配置）
# --------------------------------------------------------------------------

def _identities(rows):
    return {(row["identity"], row["region"]): row for row in rows}


def test_stage_plan_identities_close_with_obligation_build_outside_check():
    """配置 A: obligation の構築が check の外（stage runner 相当）で起きる場合。"""
    clock = StageClock()
    with clock.scope():
        with stage_region("branch_plan_orchestration"):
            with stage_region("obligation_build"):      # runtime の生成 / schedule
                _burn()
            _burn()                                     # branch activation / lease
            for _ in range(2):
                with stage_region("check"):
                    with stage_region("strategy_branch"):
                        _burn()
                    _burn()
    stages = clock.snapshot()
    orchestration = _node(stages["regions"], "branch_plan_orchestration")
    phases = [{"seconds": {"stage_plan": orchestration["seconds_inclusive"]}}]

    rows = _identities(region_identity_rows(stages, phases))
    assert all(row["within_tolerance"] for row in rows.values())
    assert ("A", "branch_plan_orchestration") in rows
    assert ("B", "branch_plan_orchestration") in rows
    assert ("C", "branch_plan_orchestration.check") in rows

    split = stages["obligation_build"]
    assert split["outside_check"]["seconds"] >= TICK
    assert split["outside_check"]["calls"] == 1
    assert split["inside_check"] == {"seconds": 0.0, "calls": 0}

    # orchestration の exclusive から check と obligation_build を二重に引いていない。
    check = _node(stages["regions"], "branch_plan_orchestration", "check")
    assert orchestration["seconds_exclusive"] == pytest.approx(
        orchestration["seconds_inclusive"]
        - check["seconds_inclusive"]
        - split["outside_check"]["seconds"],
        abs=1e-5,
    )
    assert orchestration["seconds_exclusive"] >= TICK


def test_stage_plan_identities_close_with_obligation_build_inside_check():
    """配置 B: obligation の構築が check の内側（prepare_strategy_runtime 相当）。"""
    clock = StageClock()
    with clock.scope():
        with stage_region("branch_plan_orchestration"):
            _burn()
            for _ in range(2):
                with stage_region("check"):
                    with stage_region("obligation_build"):
                        _burn()
                    with stage_region("strategy_branch"):
                        _burn()
    stages = clock.snapshot()
    orchestration = _node(stages["regions"], "branch_plan_orchestration")
    check = _node(stages["regions"], "branch_plan_orchestration", "check")
    phases = [{"seconds": {"stage_plan": orchestration["seconds_inclusive"]}}]

    rows = _identities(region_identity_rows(stages, phases))
    assert all(row["within_tolerance"] for row in rows.values())

    split = stages["obligation_build"]
    assert split["inside_check"]["calls"] == 2
    assert split["inside_check"]["seconds"] >= 2 * TICK
    assert split["outside_check"] == {"seconds": 0.0, "calls": 0}

    # check 内の obligation_build は check の内訳であり、orchestration からは
    # 差し引かない（差し引くと同じ時間を 2 回引くことになる）。
    assert orchestration["seconds_exclusive"] == pytest.approx(
        orchestration["seconds_inclusive"] - check["seconds_inclusive"], abs=1e-5
    )
    assert orchestration["seconds_exclusive"] == pytest.approx(TICK, abs=TICK)
    assert check["seconds_exclusive"] == pytest.approx(
        check["seconds_inclusive"]
        - split["inside_check"]["seconds"]
        - _node(
            stages["regions"], "branch_plan_orchestration", "check", "strategy_branch"
        )["seconds_inclusive"],
        abs=1e-5,
    )


def test_report_total_of_obligation_build_is_sum_not_identity_term():
    clock = StageClock()
    with clock.scope():
        with stage_region("branch_plan_orchestration"):
            with stage_region("obligation_build"):
                _burn()
            with stage_region("check"):
                with stage_region("obligation_build"):
                    _burn()
    stages = clock.snapshot()
    split = stages["obligation_build"]

    assert split["total_seconds"] == pytest.approx(
        split["inside_check"]["seconds"] + split["outside_check"]["seconds"], abs=1e-6
    )
    assert split["total_calls"] == 2
    # report 用の合計であって恒等式の項ではない、という契約を payload に残す。
    assert split["total_is_report_metric_not_identity_term"] is True

    # 合計を恒等式の項に混ぜると閉じなくなることを直接示す。
    orchestration = _node(stages["regions"], "branch_plan_orchestration")
    check = _node(stages["regions"], "branch_plan_orchestration", "check")
    wrong_residual = (
        orchestration["seconds_inclusive"]
        - check["seconds_inclusive"]
        - split["total_seconds"]
        - orchestration["seconds_exclusive"]
    )
    assert abs(wrong_residual) > 0.0
    assert all(row["within_tolerance"] for row in region_identity_rows(stages))


def test_identity_tolerance_is_relative_not_exact_float_equality():
    # 絶対 0.05 s と相対 1 % の大きい方。厳密 float 一致を条件にしない。
    assert identity_tolerance(0.0, 0.0) == pytest.approx(0.05)
    assert identity_tolerance(600.0, 599.0) == pytest.approx(6.0)
    rows = region_identity_rows(
        {
            "regions": {
                "branch_plan_orchestration": {
                    "seconds_inclusive": 100.0,
                    "seconds_exclusive": 100.0,
                    "calls": 1,
                    "reentrant_calls": 0,
                }
            }
        },
        [{"seconds": {"stage_plan": 100.4}}],
    )
    assert _identities(rows)[("A", "branch_plan_orchestration")]["within_tolerance"]
    rows = region_identity_rows(
        {
            "regions": {
                "branch_plan_orchestration": {
                    "seconds_inclusive": 100.0,
                    "seconds_exclusive": 100.0,
                    "calls": 1,
                    "reentrant_calls": 0,
                }
            }
        },
        [{"seconds": {"stage_plan": 130.0}}],
    )
    assert not _identities(rows)[("A", "branch_plan_orchestration")]["within_tolerance"]


def test_stage_clock_scope_covers_multiple_checks_and_nested_regions():
    """1 つの scope で複数 check を回し、子孫の obligation_build も二重計上しない。"""
    clock = StageClock()
    with clock.scope():
        # scope は stage plan の外から開いている（解析はその外側で起きる）。
        with stage_region("analysis_regions"), stage_region("function1"):
            with stage_region("trace_returns"):
                _burn()
        with stage_region("branch_plan_orchestration"):
            for _ in range(3):
                with stage_region("check"):
                    with stage_region("strategy_branch"):
                        # 直接子ではない（孫）の obligation_build。
                        with stage_region("obligation_build"):
                            _burn()
                        with stage_region("query_build"):
                            _burn()
    stages = clock.snapshot()
    regions = stages["regions"]
    check = _node(regions, "branch_plan_orchestration", "check")
    strategy = _node(regions, "branch_plan_orchestration", "check", "strategy_branch")

    assert check["calls"] == 3
    assert stages["region_totals"]["obligation_build"]["calls"] == 3
    assert stages["obligation_build"]["inside_check"]["calls"] == 3
    # C は check の直接子だけで閉じる（孫は strategy_branch 側に含まれる）。
    assert check["seconds_exclusive"] == pytest.approx(
        check["seconds_inclusive"] - strategy["seconds_inclusive"], abs=1e-5
    )
    assert all(row["within_tolerance"] for row in region_identity_rows(stages))
    # 解析 region は stage plan の外に積まれている。
    assert _node(regions, "analysis_regions", "function1", "trace_returns")["calls"] == 1


def test_split_region_by_ancestor_reports_nothing_when_region_absent():
    assert split_region_by_ancestor({}, "obligation_build", "check") is None


# --------------------------------------------------------------------------
# 3. diagnostics の merge
# --------------------------------------------------------------------------

def test_attach_analysis_diagnostics_merges():
    timer = AnalysisTimer()
    timer.timed("function1", lambda: _burn(0.001))
    checker = SimpleNamespace(_analysis_timer=timer)
    result = SimpleNamespace(
        diagnostics={
            "phases": [{"schema": "phase-timing-v1", "phase": "P0_BASE"}],
            "boundary_seconds": {"finish": 1.0},
            "conditional_lane": {"status": "not_started"},
        }
    )

    _attach_analysis_diagnostics(checker, result)

    # 既存の診断が残っている（上書きされていない）。
    assert result.diagnostics["phases"] == [{"schema": "phase-timing-v1", "phase": "P0_BASE"}]
    assert result.diagnostics["boundary_seconds"] == {"finish": 1.0}
    assert result.diagnostics["conditional_lane"] == {"status": "not_started"}
    # AnalysisTimer の観測が足されている。
    assert result.diagnostics["analysis_seconds"]["function1"] > 0.0
    assert "expressions" in result.diagnostics


def test_attach_stage_timing_merges_and_keeps_existing_diagnostics():
    clock = StageClock()
    clock.mark("jvm_start", 1.0)
    with clock.scope():
        with stage_region("check"):
            _burn()
    result = SimpleNamespace(
        diagnostics={"analysis_seconds": {"function1": 1.5}, "phases": [{"phase": "P0_BASE"}]},
        total_time=3.0,
        debug_trace=None,
        solver_results=[],
        pairwise_stats={},
        stage_path=["P0_BASE"],
    )

    attach_stage_timing(result, clock)

    assert result.diagnostics["analysis_seconds"] == {"function1": 1.5}
    assert result.diagnostics["phases"] == [{"phase": "P0_BASE"}]
    stages = result.diagnostics["stages"]
    assert stages["schema"] == "pair-stage-timing-v1"
    assert stages["seconds"] == {"jvm_start": 1.0}
    assert stages["regions"]["check"]["calls"] == 1
    # process 単位の counter（worker thread から加算されるので region では
    # 測れない）も同じ block に載る。
    assert set(stages["solver"]) == {
        "logical_queries",
        "backend_runs",
        "backend_seconds",
        "wall_seconds",
    }

    # 結果 JSON の診断 payload にも region がそのまま出る。
    payload = result_diagnostics_payload(result)
    assert payload["timings"]["stages"]["regions"]["check"]["calls"] == 1
    assert payload["timings"]["analysis_seconds"] == {"function1": 1.5}


def test_attach_stage_timing_records_the_identity_rows_with_the_phase_rows():
    """恒等式の実測値は結果 JSON 単体で確認できる（phase 行は添付済み）。"""
    clock = StageClock()
    with clock.scope():
        with stage_region("branch_plan_orchestration"):
            with stage_region("check"):
                _burn()
            _burn()
    orchestration_seconds = clock.snapshot()["regions"][
        "branch_plan_orchestration"
    ]["seconds_inclusive"]
    result = SimpleNamespace(
        diagnostics={
            "phases": [
                {"schema": "phase-timing-v1", "seconds": {"stage_plan": orchestration_seconds / 2}},
                {"schema": "phase-timing-v1", "seconds": {"stage_plan": orchestration_seconds / 2}},
            ]
        }
    )
    attach_stage_timing(result, clock)

    rows = {(row["identity"], row["region"]): row for row in result.diagnostics["stages"]["identities"]}
    assert {identity for identity, _region in rows} == {"A", "B", "C"}
    assert all(row["within_tolerance"] for row in rows.values())
    # A は phase 行の合計と比べる（最後の 1 phase だけではない）。
    assert rows[("A", "branch_plan_orchestration")]["left"] == pytest.approx(
        orchestration_seconds, abs=1e-5
    )


# --------------------------------------------------------------------------
# 4. solver の 4 counter
# --------------------------------------------------------------------------

def _solver_class(label, status, delay):
    from scripts.function_tracer_pcode.smt.interface import SolverResult

    class _FakeSolver:
        name = label

        def __init__(self, timeout=10):
            self.timeout = timeout

        def check_availability(self):
            return True, "available"

        def set_timeout(self, seconds):
            self.timeout = seconds

        def check_equivalence_direct(self, smt_script, cancellation_token=None):
            time.sleep(delay)
            return SolverResult(solver_name=label, status=status, elapsed_time=delay)

    return _FakeSolver


def test_solver_counters_do_not_double_count():
    from scripts.function_tracer_pcode.smt.interface import SolverStatus
    from scripts.function_tracer_pcode.smt.parallel import (
        ParallelSolverRunner,
        reset_solver_counters,
        solver_counter_snapshot,
    )

    def _measure(run):
        """実時間を測る区間の外で世代 GC を済ませてから走らせる。

        この test は 50ms の sleep に対して「2 倍未満」を主張する。suite を通しで
        走らせると、測る区間のちょうど中で第 2 世代の回収（27 万 object 規模）が
        起きることがあり、その 20-30ms が余裕をほぼ食い潰す。どの test が幾つ
        object を作るかで回収の位相が変わるので、**この test と無関係な変更**で
        赤くなる。回収を先に済ませておけば、測っているものは変わらないまま、
        位相への依存だけが消える（主張は緩めない）。
        """

        gc.collect()
        reset_solver_counters()
        run()
        return solver_counter_snapshot()

    delay = 0.05
    classes = [
        _solver_class("s1", SolverStatus.UNKNOWN, delay),
        _solver_class("s2", SolverStatus.UNKNOWN, delay),
        _solver_class("s3", SolverStatus.UNKNOWN, delay),
    ]
    runner = ParallelSolverRunner(timeout=5, solver_classes=classes)

    parallel = _measure(lambda: runner.run_parallel("(check-sat)"))
    # 論理的な問い合わせは 1 回、backend は 3 回。
    assert parallel["logical_queries"] == 1
    assert parallel["backend_runs"] == 3
    # backend の合計は 3 本分、実時間は 1 本分に近い（並列なので）。
    assert parallel["backend_seconds"] >= 2.5 * delay
    assert parallel["wall_seconds"] >= delay
    # 「wrapper 時間 × 子の数」で数えていたらここで落ちる。
    assert parallel["wall_seconds"] < 2 * delay
    assert parallel["wall_seconds"] < parallel["backend_seconds"]

    # run_sequential: 最初の確定結果で打ち切るので backend は 1 回だけ。
    sequential_runner = ParallelSolverRunner(
        timeout=5,
        solver_classes=[
            _solver_class("d1", SolverStatus.UNSAT, delay),
            _solver_class("d2", SolverStatus.UNSAT, delay),
        ],
    )
    sequential = _measure(lambda: sequential_runner.run_sequential("(check-sat)"))
    assert sequential["logical_queries"] == 1
    assert sequential["backend_runs"] == 1
    assert sequential["wall_seconds"] >= delay
    # 順次実行では wall は backend を包む（入れ子で二重加算していない）。
    assert sequential["wall_seconds"] >= sequential["backend_seconds"]
    assert sequential["wall_seconds"] < 2 * delay

    # orchestration の外から直接呼ばれた run_single も論理問い合わせ 1 回。
    direct = _measure(lambda: runner.run_single(runner._solvers[0], "(check-sat)"))
    assert direct == {
        "logical_queries": 1,
        "backend_runs": 1,
        "backend_seconds": direct["backend_seconds"],
        "wall_seconds": direct["wall_seconds"],
    }
    assert direct["backend_seconds"] >= delay
    assert direct["wall_seconds"] >= delay
    reset_solver_counters()


def test_solver_counters_are_pulled_into_the_stage_block():
    from scripts.function_tracer_pcode.smt.interface import SolverStatus
    from scripts.function_tracer_pcode.smt.parallel import (
        ParallelSolverRunner,
        reset_solver_counters,
    )

    reset_solver_counters()
    runner = ParallelSolverRunner(
        timeout=5, solver_classes=[_solver_class("s1", SolverStatus.UNSAT, 0.01)]
    )
    runner.run_parallel("(check-sat)")
    result = SimpleNamespace(diagnostics={})
    attach_stage_timing(result, StageClock())
    assert result.diagnostics["stages"]["solver"]["logical_queries"] == 1
    assert result.diagnostics["stages"]["solver"]["backend_runs"] == 1
    reset_solver_counters()


# --------------------------------------------------------------------------
# 5. boundary_seconds の内訳
# --------------------------------------------------------------------------

def _boundary_environment(monkeypatch, *, finalize_seconds, lane_seconds, finish_raises=False):
    """`finish` 区間の内訳だけを見るための最小構成。

    判定そのもの（reconciliation / receipt の添付）は他の test が固定しているので、
    ここでは計時の対象区間だけを本物の制御フローで通す。
    """
    from scripts.function_tracer_pcode.authority.lifecycle import production_boundary
    from scripts.function_tracer_pcode.authority.lifecycle.pilot import (
        ProductionDualWritePilotConnector,
    )
    from scripts.function_tracer_pcode.authority.lifecycle.reducer import ShadowLifecycleReducer
    from scripts.function_tracer_pcode.authority.process.supervisor import (
        PROCESS_DURABLE_REASON_REGISTRY,
        PROCESS_DURABLE_RECOVERY_REGISTRY,
    )

    connector = ProductionDualWritePilotConnector(
        ShadowLifecycleReducer(
            reason_registry=PROCESS_DURABLE_REASON_REGISTRY,
            recovery_registry=PROCESS_DURABLE_RECOVERY_REGISTRY,
        )
    )
    checker = SimpleNamespace(
        v2_dual_write_pilot_connector=connector,
        observation_contract=SimpleNamespace(contract_id="contract-1"),
        _active_binary_content_identities=(None, None),
    )
    result = SimpleNamespace(
        is_equivalent=True,
        error_message=None,
        failure_status=None,
        failure_message=None,
        unknown_reasons=[],
        unknown_recovery_actions=[],
        diagnostics={},
        is_timeout=lambda: False,
    )
    monkeypatch.setattr(
        production_boundary, "_run_legacy_check_from_binaries",
        lambda *_a, **_k: result,
    )

    def fake_finish(*_args, **_kwargs):
        time.sleep(finalize_seconds)
        if finish_raises:
            raise RuntimeError("finish failed")
        return SimpleNamespace(
            to_dict=lambda: {},
            pilot_result=SimpleNamespace(
                legacy_outcome_after="EQUIVALENT",
                candidate=SimpleNamespace(decision_receipt=object()),
                reduction=SimpleNamespace(projection=object()),
            ),
        )

    monkeypatch.setattr(production_boundary, "_profiled_finish", fake_finish)
    monkeypatch.setattr(
        production_boundary, "_reconcile_legacy_and_canonical_candidate",
        lambda **kwargs: (kwargs["candidate_receipt"], None),
    )
    monkeypatch.setattr(production_boundary, "attach_canonical_decision", lambda *_a, **_k: None)
    monkeypatch.setattr(production_boundary, "attach_canonical_relations", lambda *_a, **_k: None)

    def fake_lane(*_args, **_kwargs):
        time.sleep(lane_seconds)

    monkeypatch.setattr(production_boundary, "_run_conditional_lane", fake_lane)
    return production_boundary, checker


def test_boundary_seconds_split_authority_and_conditional_lane(monkeypatch):
    boundary, checker = _boundary_environment(
        monkeypatch, finalize_seconds=0.05, lane_seconds=0.10
    )
    actual = boundary.run_check_from_binaries_with_v2_pilot(
        checker, object(), object(), "left", "right"
    )
    seconds = actual.diagnostics["boundary_seconds"]

    # 既存 key は全区間のまま（後方互換）。
    assert set(seconds) >= {
        "session_begin", "check_body", "finish",
        "authority_finalize", "conditional_lane", "finish_other",
    }
    assert seconds["authority_finalize"] == pytest.approx(0.05, abs=0.03)
    assert seconds["conditional_lane"] == pytest.approx(0.10, abs=0.03)
    assert seconds["finish"] >= seconds["authority_finalize"] + seconds["conditional_lane"]
    assert seconds["finish_other"] == pytest.approx(
        seconds["finish"] - seconds["authority_finalize"] - seconds["conditional_lane"],
        abs=1e-5,
    )
    # `finish` 全体を authority 固有コストと読むと lane の分だけ過大になる。
    assert seconds["finish"] > 1.5 * seconds["authority_finalize"]


def test_boundary_seconds_record_authority_finalize_even_when_finish_raises(monkeypatch):
    boundary, checker = _boundary_environment(
        monkeypatch, finalize_seconds=0.05, lane_seconds=0.10, finish_raises=True
    )
    actual = boundary.run_check_from_binaries_with_v2_pilot(
        checker, object(), object(), "left", "right"
    )
    seconds = actual.diagnostics["boundary_seconds"]
    assert seconds["authority_finalize"] == pytest.approx(0.05, abs=0.03)
    # lane は回っていないので 0（「不明」と「0」を混同しない）。
    assert seconds["conditional_lane"] == 0.0
    assert seconds["finish_other"] >= 0.0


# --------------------------------------------------------------------------
# 6. production の計測点（どこに region が付くか）と、判定への非干渉
# --------------------------------------------------------------------------

def _real_checker():
    from scripts.function_tracer_pcode.checker.checker import EquivalenceChecker

    return EquivalenceChecker(
        strategy="monolithic", timeout=5, monolithic_timeout=5,
        canonical_decision_cutover=False,
    )


def _reason_ids(result):
    return sorted(
        str(getattr(reason, "reason_id", reason))
        for reason in getattr(result, "unknown_reasons", ()) or ()
    )


def test_production_check_opens_the_documented_regions():
    from scripts.function_tracer_pcode.tests.unit.test_monolithic_region_split import _analysis

    clock = StageClock()
    with clock.scope():
        with stage_region("branch_plan_orchestration"):
            _real_checker().check(_analysis("left", 7), _analysis("right", 7))

    stages = clock.snapshot()
    check = _node(stages["regions"], "branch_plan_orchestration", "check")
    # `check` は stage plan の直下 1 段に積まれ、回数は実際の呼び出し回数。
    assert check["calls"] == 1 and check["reentrant_calls"] == 0
    assert {
        "preflight_projection", "strategy_branch", "unknown_refinement", "result_assembly"
    } <= set(check["children"])
    # obligation の構築は（この経路では）check の内側で起きる。
    assert stages["obligation_build"]["inside_check"]["calls"] >= 1
    assert stages["obligation_build"]["outside_check"]["calls"] == 0
    # query 構築も計測されている。
    assert stages["region_totals"]["query_build"]["calls"] >= 1
    # 直接子だけで閉じる（B / C）。
    assert all(row["within_tolerance"] for row in region_identity_rows(stages))


def test_check_regions_do_not_change_outcome_or_reasons():
    from scripts.function_tracer_pcode.tests.unit.test_monolithic_region_split import _analysis

    without_clock = _real_checker().check(_analysis("left", 7), _analysis("right", 7))

    clock = StageClock()
    with clock.scope():
        with stage_region("branch_plan_orchestration"):
            with_clock = _real_checker().check(_analysis("left", 7), _analysis("right", 7))

    assert with_clock.is_equivalent == without_clock.is_equivalent
    assert _reason_ids(with_clock) == _reason_ids(without_clock)
    assert with_clock.error_message == without_clock.error_message
    assert with_clock.failure_status == without_clock.failure_status
    assert list(with_clock.stage_path or ()) == list(without_clock.stage_path or ())
    assert list(with_clock.unknown_recovery_actions or ()) == list(
        without_clock.unknown_recovery_actions or ()
    )
    # region を開いた側だけが観測を持つ（観測の有無が判定に出ていない）。
    assert clock.snapshot()["regions"]["branch_plan_orchestration"]["calls"] == 1


def test_decompile_is_measured_as_a_region_at_the_analysis_entry_points():
    """decompile は broker ではなく解析側の呼び出し口で region 化してある。

    broker（`ghidra/decompilation_broker.py`）は Phase 7 の producer site を持つ
    追跡 artifact に紐づくので、この PR では触らない。
    """
    import inspect

    from scripts.function_tracer_pcode.analysis.returns import (
        analyze_function,
        analyzer,
        call_recovery,
    )

    sources = [
        inspect.getsource(analyzer.ReturnAnalyzer._decompile_with_broker),
        inspect.getsource(analyze_function._impl_analyze_function),
        inspect.getsource(analyze_function._impl_refresh_structural_recurrence_summary),
        inspect.getsource(call_recovery),
    ]
    assert all('stage_region("decompile")' in source for source in sources)


# --------------------------------------------------------------------------
# 7. digest: preimage は変わるが semantic projection は変わらない
# --------------------------------------------------------------------------

def _result_for_preimage():
    from scripts.function_tracer_pcode.checker.result import EquivalenceResult

    return EquivalenceResult(
        is_equivalent=True,
        function1_name="f",
        function2_name="f",
        binary1_name="left",
        binary2_name="right",
        solver_results=None,
    )


def test_stages_change_preimage_but_no_semantic_field(tmp_path, monkeypatch):
    from scripts.function_tracer_pcode.authority.decision.canonical_result import (
        validate_canonical_result_finalization_bundle,
    )
    from scripts.function_tracer_pcode.tests.unit._finalization_support import (
        _independent_finalization,
    )

    bundle_key = tmp_path / "canonical-bundle.key"
    bundle_key.write_bytes(b"k" * 32)
    monkeypatch.setenv("UNKNOWN_TAXONOMY_V2_SUPERVISOR_KEY_ID", "issue124-test-key")
    monkeypatch.setenv("UNKNOWN_TAXONOMY_V2_SUPERVISOR_KEY_FILE", str(bundle_key))
    monkeypatch.setenv(
        "UNKNOWN_TAXONOMY_V2_RESULT_ENTRY_OCCURRENCE_NONCE", "issue124-occurrence"
    )

    clock = StageClock()
    with clock.scope():
        with stage_region("branch_plan_orchestration"):
            with stage_region("check"):
                with stage_region("obligation_build"):
                    _burn()

    without_stages = _result_for_preimage()
    with_stages = _result_for_preimage()
    attach_stage_timing(with_stages, clock)

    payload_without = without_stages.to_dict()
    payload_with = with_stages.to_dict()

    # 差は diagnostics だけ、その中でも `timings.stages` だけ。
    assert payload_with != payload_without
    assert {k: v for k, v in payload_with.items() if k != "diagnostics"} == {
        k: v for k, v in payload_without.items() if k != "diagnostics"
    }
    timings_with = payload_with["diagnostics"]["timings"]
    timings_without = payload_without["diagnostics"]["timings"]
    assert timings_with["stages"] != timings_without["stages"]
    assert timings_with["stages"]["regions"]["branch_plan_orchestration"]["calls"] == 1
    assert {k: v for k, v in timings_with.items() if k != "stages"} == {
        k: v for k, v in timings_without.items() if k != "stages"
    }

    bundle_without, session_a, evidence_a = _independent_finalization(
        tmp_path, monkeypatch,
        case_id="issue124-without-stages", result_payload_preimage=payload_without,
    )
    bundle_with, session_b, evidence_b = _independent_finalization(
        tmp_path, monkeypatch,
        case_id="issue124-with-stages", result_payload_preimage=payload_with,
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
            bundle_verification_key_id="issue124-test-key",
            bundle_verification_key=b"k" * 32,work=SealWorkBudget.for_result()
        )
        assert validated["outcome"] == "EQUIVALENT"

    # serialization surface が違うので preimage digest は違う（意図どおり）。
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
    # 一致が vacuous でないこと（射影が空ではない）。
    projection = bundle_with["canonical_semantic_result_projection"]["payload"]
    assert projection["canonical_outcome"] == "EQUIVALENT"
    assert "diagnostics" not in projection and "stages" not in projection


# --------------------------------------------------------------------------
# 8. region の境界（どこから測り始めるか）
#
# 恒等式 B / C は `exclusive = inclusive - 直接子` から作った値を同じ式で確かめる
# ので、region を開くのが遅くても閉じてしまう。境界そのものはここで固定する。
# --------------------------------------------------------------------------

def _checker_function_ast(name):
    import ast
    import inspect

    from scripts.function_tracer_pcode.checker.checker import EquivalenceChecker

    source = inspect.getsource(getattr(EquivalenceChecker, name))
    tree = __import__("ast").parse(
        "class _C:\n" + "\n".join("    " + line for line in source.splitlines())
    )
    function = tree.body[0].body[0]
    body = function.body
    if (
        body
        and isinstance(body[0], ast.Expr)
        and isinstance(getattr(body[0], "value", None), ast.Constant)
        and isinstance(body[0].value.value, str)
    ):
        body = body[1:]
    return ast, function, body


def test_stage_plan_region_covers_the_whole_method_body_including_the_import():
    """`branch_plan_orchestration` は `_run_stage_plan()` の本体全部を測る。

    `phases[].seconds.stage_plan` は method 呼び出し全体を測るので、region が
    後ろで開くと恒等式 A の左右が別の区間になる（差は「意図的に除外した前処理」
    として残り、誰にも帰属されない）。
    """
    ast, _function, body = _checker_function_ast("_run_stage_plan")

    # docstring の次は region そのもの。前に実行される文を 1 つも許さない。
    assert len(body) == 1 and isinstance(body[0], ast.With), [
        ast.unparse(node) for node in body
    ]
    assert [ast.unparse(item.context_expr) for item in body[0].items] == [
        "stage_region('branch_plan_orchestration')"
    ]
    # 遅延 import も region の内側にある。
    imports = [
        node for node in ast.walk(body[0])
        if isinstance(node, ast.ImportFrom)
        and any(alias.name == "run_obligation_branch_plan" for alias in node.names)
    ]
    assert len(imports) == 1


def test_check_region_opens_at_method_entry_without_widening_the_catch_scope():
    """`check` は method entry 直後から測り、判定用 try の catch 範囲は広げない。"""
    ast, _function, body = _checker_function_ast("check")

    # 1 文目が region の open、2 文目が計時専用の try。
    assert ast.unparse(body[0]) == "check_region = open_stage_region('check')"
    assert len(body) == 2 and isinstance(body[1], ast.Try), [
        ast.unparse(node) for node in body
    ]
    timing = body[1]
    # 計時用の try は handler を持たない = 例外の扱いを変えない。
    assert timing.handlers == [] and timing.orelse == []
    assert [ast.unparse(node) for node in timing.finalbody] == ["check_region.close()"]

    # 冒頭の実処理（start_time と signature 生成）は region の内側、判定用 try の外側。
    judgement = [node for node in timing.body if isinstance(node, ast.Try)]
    assert len(judgement) == 1
    before = timing.body[:timing.body.index(judgement[0])]
    rendered = [ast.unparse(node).splitlines()[0] for node in before]
    assert rendered == [
        "start_time = time.time()",
        "if original_signature1 is None:",
        "if original_signature2 is None:",
    ]
    # 判定用 try の handler の種類と順序（Issue #125 で typed 分岐を 2 つ足した）。
    # region は計時だけで catch scope を広げていないことがここで固定される。
    # Issue #106 PR-106-0: typed handler は族 1 つ（`AnalysisFailureError`）。
    # catch scope は変えていないので、region の開き位置の契約はそのまま。
    assert [ast.unparse(handler.type) for handler in judgement[0].handlers] == [
        "(UnknownSmtExtensionWidthError, UnsupportedSmtOperatorError)",
        "AnalysisFailureError",
        "Exception",
    ]
    assert judgement[0].finalbody == []


def test_check_inclusive_covers_the_signature_work_at_the_entry(monkeypatch):
    """`check()` 冒頭の非ゼロ処理が `check` の inclusive に入る（実行で確認）。"""
    from scripts.function_tracer_pcode.core.signature import FunctionSignature
    from scripts.function_tracer_pcode.tests.unit.test_monolithic_region_split import _analysis

    original = FunctionSignature.from_analysis
    delay = 0.05

    def slow_from_analysis(analysis):
        time.sleep(delay)
        return original(analysis)

    monkeypatch.setattr(FunctionSignature, "from_analysis", staticmethod(slow_from_analysis))

    clock = StageClock()
    with clock.scope():
        with stage_region("branch_plan_orchestration"):
            # original_signature1/2 を渡さないので、冒頭で 2 回 signature を作る。
            _real_checker().check(_analysis("left", 7), _analysis("right", 7))

    stages = clock.snapshot()
    orchestration = _node(stages["regions"], "branch_plan_orchestration")
    check = _node(stages["regions"], "branch_plan_orchestration", "check")
    # 2 回分の signature 生成が check の内側にある。
    assert check["seconds_inclusive"] >= 2 * delay
    # したがって orchestration exclusive へは漏れていない。
    assert orchestration["seconds_exclusive"] < delay
    assert all(row["within_tolerance"] for row in region_identity_rows(stages))


def test_check_entry_exception_is_not_caught_by_the_judgement_handlers(monkeypatch):
    """冒頭の signature 生成が投げた例外は、従来どおり呼び出し元へ出る。

    計時用の try を足したことで catch-all が広がっていないことを実行で固定する。
    region は閉じるが、`_create_error_result` へは落ちない。
    """
    from scripts.function_tracer_pcode.core.signature import FunctionSignature
    from scripts.function_tracer_pcode.tests.unit.test_monolithic_region_split import _analysis

    class _EntryFailure(RuntimeError):
        pass

    def failing_from_analysis(_analysis_argument):
        raise _EntryFailure("signature construction failed")

    monkeypatch.setattr(
        FunctionSignature, "from_analysis", staticmethod(failing_from_analysis)
    )

    clock = StageClock()
    with clock.scope():
        with stage_region("branch_plan_orchestration"):
            with pytest.raises(_EntryFailure):
                _real_checker().check(_analysis("left", 7), _analysis("right", 7))

    # 例外で抜けても region は閉じている（回数と時間が残る）。
    check = _node(clock.snapshot()["regions"], "branch_plan_orchestration", "check")
    assert check["calls"] == 1

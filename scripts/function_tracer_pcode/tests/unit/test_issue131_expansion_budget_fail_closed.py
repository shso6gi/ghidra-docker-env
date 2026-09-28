# -*- coding: utf-8 -*-
"""Issue #131 PR-B: 観測した切り捨てを fail-closed にする回帰テスト。

PR-A（``test_issue131_expansion_budget_observation.py``）が「生成 → 保持 → 伝搬 →
同期」を固定しているのに対し、本 file は marker が

* 解析前提（``to_dict`` / snapshot fingerprint / outcome seed）へ入ること、
* 網羅性 producer・fallback coverage・決定的 SAT・無条件 EQ の各 gate を閉じること、
* 記録が増えたときに古い派生 authority を無効化すること、
* 効果面では既存の効果不完全性 reason として残ること、

を固定する。solver Mock は gate の制御フロー確認に使い、網羅性 producer の判定は
実 solver（z3）を通す。false EQ の再現・非再現の結論は実バイナリ計測で述べる。
"""

from dataclasses import replace
from unittest.mock import Mock, patch

import pytest

from scripts.function_tracer_pcode.analysis.returns.return_extraction import (
    _build_function_outcome_seed,
)
from scripts.function_tracer_pcode.authority.domains.loop_recurrence import (
    classify_effect_incomplete_reasons,
)
from scripts.function_tracer_pcode.authority.domains.return_outcome import (
    OUTCOME_STAGE_REASON_MATRIX,
    RETURN_OUTCOME_TYPED_REASON_IDS,
    reason_for_stage_status,
)
from scripts.function_tracer_pcode.core import (
    Condition,
    Expression,
    FunctionReturnAnalysis,
    ReturnInfo,
)
from scripts.function_tracer_pcode.core.analysis import (
    _SEMANTIC_SUCCESSOR_INVALIDATION_BY_CHANGE,
    ReturnOutcome,
    ReturnPathEvidence,
    SymbolicRegionCandidate,
    TerminalCandidate,
    FunctionOutcomeSeed,
    semantic_successor_invalidated_fields,
)
from scripts.function_tracer_pcode.core.runtime_refs import (
    EFFECT_EXPANSION_CASE_BUDGET_EXCEEDED_REASON,
    EXPANSION_CASE_BUDGET_EXCEEDED_REASON,
    ExpansionBudgetCollector,
    ExpansionBudgetTruncation,
    PcodeOpRef,
)
from scripts.function_tracer_pcode.proof.obligations.snapshot import AnalysisSnapshot
from scripts.function_tracer_pcode.proof.obligations.runtime import ObligationRuntimeSession
from scripts.function_tracer_pcode.proof.strategies import PairwiseStrategy
from scripts.function_tracer_pcode.proof.strategies.proof_gates._shared import UnknownReasonId
from scripts.function_tracer_pcode.proof.unknown_reason import (
    UnknownAggregationUnit,
    UnknownDecisionEffect,
    UnknownRecoveryProofKind,
    UnknownReasonScope,
    get_unknown_reason_definition,
)
from scripts.function_tracer_pcode.smt.parallel import ParallelResult
from scripts.function_tracer_pcode.smt.solvers.z3 import Z3Solver

# PR-A のテストが持つ fake CFG / 展開 / 効果要約 harness をそのまま使う
# （scaffold を二重に持たないため。import しても pytest の収集対象は変わらない）。
from scripts.function_tracer_pcode.tests.unit.test_issue131_expansion_budget_observation import (
    _FakeCfg,
    _FakeTracer,
    _a1_expansion,
    _analyzer,
    _build_effect_summary_harness,
    _callee_analysis_with_marker,
    _loop_cfg,
    _record,
)
from scripts.function_tracer_pcode.tests.unit._publication import published
from scripts.function_tracer_pcode.tests.unit._publication import raw_function_analysis


# ---------------------------------------------------------------------------
# 共通 scaffold
# ---------------------------------------------------------------------------


def _const(value: int) -> Expression:
    return Expression.constant(value, 4)


def _param() -> Expression:
    return Expression.parameter("param_1", 0, 4)


class _CompleteProfile:
    pcode_enumeration_complete = True
    cfg_edges_complete = True
    region_identity_complete = True
    region_single_entry = True
    region_all_exits_enumerated = True
    region_cross_edges_enumerated = True
    terminal_return_coverage_complete = True
    unsupported_mnemonics = ()
    branchind_count = 0
    callind_count = 0
    callother_count = 0
    abnormal_terminal_block_count = 0
    cfg_acyclic = True
    return_block_count = 1
    region_pcode_op_keys = (PcodeOpRef(address_offset=1, mnemonic="RETURN").stable_key(),)
    region_entry_block_key = ("block", 0)
    region_block_keys = (("block", 0),)
    region_exit_block_keys = (("block", 0),)
    region_cfg_edge_keys = ()

    def stable_key(self):
        return ("function_control_effect_profile", "complete")


class _EffectSummaryStub:
    incomplete_reasons = ()
    has_unsupported_call = False

    def __init__(self, profile=None):
        self.function_control_effect_profile = profile or _CompleteProfile()

    def stable_key(self):
        return ("effect_summary_stub", self.function_control_effect_profile.stable_key())


class _Z3Runner:
    def __init__(self):
        self._solver = Z3Solver(timeout=2)

    def run_sequential(self, query: str):
        return ParallelResult([self._solver.check_equivalence_direct(query)])


def _strategy(solver_runner=None) -> PairwiseStrategy:
    return PairwiseStrategy(Mock(), solver_runner or _Z3Runner(), debug=False)


def _base_ctx():
    return {
        "header_lines": [
            "(declare-fun p1 () (_ BitVec 32))",
            "(declare-fun p2 () (_ BitVec 32))",
            "(assert (= p1 p2))",
        ],
    }


def _replace_param(symbol: str):
    def _replace(obj):
        if isinstance(obj, (Condition, Expression)):
            smt = obj.to_smt(float_mode="fp")
        else:
            smt = str(obj)
        return smt.replace("param_1", symbol)

    return _replace


def _total_return_analysis(*, truncations=()) -> FunctionReturnAnalysis:
    """空 guard の 1 ケースだけを持つ、単項証明が通る解析結果。

    生存 guard の OR は恒真（空 guard がある）なので、marker が無ければ
    ``path_region_completeness`` まで含めて complete になる。
    """

    ret = ReturnInfo(address="0x0", value=_const(0), conditions=[], branch_index=0)
    analysis = raw_function_analysis(
        function_name="f",
        entry_point="0x1000",
        parameters=[
            {"name": "param_1", "index": 0, "size": 4, "data_type": "int", "is_signed": True}
        ],
        returns=[ret],
        return_type="int",
        expansion_budget_truncations=tuple(truncations),
    )
    analysis.return_outcomes = (
        ReturnOutcome(guard=(), value=ret.value, return_info=ret),
    )
    op_ref = PcodeOpRef(address_offset=1, mnemonic="RETURN")
    ret.pcode_op_ref = op_ref
    evidence = ReturnPathEvidence(
        terminal_op_ref=op_ref,
        coverage_status="complete",
        path_block_keys=((("path_block", 0, "0x0"),),),
        path_guard_keys=((),),
    )
    ret.return_path_evidence = evidence
    terminal_id = ("return", analysis.entry_point)
    analysis.outcome_seed = FunctionOutcomeSeed(
        function_identity=analysis.outcome_function_identity(),
        input_domain_contract=("all_inputs",),
        terminal_candidates=(
            TerminalCandidate(terminal_id, "return", op_ref=op_ref),
        ),
        symbolic_regions=(
            SymbolicRegionCandidate(
                ("region", terminal_id),
                terminal_id,
                (),
                True,
                producer_evidence_key=("return_path_evidence", evidence.stable_key()),
                observed_value=_const(0),
            ),
        ),
        control_flow_evidence_key=_CompleteProfile().stable_key(),
    )
    analysis.effect_summary = _EffectSummaryStub()
    # test がこの解析の producer。組み立て終えたここで公開する。
    return published(analysis)


# ---------------------------------------------------------------------------
# reason 登録・行列・写像
# ---------------------------------------------------------------------------


def test_the_new_reason_is_registered_with_the_planned_contract():
    definition = get_unknown_reason_definition(EXPANSION_CASE_BUDGET_EXCEEDED_REASON)
    assert definition.reason_id == "expansion_case_budget_exceeded"
    assert definition.decision_effect == UnknownDecisionEffect.BLOCKS_DECISION.value
    assert definition.reason_scope == UnknownReasonScope.FUNCTION.value
    assert definition.aggregation_unit == UnknownAggregationUnit.FUNCTION.value
    # marker を解除する回復手段は用意しない
    assert definition.recovery_proof_kind == UnknownRecoveryProofKind.NONE.value


def test_the_event_ingress_status_table_is_derived_from_the_stage_matrix():
    """封印済み stage/status を 2 か所で持たない。

    ingress 側に別表があると、行列へ status を足しても event が拒否され、pair が
    ERROR で落ちる（本 PR の計測で実際に起きた）。
    """
    from scripts.function_tracer_pcode.authority.lifecycle.stream import (
        sealed_outcome_stage_statuses,
    )

    derived = {}
    for stage, status in OUTCOME_STAGE_REASON_MATRIX:
        derived.setdefault(stage, set()).add(status)
    assert {stage: set(statuses) for stage, statuses in sealed_outcome_stage_statuses().items()} == derived
    assert "case_budget_exceeded" in sealed_outcome_stage_statuses()["path_region_completeness"]


def test_the_case_budget_producer_attempt_event_is_accepted_by_ingress():
    """producer が返した status がそのまま event authority を通る。"""
    from scripts.function_tracer_pcode.authority.lifecycle.stream import (
        sealed_outcome_stage_statuses,
    )

    statuses = sealed_outcome_stage_statuses()
    for stage, status in OUTCOME_STAGE_REASON_MATRIX:
        assert status in statuses[stage], (stage, status)


def test_the_stage_status_pair_is_sealed_and_typed():
    assert (
        reason_for_stage_status("path_region_completeness", "case_budget_exceeded")
        == EXPANSION_CASE_BUDGET_EXCEEDED_REASON
    )
    assert (
        OUTCOME_STAGE_REASON_MATRIX[("path_region_completeness", "case_budget_exceeded")]
        == EXPANSION_CASE_BUDGET_EXCEEDED_REASON
    )
    assert EXPANSION_CASE_BUDGET_EXCEEDED_REASON in RETURN_OUTCOME_TYPED_REASON_IDS


def test_the_effect_side_reason_maps_to_the_existing_effect_incompleteness():
    classification = classify_effect_incomplete_reasons(
        (EFFECT_EXPANSION_CASE_BUDGET_EXCEEDED_REASON,)
    )
    assert classification.reason_ids == ("effect_observation_coverage_incomplete",)


def test_blocking_and_unary_blockers_map_to_the_registered_reason():
    strategy = _strategy(Mock())
    assert strategy._unknown_reason_id_for_blocking_unsafety(
        f"function1:{EXPANSION_CASE_BUDGET_EXCEEDED_REASON}"
    ) is UnknownReasonId.EXPANSION_CASE_BUDGET_EXCEEDED
    # 効果面の reason は既存の効果観測不完全性へ落ちる（未登録 reason にしない）
    assert strategy._unknown_reason_id_for_blocking_unsafety(
        f"function2:{EFFECT_EXPANSION_CASE_BUDGET_EXCEEDED_REASON}"
    ) == "effect_observation_coverage_incomplete"

    from scripts.function_tracer_pcode.proof.strategies.proof_gates.return_coverage import (
        _unary_blocker_reason_id,
    )

    assert _unary_blocker_reason_id(
        "outcome_path_region_completeness_case_budget_exceeded"
    ) is UnknownReasonId.EXPANSION_CASE_BUDGET_EXCEEDED
    # 通常の未完了は従来どおり
    assert _unary_blocker_reason_id(
        "outcome_path_region_completeness_incomplete"
    ) is UnknownReasonId.OUTCOME_PATH_REGION_INCOMPLETE


def test_the_blocking_reason_record_uses_the_registered_reason_id():
    """blocker から作る reason record が登録済み reason のまま出ること。"""
    strategy = _strategy(Mock())
    left = _total_return_analysis(truncations=(_record(),))
    right = _total_return_analysis()
    record = strategy._make_blocking_unsafety_unknown_reason(
        f"function1:{EXPANSION_CASE_BUDGET_EXCEEDED_REASON}",
        left,
        right,
        stage="S_PAIRWISE",
    )
    assert record.reason_id == EXPANSION_CASE_BUDGET_EXCEEDED_REASON
    assert record.detail == f"function1:{EXPANSION_CASE_BUDGET_EXCEEDED_REASON}"


# ---------------------------------------------------------------------------
# A7: 解析レベルの gate（決定的 SAT / 無条件 EQ）
# ---------------------------------------------------------------------------


def test_marker_blocks_the_decisive_sat_and_the_unconditional_equivalence_gate():
    analysis = _total_return_analysis(truncations=(_record(),))
    assert analysis.has_expansion_budget_truncation() is True
    assert EXPANSION_CASE_BUDGET_EXCEEDED_REASON in analysis.get_decisive_sat_unsafety_reasons()
    assert (
        EXPANSION_CASE_BUDGET_EXCEEDED_REASON
        in analysis.get_equivalence_blocking_unsafety_reasons()
    )


def test_effect_only_truncation_blocks_both_gates_without_an_analysis_marker():
    analysis = _total_return_analysis()
    analysis.effect_summary = Mock(
        incomplete_reasons=(EFFECT_EXPANSION_CASE_BUDGET_EXCEEDED_REASON,),
        has_unsupported_call=False,
    )
    assert analysis.expansion_budget_truncations == ()
    assert analysis.has_expansion_budget_truncation() is True
    for reasons in (
        analysis.get_decisive_sat_unsafety_reasons(),
        analysis.get_equivalence_blocking_unsafety_reasons(),
    ):
        assert EXPANSION_CASE_BUDGET_EXCEEDED_REASON in reasons
        assert EFFECT_EXPANSION_CASE_BUDGET_EXCEEDED_REASON in reasons


def test_a7_surviving_sat_does_not_become_decisive_for_either_side():
    strategy = _strategy(Mock())
    left = _total_return_analysis(truncations=(_record(),))
    right = _total_return_analysis()
    assert strategy._collect_decisive_sat_unsafety_reasons(left, right) == [
        f"function1:{EXPANSION_CASE_BUDGET_EXCEEDED_REASON}"
    ]
    assert (
        f"function1:{EXPANSION_CASE_BUDGET_EXCEEDED_REASON}"
        in strategy._collect_equivalence_blocking_unsafety_reasons(left, right)
    )


def _a1_analysis(input_values, *, with_markers=True):
    """A1 の実展開（18 ケース → 生存 16 ケース）から解析結果を組み立てる。

    切り捨てられる 2 ケースだけが左右で異なるので、生存ケースだけを比較すると
    左右は完全に一致する。marker の有無だけを変えて対照できるようにする。
    """

    expanded, collector, _expander = _a1_expansion(input_values)
    assert len(expanded) == 16
    returns = [
        ReturnInfo(
            address=f"0x{index:x}",
            value=item.value,
            conditions=list(item.conditions),
            branch_index=index,
        )
        for index, item in enumerate(expanded)
    ]
    analysis = raw_function_analysis(
        function_name="f",
        entry_point="0x1000",
        parameters=[
            {
                "name": f"param_{index + 1}",
                "index": index,
                "size": 4,
                "data_type": "int",
                "is_signed": True,
            }
            for index in range(13)
        ],
        returns=returns,
        return_type="int",
        expansion_budget_truncations=collector.as_tuple() if with_markers else (),
    )
    assert collector.as_tuple(), "A1 fixture must truncate"
    return analysis


def test_a1_reaches_a_final_unknown_with_the_registered_reason():
    """A1 を最終判定入口（``PairwiseStrategy.check``）まで通す。

    生存 16 ケースは左右一致するので、切り捨てを見なければ EQUIVALENT になり得る
    入力。marker があるときは UNKNOWN になり、登録 reason が出ることを固定する。
    """

    from scripts.function_tracer_pcode.proof.formula.builder import FormulaBuilder
    from scripts.function_tracer_pcode.smt.parallel import ParallelSolverRunner

    left = _a1_analysis([100, 101, 102, 103])
    right = _a1_analysis([100, 101, 202, 203])
    strategy = PairwiseStrategy(FormulaBuilder(), ParallelSolverRunner(timeout=5), debug=False)
    result = strategy.check(left, right)

    # 生存ケースの比較はすべて UNSAT（= 切り捨てを見なければ等価に見える）
    assert (result.total_pairs, result.unsat_pairs, result.sat_pairs) == (256, 256, 0)
    assert result.is_equivalent is None, "final outcome must be UNKNOWN"
    assert result.is_equivalent is not True and result.is_equivalent is not False
    reason_ids = {str(getattr(record, "reason_id", "")) for record in result.unknown_reasons}
    assert reason_ids == {EXPANSION_CASE_BUDGET_EXCEEDED_REASON}, sorted(reason_ids)
    assert all(
        get_unknown_reason_definition(reason).decision_effect
        == UnknownDecisionEffect.BLOCKS_DECISION.value
        for reason in reason_ids
    )


def test_a1_without_markers_does_not_report_the_case_budget_reason():
    """対照: 同じ生存ケースでも marker が無ければ本 reason は出ない（退行検査）。"""

    from scripts.function_tracer_pcode.proof.formula.builder import FormulaBuilder
    from scripts.function_tracer_pcode.smt.parallel import ParallelSolverRunner

    left = _a1_analysis([100, 101, 102, 103], with_markers=False)
    right = _a1_analysis([100, 101, 202, 203], with_markers=False)
    strategy = PairwiseStrategy(FormulaBuilder(), ParallelSolverRunner(timeout=5), debug=False)
    result = strategy.check(left, right)

    assert (result.total_pairs, result.unsat_pairs, result.sat_pairs) == (256, 256, 0)
    assert result.is_equivalent is not False, "surviving cases agree; NOT_EQ must not appear"
    reason_ids = {str(getattr(record, "reason_id", "")) for record in result.unknown_reasons}
    assert EXPANSION_CASE_BUDGET_EXCEEDED_REASON not in reason_ids
    # marker が無ければ従来どおりの blocker（切り捨て以外の理由）だけが残る
    assert reason_ids == {"return_coverage_gap"}, sorted(reason_ids)


def test_a1_surviving_cases_that_agree_still_block_equivalence_on_both_sides():
    """A1: 捨てられたケースだけで値が違う対でも、生存ケースは一致する。

    その状態で無条件 EQ / 決定的 SAT の両 gate が閉じることを固定する。
    """

    left_expanded, left_collector, _ = _a1_expansion([100, 101, 102, 103])
    right_expanded, right_collector, _ = _a1_expansion([100, 101, 202, 203])
    assert len(left_expanded) == len(right_expanded) == 16
    assert left_collector.as_tuple() and right_collector.as_tuple()

    strategy = _strategy(Mock())
    left = _total_return_analysis(truncations=left_collector.as_tuple())
    right = _total_return_analysis(truncations=right_collector.as_tuple())
    blocking = strategy._collect_equivalence_blocking_unsafety_reasons(left, right)
    assert [
        item for item in blocking if item.endswith(EXPANSION_CASE_BUDGET_EXCEEDED_REASON)
    ] == [
        f"function1:{EXPANSION_CASE_BUDGET_EXCEEDED_REASON}",
        f"function2:{EXPANSION_CASE_BUDGET_EXCEEDED_REASON}",
    ]
    reason_id = strategy._unknown_reason_id_for_blocking_unsafety(blocking[0])
    assert get_unknown_reason_definition(reason_id).decision_effect == (
        UnknownDecisionEffect.BLOCKS_DECISION.value
    )


# ---------------------------------------------------------------------------
# A2 / A3: 単項網羅性 producer
# ---------------------------------------------------------------------------


def test_a3_total_partition_without_a_marker_is_still_covered():
    strategy = _strategy()
    left = _total_return_analysis()
    right = _total_return_analysis()
    strategy._obligation_runtime_session = ObligationRuntimeSession.create(left, right)
    assert strategy._outcome_partition_covered_labels(
        _base_ctx(), left, right, _replace_param("p1"), _replace_param("p2")
    ) == {"function1", "function2"}


def test_a2_surviving_guard_union_total_does_not_make_the_partition_complete():
    strategy = _strategy()
    left = _total_return_analysis(truncations=(_record(),))
    right = _total_return_analysis()
    strategy._obligation_runtime_session = ObligationRuntimeSession.create(left, right)
    assert strategy._outcome_partition_covered_labels(
        _base_ctx(), left, right, _replace_param("p1"), _replace_param("p2")
    ) == set()
    assert strategy._last_unary_outcome_blockers == {
        "function1": "outcome_path_region_completeness_case_budget_exceeded"
    }


def test_a2_loop_phi_truncation_reaches_the_producer_through_the_seed():
    """A2 の展開（entry 空 guard + latch 3 × 6 経路 = 19 ケース）を実際に通す。"""

    from scripts.function_tracer_pcode.tests.unit.test_issue131_expansion_budget_observation import (
        _FakeMultiequalOp,
        _FakePhiParent,
        _FakeVarnode,
        _expander,
    )

    cfg, latches = _loop_cfg(latch_count=3, paths_per_latch=6)
    tracker = cfg.tracker()
    preds = [cfg.block(0).block] + [cfg.block(latch).block for latch in latches]
    op = _FakeMultiequalOp(
        _FakePhiParent(preds),
        [_FakeVarnode(200 + index) for index in range(len(preds))],
    )
    expander, collector = _expander(tracker)
    expanded = expander._expand_multiequal(op, [], 0)
    assert len(expanded) == 16 and any(not ev.conditions for ev in expanded)

    analysis = _total_return_analysis(truncations=collector.as_tuple())
    _build_function_outcome_seed(analysis)
    assert analysis.outcome_seed.unresolved_control_evidence == (
        ("expansion_budget_truncation", collector.as_tuple()[0].event_id, ()),
    )


# ---------------------------------------------------------------------------
# fallback coverage（ラベル別分岐の前で inconclusive）
# ---------------------------------------------------------------------------


def _explode(*_args, **_kwargs):
    raise AssertionError("coverage query must not run for a truncated analysis")


def _covered_recorder(labels):
    def _covered(_base_ctx_arg, _cases, _replace_fn, label):
        from scripts.function_tracer_pcode.proof.strategies.proof_gates._shared import (
            ReturnCoverageCheckResult,
        )

        labels.append(label)
        return ReturnCoverageCheckResult(
            status="covered", coverage_proof_method="unconditional_return_case"
        )

    return _covered


def test_fallback_coverage_is_inconclusive_before_any_coverage_query_runs():
    """切り捨てのある側だけが、coverage 問い合わせを迂回して inconclusive になる。"""
    strategy = _strategy(Mock())
    strategy.enable_completed_recovery_proofs = False
    left = _total_return_analysis(truncations=(_record(),))
    right = _total_return_analysis()
    queried = []
    with patch.object(strategy, "_outcome_partition_covered_labels", return_value=set()), \
            patch.object(strategy, "_outcome_partition_inconclusive_labels", return_value=set()), \
            patch.object(
                strategy, "_check_return_case_coverage_gap", _covered_recorder(queried)
            ):
        reasons = strategy._collect_return_coverage_unsafety_reasons(
            _base_ctx(), left.returns, right.returns,
            _replace_param("p1"), _replace_param("p2"), left, right,
        )
    assert reasons == [f"function1:{EXPANSION_CASE_BUDGET_EXCEEDED_REASON}"]
    assert queried == ["function2"]


def test_fallback_coverage_records_no_completion_proof_for_a_truncated_analysis():
    strategy = _strategy(Mock())
    strategy.enable_completed_recovery_proofs = True
    left = _total_return_analysis(truncations=(_record(),))
    right = _total_return_analysis(truncations=(_record(),))
    recorded = []
    with patch.object(strategy, "_outcome_partition_covered_labels", return_value=set()), \
            patch.object(strategy, "_outcome_partition_inconclusive_labels", return_value=set()), \
            patch.object(strategy, "_check_return_case_coverage_gap", _explode), \
            patch.object(
                strategy,
                "_record_completed_return_coverage_proof",
                side_effect=lambda *a, **k: recorded.append(a),
            ):
        reasons = strategy._collect_return_coverage_unsafety_reasons(
            _base_ctx(), left.returns, right.returns,
            _replace_param("p1"), _replace_param("p2"), left, right,
        )
    assert reasons == [
        f"function1:{EXPANSION_CASE_BUDGET_EXCEEDED_REASON}",
        f"function2:{EXPANSION_CASE_BUDGET_EXCEEDED_REASON}",
    ]
    assert recorded == []


def test_fallback_coverage_is_unchanged_for_an_untruncated_analysis():
    strategy = _strategy(Mock())
    strategy.enable_completed_recovery_proofs = False
    left = _total_return_analysis()
    right = _total_return_analysis()
    queried = []
    with patch.object(strategy, "_outcome_partition_covered_labels", return_value=set()), \
            patch.object(strategy, "_outcome_partition_inconclusive_labels", return_value=set()), \
            patch.object(
                strategy, "_check_return_case_coverage_gap", _covered_recorder(queried)
            ):
        reasons = strategy._collect_return_coverage_unsafety_reasons(
            _base_ctx(), left.returns, right.returns,
            _replace_param("p1"), _replace_param("p2"), left, right,
        )
    assert queried == ["function1", "function2"]
    assert reasons == []


# ---------------------------------------------------------------------------
# A5: 分岐条件 refinement の停止
# ---------------------------------------------------------------------------


class _TruncatingExpander:
    """``expand_from_varnode`` で必ず 1 件切り捨てる展開器の差し替え。"""

    instances = []

    def __init__(self, *_args, budget_sink=None, **_kwargs):
        self.budget_sink = budget_sink
        _TruncatingExpander.instances.append(self)

    def expand_from_varnode(self, _varnode, _conditions):
        from scripts.function_tracer_pcode.semantics.transform.expander import ExpandedValue

        if self.budget_sink is not None:
            self.budget_sink(
                ExpansionBudgetTruncation(kind="dedup_case_limit", dedup=(17, 16, 16))
            )
        return [ExpandedValue(_refined_expression(), [])]


class _CleanExpander(_TruncatingExpander):
    def expand_from_varnode(self, _varnode, _conditions):
        from scripts.function_tracer_pcode.semantics.transform.expander import ExpandedValue

        return [ExpandedValue(_refined_expression(), [])]


def _refined_expression() -> Expression:
    """再構築後の分岐条件として採用可能な bool 式（未解決を含まない）。"""
    return Expression.binary_op("INT_EQUAL", _param(), _const(1))


def _refinable_tracker():
    cfg = _FakeCfg()
    unresolved = Expression.unknown("call_result")
    cfg.branch(0, unresolved, 1, 2)
    cfg.block(1)
    cfg.block(2)
    tracker = cfg.tracker()
    tracker.tracer = _FakeTracer()
    tracker.block_by_index = {index: info for index, info in cfg.blocks.items()}
    block = cfg.block(0)
    block.branch_condition_varnode = Mock(getSize=Mock(return_value=1))
    return tracker, block, unresolved


def _transform_module():
    import scripts.function_tracer_pcode.semantics.transform as transform_module

    return transform_module


def test_a5_branch_refinement_is_not_adopted_when_the_expansion_truncates():
    tracker, block, unresolved = _refinable_tracker()
    collector = ExpansionBudgetCollector()
    with patch.object(_transform_module(), "ExpressionExpander", _TruncatingExpander):
        changed = tracker.refine_branch_conditions(budget_sink=collector.record)

    assert changed == 0
    assert block.branch_condition is unresolved
    # 記録は所有 scope へ 1 度だけ届く（二重転送なし）
    assert len(collector.as_tuple()) == 1
    assert collector.as_tuple()[0].kind == "dedup_case_limit"


def test_a5_branch_refinement_still_applies_without_a_truncation():
    tracker, block, unresolved = _refinable_tracker()
    collector = ExpansionBudgetCollector()
    with patch.object(_transform_module(), "ExpressionExpander", _CleanExpander):
        changed = tracker.refine_branch_conditions(budget_sink=collector.record)

    assert changed == 1
    assert block.branch_condition is not unresolved
    assert collector.as_tuple() == ()


# ---------------------------------------------------------------------------
# 採用 callee の marker 伝搬（fail-open を残さない）
# ---------------------------------------------------------------------------


def _refiner_with_adopted_callee(on_callee_adopted):
    """callee の戻り値が実際に最終 returns へ残る bounded refinement を組む。"""
    from scripts.function_tracer_pcode.tests.unit.test_issue131_expansion_budget_observation import (
        _adopted_callee_refinement_case,
    )

    return _adopted_callee_refinement_case(on_callee_adopted)


def test_marker_propagation_failure_is_not_swallowed_and_blocks_adoption():
    """採用 callee の marker 伝搬が失敗したら refined returns を公開しない。"""

    calls = []

    def _failing(callee_analysis):
        calls.append(callee_analysis)
        raise RuntimeError("marker propagation failed")

    refiner, analysis = _refiner_with_adopted_callee(_failing)
    returns_before = analysis.returns

    with pytest.raises(RuntimeError, match="marker propagation failed"):
        refiner.refine_analysis(analysis)

    assert calls, "the callee must actually have been adopted"
    # 採用された callee 由来の値だけが残る状態にはしない
    assert analysis.returns is returns_before
    assert "bounded_call_refinement" not in analysis.analysis_notes


def test_marker_propagation_success_still_adopts_and_propagates():
    """正常時は従来どおり採用され、marker も伝搬する。"""

    calls = []
    refiner, analysis = _refiner_with_adopted_callee(calls.append)
    returns_before = analysis.returns

    changed = refiner.refine_analysis(analysis)

    assert changed is True
    assert analysis.returns is not returns_before
    assert len(calls) == 1
    assert calls[0].expansion_budget_truncations


def test_adoption_notification_happens_before_the_returns_are_published():
    """順序契約: 採用 callee 確定 → marker 伝搬 → refined returns 公開。"""
    import inspect

    from scripts.function_tracer_pcode.analysis import bounded_refinement

    source = inspect.getsource(bounded_refinement.BoundedCallRefiner.refine_analysis)
    notify_at = source.index("self._notify_adopted_callees(deduped)")
    publish_at = source.index("analysis.returns = deduped")
    assert notify_at < publish_at
    # 通知経路に例外の握り潰しを残さない
    notify_source = inspect.getsource(
        bounded_refinement.BoundedCallRefiner._notify_callee_adopted
    )
    assert "except" not in notify_source


# ---------------------------------------------------------------------------
# A6 / A9: 効果要約
# ---------------------------------------------------------------------------


def test_a6_effect_summary_records_the_effect_reason_when_its_expansion_truncates():
    analyzer = _analyzer()
    callee, _callee_record = _callee_analysis_with_marker()
    service, function, high_function, condition_tracker, stack, _calls = (
        _build_effect_summary_harness(analyzer, callee)
    )
    for item in stack:
        item.__enter__()
    try:
        summary = service.build_effect_summary(
            function, high_function, Mock(), condition_tracker, [], set()
        )
    finally:
        for item in reversed(stack):
            item.__exit__(None, None, None)

    assert EFFECT_EXPANSION_CASE_BUDGET_EXCEEDED_REASON in summary.incomplete_reasons
    # 保存された要約自身が reason を持つ（診断 dict とは別の寿命）
    cached = analyzer._runtime_state.effect_summary_cache[("summary_scope",)]
    assert cached is summary


def test_a9_cached_effect_summary_keeps_the_reason_when_the_diagnostics_are_dropped():
    analyzer = _analyzer()
    callee, _callee_record = _callee_analysis_with_marker()
    service, function, high_function, condition_tracker, stack, _calls = (
        _build_effect_summary_harness(analyzer, callee)
    )
    for item in stack:
        item.__enter__()
    try:
        summary = service.build_effect_summary(
            function, high_function, Mock(), condition_tracker, [], set()
        )
    finally:
        for item in reversed(stack):
            item.__exit__(None, None, None)

    analyzer._runtime_state.effect_summary_budget_diagnostics.clear()
    analysis = _total_return_analysis()
    analysis.effect_summary = summary
    assert analysis.expansion_budget_truncations == ()
    assert analysis.has_expansion_budget_truncation() is True
    assert (
        EXPANSION_CASE_BUDGET_EXCEEDED_REASON
        in analysis.get_equivalence_blocking_unsafety_reasons()
    )


def test_a6_the_effect_reason_helper_keeps_the_reason_tuple_sorted_and_unique():
    from scripts.function_tracer_pcode.analysis.returns.expansion_budget import (
        mark_effect_expansion_case_budget_exceeded,
    )

    summary = Mock(incomplete_reasons=("effect_store_location_unmodeled",))
    assert mark_effect_expansion_case_budget_exceeded(summary) is True
    assert summary.incomplete_reasons == (
        EFFECT_EXPANSION_CASE_BUDGET_EXCEEDED_REASON,
        "effect_store_location_unmodeled",
    )
    # 2 度目は増やさない（v2 の効果 reason 分類は昇順・重複なしを要求する）
    assert mark_effect_expansion_case_budget_exceeded(summary) is False
    assert classify_effect_incomplete_reasons(summary.incomplete_reasons).reason_ids == (
        "effect_observation_coverage_incomplete",
        "effect_observation_coverage_incomplete",
    )


def test_a9_callee_branch_refinement_truncation_marks_the_callee_summary_itself():
    """要約構築の外で走る callee の分岐条件 refinement 分も要約自身へ残す。"""
    import inspect

    from scripts.function_tracer_pcode.analysis.returns import effect_integration

    source = inspect.getsource(effect_integration.EffectIntegrationService.build_effect_summary)
    marker = "diagnostics[callee_summary_cache_key] = merge_expansion_budget_truncations"
    head, _sep, tail = source.partition(marker)
    assert _sep, "callee 診断の合流点が見つからない"
    # 合流の直後・caller 側 marker の記録より前で要約自身にも印を付ける
    mark_at = tail.index("mark_effect_expansion_case_budget_exceeded(summary)")
    record_at = tail.index("budget_collector.record(")
    assert mark_at < record_at
    assert "if callee_refinement_collector:" in tail[:mark_at]


def test_a9_a_truncated_callee_summary_is_never_used_for_caller_effects():
    """診断 dict が失われても、要約自身の reason で callee 効果は採用されない。

    cache hit 経路で marker を作れなくても、caller 側は ``incomplete_reasons`` を
    見て「未対応の呼び出し」として閉じる（fail-open が残っていないことの確認）。
    """
    from scripts.function_tracer_pcode.analysis.effects.summary import (
        EffectSummary,
        is_call_effect_summary_allowed,
    )

    summary = EffectSummary(
        parameter_names=[],
        effects=[],
        incomplete_reasons=(EFFECT_EXPANSION_CASE_BUDGET_EXCEEDED_REASON,),
    )
    assert is_call_effect_summary_allowed(summary) is False


def test_a9_missing_diagnostics_alone_never_invent_a_truncation():
    analysis = _total_return_analysis()
    analysis.effect_summary = Mock(incomplete_reasons=(), has_unsupported_call=False)
    assert analysis.has_expansion_budget_truncation() is False
    assert (
        EXPANSION_CASE_BUDGET_EXCEEDED_REASON
        not in analysis.get_equivalence_blocking_unsafety_reasons()
    )


# ---------------------------------------------------------------------------
# A10: 共通無効化
# ---------------------------------------------------------------------------


def test_the_invalidation_set_is_the_same_as_a_returns_change():
    assert (
        _SEMANTIC_SUCCESSOR_INVALIDATION_BY_CHANGE["expansion_budget_truncations"]
        == _SEMANTIC_SUCCESSOR_INVALIDATION_BY_CHANGE["returns"]
    )
    assert semantic_successor_invalidated_fields("expansion_budget_truncations") == (
        _SEMANTIC_SUCCESSOR_INVALIDATION_BY_CHANGE["returns"]
    )


def _analysis_with_derived_state():
    analysis = _total_return_analysis()
    analysis.analysis_view_identity = ("view", 1)
    analysis.partition_revision = 3
    analysis.completed_recovery_proof_ids = (("proof", 1),)
    analysis.summary_return_candidates = ()
    return analysis


def test_a10_adding_a_marker_invalidates_the_derived_authority():
    analyzer = _analyzer()
    analysis = _analysis_with_derived_state()
    assert analysis.outcome_seed is not None
    collector = ExpansionBudgetCollector()
    collector.record(_record())

    analyzer._sync_expansion_budget_truncations(analysis, collector=collector)

    assert analysis.expansion_budget_truncations == collector.as_tuple()
    assert analysis.outcome_seed is None
    assert analysis.return_outcomes == ()
    assert analysis.analysis_view_identity is None
    assert analysis.partition_revision == 0
    assert analysis.completed_recovery_proof_ids == ()


def test_a10_resyncing_the_same_records_is_a_no_op():
    analyzer = _analyzer()
    marker = _record()
    analysis = _analysis_with_derived_state()
    analysis.expansion_budget_truncations = (marker,)
    collector = ExpansionBudgetCollector()
    collector.record(marker)

    analyzer._sync_expansion_budget_truncations(analysis, collector=collector)

    assert analysis.outcome_seed is not None
    assert analysis.analysis_view_identity == ("view", 1)
    assert analysis.partition_revision == 3


def test_a10_adding_only_a_reference_id_still_invalidates():
    analyzer = _analyzer()
    marker = _record()
    analysis = _analysis_with_derived_state()
    analysis.expansion_budget_truncations = (marker,)
    collector = ExpansionBudgetCollector()
    collector.record(replace(marker, referenced_event_ids=("ref-1",)))

    analyzer._sync_expansion_budget_truncations(analysis, collector=collector)

    assert analysis.expansion_budget_truncations[0].referenced_event_ids == ("ref-1",)
    assert analysis.outcome_seed is None
    assert analysis.analysis_view_identity is None


def test_invalidation_defaults_are_not_shared_between_results():
    first = _analysis_with_derived_state()
    second = _analysis_with_derived_state()
    from scripts.function_tracer_pcode.core.analysis import (
        invalidate_semantic_successor_fields,
    )

    invalidate_semantic_successor_fields(first, "expansion_budget_truncations")
    invalidate_semantic_successor_fields(second, "expansion_budget_truncations")
    assert first.return_abi_facts is not second.return_abi_facts or not first.return_abi_facts
    assert first.return_outcomes == second.return_outcomes == ()


def test_a10_invalidation_clears_blockers_but_the_marker_keeps_both_verdicts_closed():
    """無効化は quarantine のような既存 blocker も既定へ戻すが、marker 自身が
    等価・非等価の両方を塞ぎ続けるので、判定が緩む方向へは動かない。"""
    analyzer = _analyzer()
    analysis = _analysis_with_derived_state()
    analysis.quarantined_recurrence_proposals = ("proposal",)
    analysis.termination_path_effect_evidence = ("evidence",)
    collector = ExpansionBudgetCollector()
    collector.record(_record())

    analyzer._sync_expansion_budget_truncations(analysis, collector=collector)

    assert analysis.quarantined_recurrence_proposals == ()
    assert analysis.termination_path_effect_evidence == ()
    assert EXPANSION_CASE_BUDGET_EXCEEDED_REASON in analysis.get_decisive_sat_unsafety_reasons()
    assert (
        EXPANSION_CASE_BUDGET_EXCEEDED_REASON
        in analysis.get_equivalence_blocking_unsafety_reasons()
    )


def test_the_new_blocking_reason_cannot_be_discharged_by_a_completed_recovery_proof():
    """marker を解除する機構は追加しない。既存の完了証明のどれも discharge しない。"""
    strategy = _strategy(Mock())
    strategy.enable_completed_recovery_proofs = True
    left = _total_return_analysis(truncations=(_record(),))
    right = _total_return_analysis()
    unresolved = strategy._unresolved_equivalence_blocking_unknown_reasons(
        [f"function1:{EXPANSION_CASE_BUDGET_EXCEEDED_REASON}"],
        left,
        right,
        stage="S_PAIRWISE",
    )
    assert [record.reason_id for record in unresolved] == [
        EXPANSION_CASE_BUDGET_EXCEEDED_REASON
    ]
    # 登録上も回復手段を持たない
    assert get_unknown_reason_definition(
        EXPANSION_CASE_BUDGET_EXCEEDED_REASON
    ).recovery_proof_kind == UnknownRecoveryProofKind.NONE.value


# ---------------------------------------------------------------------------
# seed / snapshot への束縛
# ---------------------------------------------------------------------------


def test_the_seed_binds_referenced_event_ids_not_only_the_event_id():
    """同一 ``event_id`` でも参照 ID が増えれば seed digest が変わる。"""
    from scripts.function_tracer_pcode.proof.obligations.outcome_partition import (
        outcome_seed_digest,
    )

    marker = _record()
    base = _total_return_analysis(truncations=(marker,))
    _build_function_outcome_seed(base)
    referenced = _total_return_analysis(
        truncations=(replace(marker, referenced_event_ids=("ref-1",)),)
    )
    _build_function_outcome_seed(referenced)

    assert base.outcome_seed.unresolved_control_evidence == (
        ("expansion_budget_truncation", marker.event_id, ()),
    )
    assert referenced.outcome_seed.unresolved_control_evidence == (
        ("expansion_budget_truncation", marker.event_id, ("ref-1",)),
    )
    assert outcome_seed_digest(base.outcome_seed) != outcome_seed_digest(
        referenced.outcome_seed
    )


def test_the_seed_binds_an_effect_only_truncation():
    """解析 marker が空でも、効果要約の切り捨て reason を seed へ束縛する。"""
    from scripts.function_tracer_pcode.proof.obligations.outcome_partition import (
        outcome_seed_digest,
    )

    clean = _total_return_analysis()
    _build_function_outcome_seed(clean)
    effect_only = _total_return_analysis()
    effect_only.effect_summary = Mock(
        incomplete_reasons=(EFFECT_EXPANSION_CASE_BUDGET_EXCEEDED_REASON,),
        has_unsupported_call=False,
        function_control_effect_profile=_CompleteProfile(),
    )
    _build_function_outcome_seed(effect_only)

    assert effect_only.expansion_budget_truncations == ()
    assert (EFFECT_EXPANSION_CASE_BUDGET_EXCEEDED_REASON,) in (
        effect_only.outcome_seed.unresolved_control_evidence
    )
    assert outcome_seed_digest(clean.outcome_seed) != outcome_seed_digest(
        effect_only.outcome_seed
    )


def test_the_seed_evidence_order_is_canonical():
    """marker / 参照 ID の並び順だけでは seed digest が変わらない。"""
    from scripts.function_tracer_pcode.proof.obligations.outcome_partition import (
        outcome_seed_digest,
    )

    first = replace(_record(label="a"), referenced_event_ids=("ref-2", "ref-1"))
    second = _record(label="b")
    forward = _total_return_analysis(truncations=(first, second))
    _build_function_outcome_seed(forward)
    backward = _total_return_analysis(truncations=(second, first))
    _build_function_outcome_seed(backward)

    assert outcome_seed_digest(forward.outcome_seed) == outcome_seed_digest(
        backward.outcome_seed
    )
    assert forward.outcome_seed.unresolved_control_evidence == (
        backward.outcome_seed.unresolved_control_evidence
    )


def test_the_seed_digest_changes_when_a_marker_is_present():
    from scripts.function_tracer_pcode.proof.obligations.outcome_partition import (
        outcome_seed_digest,
    )

    clean = _total_return_analysis()
    _build_function_outcome_seed(clean)
    truncated = _total_return_analysis(truncations=(_record(),))
    _build_function_outcome_seed(truncated)

    assert clean.outcome_seed.unresolved_control_evidence == ()
    assert truncated.outcome_seed.unresolved_control_evidence == (
        ("expansion_budget_truncation", _record().event_id, ()),
    )
    assert outcome_seed_digest(clean.outcome_seed) != outcome_seed_digest(
        truncated.outcome_seed
    )


def test_the_snapshot_fingerprint_separates_truncated_from_clean_analyses():
    clean = _total_return_analysis()
    truncated = _total_return_analysis(truncations=(_record(),))
    assert (
        AnalysisSnapshot.from_function_analysis(clean).semantic_fingerprint
        != AnalysisSnapshot.from_function_analysis(truncated).semantic_fingerprint
    )

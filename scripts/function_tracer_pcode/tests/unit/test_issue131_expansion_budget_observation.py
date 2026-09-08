# -*- coding: utf-8 -*-
"""Issue #131 PR-A: 展開ケース数・経路数の切り捨てが観測可能であることの回帰テスト。

PR-A は観測のみ。判定 gate・証明前提・semantic fingerprint には接続しない。
本 file は「生成 → 保持 → 伝搬 → 同期」の各段を、実際の展開・経路列挙・解析結果
更新を通して固定する（Ghidra object だけ fake 化する）。
"""

import dataclasses
import hashlib
import io
import json
from unittest.mock import Mock

import pytest

from scripts.function_tracer_pcode.analysis.condition.tracker import ConditionTracker
from scripts.function_tracer_pcode.analysis.returns.analyzer import ReturnAnalyzer
from scripts.function_tracer_pcode.analysis.returns.expansion_budget import (
    analysis_expansion_budget_payload,
    callee_reference_truncation,
    emit_analysis_expansion_budget_diagnostics,
    make_expansion_budget_sink,
)
from scripts.function_tracer_pcode.analysis.session import AnalysisSession
from scripts.function_tracer_pcode.core import Condition, Expression, FunctionReturnAnalysis
from scripts.function_tracer_pcode.core.runtime_refs import (
    ExpansionBudgetCollector,
    ExpansionBudgetTruncation,
    merge_expansion_budget_truncations,
    normalize_expansion_budget_truncations,
)
from scripts.function_tracer_pcode.semantics.transform.expander import (
    ExpandedValue,
    ExpressionExpander,
)


# ---------------------------------------------------------------------------
# fake CFG / P-code scaffold（Ghidra 境界のみ fake、経路列挙と展開は実コード）
# ---------------------------------------------------------------------------


class _FakeBlock:
    def __init__(self, index):
        self._index = index

    def getIndex(self):
        return self._index

    def getOutSize(self):
        return 0


class _FakeBlockInfo:
    def __init__(self, index, block):
        self.index = index
        self.block = block
        self.out_edges = []
        self.branch_condition = None
        self.branch_condition_varnode = None
        self.true_out_index = -1
        self.false_out_index = -1

    def has_conditional_branch(self):
        return (
            self.branch_condition is not None
            and self.true_out_index >= 0
            and self.false_out_index >= 0
        )


class _FakeCfg:
    """条件分岐だけを持つ fake CFG。実 ``ConditionTracker`` の経路列挙にかける。"""

    def __init__(self):
        self.blocks = {}

    def block(self, index):
        if index not in self.blocks:
            self.blocks[index] = _FakeBlockInfo(index, _FakeBlock(index))
        return self.blocks[index]

    def edge(self, src, dst):
        self.block(src).out_edges.append(self.block(dst).block)

    def branch(self, src, condition, true_index, false_index):
        info = self.block(src)
        info.branch_condition = condition
        info.true_out_index = true_index
        info.false_out_index = false_index
        self.edge(src, true_index)
        self.edge(src, false_index)

    def tracker(self, entry_index=0):
        tracer = Mock()
        tracer.high_function = Mock()
        tracer.debug = False
        tracker = ConditionTracker(tracer)
        tracker.entry_block = self.block(entry_index)
        by_block = {info.block: info for info in self.blocks.values()}
        tracker.get_block_by_hash = Mock(side_effect=lambda block: by_block.get(block))
        return tracker


def _atom(index):
    """互いに独立な条件式（正規化で潰れない）。"""
    return Expression.binary_op(
        "INT_NOTEQUAL",
        Expression.parameter(f"param_{index}", index - 1, 4),
        Expression.constant(0, 4),
    )


class _FakeVarnode:
    def __init__(self, value, size=4):
        self.value = value
        self._size = size

    def getSize(self):
        return self._size

    def getDef(self):
        return None


class _FakePhiParent:
    def __init__(self, preds):
        self._preds = list(preds)

    def getIndex(self):
        return 900

    def getOutSize(self):
        return 0

    def getInSize(self):
        return len(self._preds)

    def getIn(self, index):
        return self._preds[index]


class _FakeMultiequalOp:
    def __init__(self, parent, inputs):
        self._parent = parent
        self._inputs = list(inputs)

    def getParent(self):
        return self._parent

    def getNumInputs(self):
        return len(self._inputs)

    def getInput(self, index):
        return self._inputs[index]

    def getMnemonic(self):
        return "MULTIEQUAL"


class _FakeTracer:
    """varnode 固有の値を返す tracer（呼び出し順で値が変わらない）。"""

    def __init__(self):
        self.high_function = Mock()
        self.debug = False
        self.trace_calls = 0

    def trace_varnode(self, varnode, depth=0, use_cache=True):
        self.trace_calls += 1
        return Expression.constant(varnode.value, varnode.getSize())


def _expander(tracker, tracer=None, collector=None, surface="return_value", owner=None):
    collector = collector if collector is not None else ExpansionBudgetCollector()
    expander = ExpressionExpander(
        tracer if tracer is not None else _FakeTracer(),
        tracker,
        debug=False,
        budget_sink=make_expansion_budget_sink(
            collector, surface=surface, owner_scope_key=owner
        ),
    )
    return expander, collector


# ---------------------------------------------------------------------------
# A1: 切り捨て対象だけが左右で異なる（8 / 8 / 1 / 1、合計 18 ケース）
# ---------------------------------------------------------------------------


def _a1_cfg():
    """入力0/入力1 へ 8 経路ずつ（5 条件）、入力2/入力3 へ 1 経路ずつ（8/9 条件）。

    どの前任ブロックへの経路数も tracker の上限 8 以内で、条件数も上限 20 以内。
    """
    cfg = _FakeCfg()
    # s1 で H 系（短い条件）と G 系（長い条件）に分岐する
    cfg.branch(0, _atom(1), 1, 50)
    # H 系: 4 段の diamond。最終段の true/false が入力0 / 入力1 の前任ブロック
    cfg.branch(1, _atom(2), 2, 3)
    cfg.edge(2, 4)
    cfg.edge(3, 4)
    cfg.branch(4, _atom(3), 5, 6)
    cfg.edge(5, 7)
    cfg.edge(6, 7)
    cfg.branch(7, _atom(4), 8, 9)
    cfg.edge(8, 10)
    cfg.edge(9, 10)
    cfg.branch(10, _atom(5), 11, 12)
    cfg.edge(11, 90)
    cfg.edge(12, 90)
    # G 系: 単一経路だが条件列が長い。false 側は PHI 親へ到達しない行き止まり
    cfg.branch(50, _atom(6), 51, 99)
    cfg.branch(51, _atom(7), 52, 99)
    cfg.branch(52, _atom(8), 53, 99)
    cfg.branch(53, _atom(9), 54, 99)
    cfg.branch(54, _atom(10), 55, 99)
    cfg.branch(55, _atom(11), 56, 99)
    cfg.branch(56, _atom(12), 57, 58)
    cfg.edge(57, 90)
    cfg.branch(58, _atom(13), 59, 99)
    cfg.edge(59, 90)
    cfg.block(99)
    cfg.block(90)
    return cfg


def _a1_expansion(input_values):
    cfg = _a1_cfg()
    tracker = cfg.tracker()
    preds = [cfg.block(11).block, cfg.block(12).block, cfg.block(57).block, cfg.block(59).block]
    op = _FakeMultiequalOp(
        _FakePhiParent(preds),
        [_FakeVarnode(value) for value in input_values],
    )
    expander, collector = _expander(tracker)
    expanded = expander._expand_multiequal(op, [], 0)
    return expanded, collector, expander


def _case_signatures(expander, expanded):
    return {
        (
            expander._expansion_expression_signature(ev.value),
            ev.get_condition_signature(),
        )
        for ev in expanded
    }


def test_a1_case_layout_is_eighteen_cases_with_the_two_differing_ones_longest():
    """前提の固定: 18 ケース、相違する 2 ケースだけが最長で切り捨て対象になる。"""
    cfg = _a1_cfg()
    tracker = cfg.tracker()
    lengths = []
    for index in (11, 12, 57, 59):
        paths, truncations = tracker.get_all_valid_paths_to_block_with_truncations(
            cfg.block(index)
        )
        assert truncations == (), index  # 経路列挙側では打ち切っていない
        lengths.append(sorted(len(path) for path in paths))
    assert [len(item) for item in lengths] == [8, 8, 1, 1]
    assert set(lengths[0]) == {5} and set(lengths[1]) == {5}
    assert lengths[2] == [8] and lengths[3] == [9]


def test_a1_dedup_survivors_match_when_only_truncated_cases_differ():
    left, left_collector, left_expander = _a1_expansion([100, 101, 102, 103])
    right, right_collector, right_expander = _a1_expansion([100, 101, 202, 203])

    assert len(left) == 16 and len(right) == 16
    assert _case_signatures(left_expander, left) == _case_signatures(right_expander, right)
    # 相違する値は生存ケースに残らない
    survivor_values = {ev.value.to_string() for ev in left}
    assert survivor_values == {"100", "101"}

    for collector in (left_collector, right_collector):
        records = collector.as_tuple()
        assert len(records) == 1
        record = records[0]
        assert record.kind == "dedup_case_limit"
        assert record.surface == "return_value"
        assert record.dedup == (18, 16, 16)
        assert record.pcode_op_ref is not None


def test_a1_no_marker_when_the_case_count_stays_within_the_limit():
    """A3（A1 系）: 削除された入力領域を残る枝へ割り当て直すと 16 ケースで打ち切りなし。"""
    cfg = _FakeCfg()
    cfg.branch(0, _atom(2), 2, 3)
    cfg.edge(2, 4)
    cfg.edge(3, 4)
    cfg.branch(4, _atom(3), 5, 6)
    cfg.edge(5, 7)
    cfg.edge(6, 7)
    cfg.branch(7, _atom(4), 8, 9)
    cfg.edge(8, 10)
    cfg.edge(9, 10)
    cfg.branch(10, _atom(5), 11, 12)
    cfg.edge(11, 90)
    cfg.edge(12, 90)
    cfg.block(90)
    tracker = cfg.tracker()
    op = _FakeMultiequalOp(
        _FakePhiParent([cfg.block(11).block, cfg.block(12).block]),
        [_FakeVarnode(100), _FakeVarnode(101)],
    )
    expander, collector = _expander(tracker)
    expanded = expander._expand_multiequal(op, [], 0)

    assert len(expanded) == 16
    assert collector.as_tuple() == ()
    # 入力領域 (c1..c4) を 2 枝で覆っている
    assert {len(ev.conditions) for ev in expanded} == {4}


# ---------------------------------------------------------------------------
# A2: ループ + PHI。生存ケースに空 guard があっても marker は残る
# ---------------------------------------------------------------------------


def _loop_cfg(latch_count, paths_per_latch):
    """entry 直結の 1 ケース + latch ごとに ``paths_per_latch`` 本の相異なる経路。"""
    cfg = _FakeCfg()
    next_block = 100
    next_atom = 2
    cfg.branch(0, _atom(1), 1, 10)  # true: PHI 親へ直行（entry 経路は空 guard）
    cfg.edge(1, 900)
    latches = []
    chain_head = 10
    for latch_index in range(latch_count):
        latch = next_block
        next_block += 1
        latches.append(latch)
        cursor = chain_head
        for step in range(paths_per_latch):
            cond = _atom(next_atom)
            next_atom += 1
            following = next_block if step + 1 < paths_per_latch else 999
            next_block += 1 if step + 1 < paths_per_latch else 0
            cfg.branch(cursor, cond, latch, following)
            cursor = following
        cfg.edge(latch, 900)
        chain_head = next_block
        next_block += 1
        if latch_index + 1 < latch_count:
            # 次の latch chain は行き止まり 999 の代わりに新しい head から始める
            cfg.edge(999, chain_head)
    cfg.block(999)
    cfg.block(900)
    return cfg, latches


def test_a2_loop_phi_records_marker_even_though_an_empty_guard_case_survives():
    cfg, latches = _loop_cfg(latch_count=3, paths_per_latch=6)
    tracker = cfg.tracker()
    preds = [cfg.block(0).block] + [cfg.block(latch).block for latch in latches]
    op = _FakeMultiequalOp(
        _FakePhiParent(preds),
        [_FakeVarnode(200 + index) for index in range(len(preds))],
    )
    expander, collector = _expander(tracker)
    expanded = expander._expand_multiequal(op, [], 0)

    assert len(expanded) == 16
    # 生存 guard の OR が恒真に見える（空 guard がある）が、marker は残る
    assert any(not ev.conditions for ev in expanded)
    records = collector.as_tuple()
    assert len(records) == 1
    assert records[0].kind == "dedup_case_limit"
    assert records[0].dedup == (19, 16, 16)


def test_a3_loop_phi_without_truncation_keeps_no_marker():
    cfg, latches = _loop_cfg(latch_count=2, paths_per_latch=7)
    tracker = cfg.tracker()
    preds = [cfg.block(0).block] + [cfg.block(latch).block for latch in latches]
    op = _FakeMultiequalOp(
        _FakePhiParent(preds),
        [_FakeVarnode(200 + index) for index in range(len(preds))],
    )
    expander, collector = _expander(tracker)
    expanded = expander._expand_multiequal(op, [], 0)

    assert len(expanded) == 15
    assert collector.as_tuple() == ()


# ---------------------------------------------------------------------------
# dedup 単体の境界（統合テストとは別。tracker を通さない）
# ---------------------------------------------------------------------------


def _values(count, start=0):
    return [
        ExpandedValue(Expression.constant(start + index, 4), [Condition(_atom(1 + (index % 9)))])
        for index in range(count)
    ]


def _bare_expander(collector=None):
    tracker = Mock()
    expander = ExpressionExpander(
        Mock(),
        tracker,
        debug=False,
        budget_sink=(
            make_expansion_budget_sink(collector, surface="return_value")
            if collector is not None
            else None
        ),
    )
    return expander


def test_dedup_records_only_when_the_case_limit_actually_drops_cases():
    collector = ExpansionBudgetCollector()
    expander = _bare_expander(collector)
    # 上限ちょうど（16 件）では記録しない
    at_limit = [
        ExpandedValue(Expression.constant(index, 4), [Condition(_atom(1)), Condition(_atom(2))][: index % 2 + 1])
        for index in range(16)
    ]
    assert len(expander._deduplicate_expanded_values(at_limit, 0)) == 16
    assert collector.as_tuple() == ()

    # 17 件で初めて記録する
    over_limit = [
        ExpandedValue(Expression.constant(index, 4), [Condition(_atom(1))])
        for index in range(17)
    ]
    assert len(expander._deduplicate_expanded_values(over_limit, 0)) == 16
    records = collector.as_tuple()
    assert len(records) == 1
    assert records[0].kind == "dedup_case_limit"
    assert records[0].dedup == (17, 16, 16)


def test_plain_deduplication_alone_never_records_a_truncation():
    collector = ExpansionBudgetCollector()
    expander = _bare_expander(collector)
    duplicated = [
        ExpandedValue(Expression.constant(7, 4), [Condition(_atom(1))])
        for _ in range(40)
    ]
    assert len(expander._deduplicate_expanded_values(duplicated, 0)) == 1
    assert collector.as_tuple() == ()


def test_explicit_operation_case_limit_truncation_is_also_recorded():
    collector = ExpansionBudgetCollector()
    expander = _bare_expander(collector)
    values = [
        ExpandedValue(Expression.constant(index, 4), [Condition(_atom(1 + index % 9))])
        for index in range(9)
    ]
    expander._deduplicate_expanded_values(values, 0, limit=4, label="INT_ADD combinations")
    records = collector.as_tuple()
    assert len(records) == 1
    assert records[0].dedup == (9, 4, 4)
    assert records[0].label == "INT_ADD combinations"


# ---------------------------------------------------------------------------
# A4: tracker の経路数 / 条件数上限、entry 欠如、cache hit
# ---------------------------------------------------------------------------


def _wide_cfg(path_count):
    """target へ ``path_count`` 本の相異なる条件列を持つ CFG。"""
    cfg = _FakeCfg()
    cursor = 0
    for step in range(path_count):
        following = 1000 + step if step + 1 < path_count else 999
        cfg.branch(cursor, _atom(1 + step), 500, following)
        cursor = following
    cfg.block(500)
    cfg.block(999)
    return cfg


def test_tracker_records_path_limit_truncation_with_the_actual_counts():
    cfg = _wide_cfg(16)
    tracker = cfg.tracker()
    paths, truncations = tracker.get_all_valid_paths_to_block_with_truncations(cfg.block(500))
    assert len(paths) == 8
    assert len(truncations) == 1
    assert truncations[0].kind == "path_limit"
    assert truncations[0].paths == (16, 8, 8)
    assert truncations[0].conditions is None
    assert truncations[0].label == "block_path:500"


def test_tracker_records_condition_limit_truncation_separately():
    cfg = _FakeCfg()
    # 21 条件の単一経路（条件数上限 20 を超える）
    cursor = 0
    for step in range(21):
        following = 1000 + step if step + 1 < 21 else 500
        cfg.branch(cursor, _atom(1 + step), following, 999)
        cursor = following
    cfg.block(500)
    cfg.block(999)
    tracker = cfg.tracker()
    paths, truncations = tracker.get_all_valid_paths_to_block_with_truncations(cfg.block(500))
    assert paths == []
    assert [item.kind for item in truncations] == ["condition_limit"]
    assert truncations[0].conditions == (1, ConditionTracker.MAX_CONDITIONS_PER_PATH)
    assert truncations[0].paths is None


def test_tracker_missing_entry_is_inconclusive_but_not_a_budget_truncation():
    cfg = _wide_cfg(3)
    tracker = cfg.tracker()
    tracker.entry_block = None
    paths, truncations = tracker.get_all_valid_paths_to_block_with_truncations(cfg.block(500))
    assert paths == [] and truncations == ()


def test_tracker_cache_hit_still_returns_the_truncation_causes():
    cfg = _wide_cfg(16)
    tracker = cfg.tracker()
    first_paths, first = tracker.get_all_valid_block_paths_to_block_with_truncations(cfg.block(500))
    second_paths, second = tracker.get_all_valid_block_paths_to_block_with_truncations(cfg.block(500))
    assert second == first != ()
    # 既存 API の戻り順序は従来どおり（条件列の短い順）
    legacy = tracker.get_all_valid_block_paths_to_block(cfg.block(500))
    assert [conds for _blocks, conds in legacy] == [conds for _blocks, conds in first_paths]
    assert [conds for _blocks, conds in second_paths] == [conds for _blocks, conds in first_paths]


# ---------------------------------------------------------------------------
# A5: branch condition refinement は PR-A では挙動を変えない
# ---------------------------------------------------------------------------


class _PhiDefVarnode:
    def __init__(self, op, size=4):
        self._op = op
        self._size = size

    def getSize(self):
        return self._size

    def getDef(self):
        return self._op


def _refinement_tracker():
    """分岐条件が 18 ケースの PHI から来る tracker（refinement で切り捨てが起きる）。"""
    cfg = _a1_cfg()
    tracker = cfg.tracker()
    preds = [cfg.block(11).block, cfg.block(12).block, cfg.block(57).block, cfg.block(59).block]
    op = _FakeMultiequalOp(
        _FakePhiParent(preds),
        [_FakeVarnode(value) for value in (100, 101, 102, 103)],
    )
    refine_target = cfg.block(90)
    refine_target.branch_condition = Expression.unknown("opaque_branch")
    refine_target.branch_condition_varnode = _PhiDefVarnode(op)
    tracker.block_by_index = {info.index: info for info in cfg.blocks.values()}
    tracker.tracer = _FakeTracer()
    return tracker, refine_target


def test_branch_refinement_records_markers_without_changing_pr_a_behaviour():
    observed_tracker, observed_target = _refinement_tracker()
    collector = ExpansionBudgetCollector()
    observed_changed = observed_tracker.refine_branch_conditions(
        budget_sink=make_expansion_budget_sink(
            collector, surface="branch_condition", owner_scope_key=("scope",)
        ),
    )
    baseline_tracker, baseline_target = _refinement_tracker()
    baseline_changed = baseline_tracker.refine_branch_conditions()

    # 切り捨てを観測している
    records = collector.as_tuple()
    assert [record.kind for record in records] == ["dedup_case_limit"]
    assert records[0].surface == "branch_condition"
    assert records[0].owner_scope_key == ("scope",)
    assert records[0].dedup == (18, 16, 16)

    # PR-A: refinement の採否・結果は sink の有無で変わらない
    assert observed_changed == baseline_changed
    assert (observed_target.branch_condition is None) == (
        baseline_target.branch_condition is None
    )
    if observed_target.branch_condition is not None:
        assert (
            observed_target.branch_condition.to_string()
            == baseline_target.branch_condition.to_string()
        )


# ---------------------------------------------------------------------------
# A6: STORE 値展開からの伝搬
# ---------------------------------------------------------------------------


def test_store_value_expansion_propagates_markers_through_the_sink():
    from scripts.function_tracer_pcode.analysis.effects.store_effect import (
        _resolve_object_centric_store_value_effects,
    )

    cfg = _a1_cfg()
    tracker = cfg.tracker()
    preds = [cfg.block(11).block, cfg.block(12).block, cfg.block(57).block, cfg.block(59).block]

    class _PhiVarnode:
        def __init__(self, op):
            self._op = op

        def getSize(self):
            return 4

        def getDef(self):
            return self._op

    op = _FakeMultiequalOp(
        _FakePhiParent(preds),
        [_FakeVarnode(value) for value in (100, 101, 102, 103)],
    )
    collector = ExpansionBudgetCollector()
    effects = _resolve_object_centric_store_value_effects(
        _PhiVarnode(op),
        _FakeTracer(),
        tracker,
        [],
        budget_sink=make_expansion_budget_sink(
            collector, surface="store_value", owner_scope_key=("caller",)
        ),
    )
    assert effects
    records = collector.as_tuple()
    assert [record.surface for record in records] == ["store_value"]
    assert records[0].kind == "dedup_case_limit"
    assert records[0].owner_scope_key == ("caller",)


# ---------------------------------------------------------------------------
# marker / event ID の契約
# ---------------------------------------------------------------------------


def _record(**kwargs):
    base = dict(kind="dedup_case_limit", surface="return_value", label="expanded values", dedup=(18, 16, 16))
    base.update(kwargs)
    return ExpansionBudgetTruncation(**base)


def test_event_id_is_a_deterministic_digest_of_the_occurrence_key():
    first = _record()
    second = _record()
    assert first.event_id == second.event_id
    assert first.event_id == hashlib.sha256(
        json.dumps(
            _canonical(first.stable_key()), ensure_ascii=False, sort_keys=True, separators=(",", ":")
        ).encode("utf-8")
    ).hexdigest()
    # 参照 ID は発生事実キーにも event_id にも含めない
    reference = "zz-reference-id-zz"
    assert _record(referenced_event_ids=(reference,)).event_id == first.event_id
    assert reference not in json.dumps(
        _canonical(_record(referenced_event_ids=(reference,)).stable_key())
    )


def _canonical(value):
    from scripts.function_tracer_pcode.core.runtime_refs import _canonical_budget_value

    return _canonical_budget_value(value)


def test_different_owner_scopes_are_never_treated_as_the_same_event():
    left = _record(owner_scope_key=("bin_a", "f"))
    right = _record(owner_scope_key=("bin_b", "f"))
    assert left.event_id != right.event_id
    assert len(merge_expansion_budget_truncations([left], [right])) == 2


def test_same_event_with_extra_references_unions_instead_of_dropping():
    base = _record(referenced_event_ids=("e1",))
    more = _record(referenced_event_ids=("e2",))
    merged = merge_expansion_budget_truncations([base], [more])
    assert len(merged) == 1
    assert merged[0].referenced_event_ids == ("e1", "e2")
    # 同じ集合を再度合流させても変化しない（順序も正規化済み）
    assert merge_expansion_budget_truncations(merged, [base], [more]) == merged


def test_callee_reference_marker_holds_ids_only_and_does_not_recurse():
    callee = _record(owner_scope_key=("callee",))
    marker = callee_reference_truncation(
        [callee], callee_scope_key=("callee",), label="callee_fn"
    )
    assert marker.kind == "callee_analysis"
    assert marker.referenced_event_ids == (callee.event_id,)
    # 参照先を持つ marker をさらに参照しても、履歴は 1 段しか積み上がらない
    outer = callee_reference_truncation(
        [marker], callee_scope_key=("caller",), label="caller_fn"
    )
    assert outer.referenced_event_ids == (marker.event_id,)
    assert callee.event_id not in outer.referenced_event_ids


def test_no_marker_is_created_from_missing_callee_diagnostics():
    assert callee_reference_truncation((), callee_scope_key=("callee",)) is None
    assert callee_reference_truncation(None, callee_scope_key=("callee",)) is None


def test_normalization_sorts_and_deduplicates_records():
    a = _record(label="a")
    b = _record(label="b")
    assert normalize_expansion_budget_truncations([b, a, b]) == normalize_expansion_budget_truncations([a, b])


# ---------------------------------------------------------------------------
# session / 同期契約
# ---------------------------------------------------------------------------


def _analyzer():
    return ReturnAnalyzer(program=Mock(), debug=False)


def _analysis(**kwargs):
    payload = dict(
        function_name="f",
        entry_point="0x1000",
        parameters=[],
        returns=[],
        analysis_scope_key=("scope", "f"),
        binary_id="bin",
    )
    payload.update(kwargs)
    return FunctionReturnAnalysis(**payload)


def test_child_session_collector_does_not_leak_into_the_parent():
    analyzer = _analyzer()
    parent_collector = analyzer._current_expansion_budget_collector
    parent_collector.record(_record(label="parent"))
    with analyzer._analysis_context([], None, analysis_scope_key=("child",)):
        child_collector = analyzer._current_expansion_budget_collector
        assert child_collector is not parent_collector
        assert child_collector.as_tuple() == ()
        child_collector.record(_record(label="child"))
        assert analyzer._current_analysis_scope_key == ("child",)
    assert analyzer._current_expansion_budget_collector is parent_collector
    assert [item.label for item in parent_collector.as_tuple()] == ["parent"]


def test_exception_exit_restores_the_parent_collector():
    analyzer = _analyzer()
    parent_collector = analyzer._current_expansion_budget_collector
    with pytest.raises(RuntimeError):
        with analyzer._analysis_context([], None):
            analyzer._current_expansion_budget_collector.record(_record(label="child"))
            raise RuntimeError("boom")
    assert analyzer._current_expansion_budget_collector is parent_collector
    assert parent_collector.as_tuple() == ()


def test_sync_is_a_union_and_never_erases_markers_already_on_the_result():
    analyzer = _analyzer()
    existing = _record(label="from_view")
    analysis = _analysis(expansion_budget_truncations=(existing,))
    # session が空でも結果側の marker は消えない
    analyzer._sync_expansion_budget_truncations(analysis)
    assert analysis.expansion_budget_truncations == (existing,)

    added = _record(label="from_session")
    analyzer._current_expansion_budget_collector.record(added)
    analyzer._sync_expansion_budget_truncations(analysis)
    assert {item.label for item in analysis.expansion_budget_truncations} == {
        "from_view",
        "from_session",
    }


def test_resyncing_the_same_events_is_a_no_op():
    analyzer = _analyzer()
    analyzer._current_expansion_budget_collector.record(_record(label="only"))
    analysis = _analysis()
    analyzer._sync_expansion_budget_truncations(analysis)
    before = analysis.expansion_budget_truncations
    analyzer._sync_expansion_budget_truncations(analysis)
    assert analysis.expansion_budget_truncations is before


def test_resyncing_with_extra_reference_ids_updates_the_reference_union():
    analyzer = _analyzer()
    analyzer._current_expansion_budget_collector.record(_record(referenced_event_ids=("e1",)))
    analysis = _analysis()
    analyzer._sync_expansion_budget_truncations(analysis)
    analyzer._current_expansion_budget_collector.record(_record(referenced_event_ids=("e2",)))
    analyzer._sync_expansion_budget_truncations(analysis)
    assert len(analysis.expansion_budget_truncations) == 1
    assert analysis.expansion_budget_truncations[0].referenced_event_ids == ("e1", "e2")


def test_callee_analysis_marker_is_recorded_only_when_the_callee_has_records():
    analyzer = _analyzer()
    empty_callee = _analysis(analysis_scope_key=("callee",))
    analyzer._record_callee_analysis_expansion_budget(empty_callee)
    assert analyzer._current_expansion_budget_collector.as_tuple() == ()

    callee_record = _record(owner_scope_key=("callee",))
    callee = _analysis(
        analysis_scope_key=("callee",),
        expansion_budget_truncations=(callee_record,),
    )
    analyzer._record_callee_analysis_expansion_budget(callee)
    records = analyzer._current_expansion_budget_collector.as_tuple()
    assert len(records) == 1
    assert records[0].kind == "callee_analysis"
    assert records[0].callee_scope_key == ("callee",)
    assert records[0].referenced_event_ids == (callee_record.event_id,)


def test_effect_summary_diagnostics_cache_hit_keeps_the_reference_information():
    """``summarize_call`` の cache hit 分岐と同じ組み合わせを固定する。

    保存済み要約と同じ key の診断から参照 marker を作り、診断が無ければ作らない。
    診断 dict は ``effect_summary_cache`` と key・寿命を共有する。
    """
    analyzer = _analyzer()
    callee_record = _record(owner_scope_key=("callee_summary",), surface="store_value")
    analyzer._effect_summary_budget_diagnostics[("callee_summary",)] = (callee_record,)

    collector = ExpansionBudgetCollector()
    collector.record(
        callee_reference_truncation(
            analyzer._effect_summary_budget_diagnostics.get(("callee_summary",)) or (),
            callee_scope_key=("callee_summary",),
            label="callee_fn",
        )
    )
    records = collector.as_tuple()
    assert len(records) == 1
    assert records[0].kind == "callee_analysis"
    assert records[0].referenced_event_ids == (callee_record.event_id,)

    # 診断が無い callee からは marker を作らない（欠落から切り捨てを推定しない）
    collector.record(
        callee_reference_truncation(
            analyzer._effect_summary_budget_diagnostics.get(("unknown",)) or (),
            callee_scope_key=("unknown",),
            label="other",
        )
    )
    assert len(collector.as_tuple()) == 1


def test_absorbing_own_effect_summary_diagnostics_keeps_the_recorded_surface():
    analyzer = _analyzer()
    store_record = _record(surface="store_value", owner_scope_key=("self",))
    analyzer._effect_summary_budget_diagnostics[("self",)] = (store_record,)
    analyzer._absorb_effect_summary_budget_diagnostics(("self",))
    assert analyzer._current_expansion_budget_collector.as_tuple() == (store_record,)


# ---------------------------------------------------------------------------
# analyze_function の同期点（結果構築後 / wrapper 後 / 早期 return / cache 保存前）
# ---------------------------------------------------------------------------


def _analyze_function_source():
    import inspect

    from scripts.function_tracer_pcode.analysis.returns import analyze_function

    return inspect.getsource(analyze_function._impl_analyze_function)


def test_every_result_returning_path_syncs_before_its_cache_write():
    source = _analyze_function_source()
    lines = source.splitlines()
    cache_writes = [
        index
        for index, line in enumerate(lines)
        if "self._call_analysis_cache[analysis_scope_key]" in line
    ]
    assert len(cache_writes) == 2  # 早期 return と通常終了
    for index in cache_writes:
        window = "\n".join(lines[max(0, index - 4):index])
        assert "_sync_expansion_budget_truncations" in window


def test_result_construction_and_wrapper_recovery_are_both_synced():
    source = _analyze_function_source()
    assert source.count("self._sync_expansion_budget_truncations(result)") >= 8
    wrapper_marker = "result.deferred_calls = dict(self._current_deferred_calls)"
    head, _sep, _tail = source.partition(wrapper_marker)
    # call wrapper / switch 復元の後にも同期がある
    assert head.rstrip().endswith("self._sync_expansion_budget_truncations(result)")


def test_outcome_summary_syncs_before_the_seed_is_built():
    import inspect

    from scripts.function_tracer_pcode.analysis.returns import return_extraction

    source = inspect.getsource(return_extraction._impl__apply_outcome_partition_summaries)
    sync_at = source.index("_sync_expansion_budget_truncations")
    seed_at = source.index("_build_function_outcome_seed(analysis)")
    assert sync_at < seed_at


# ---------------------------------------------------------------------------
# PR-A の非接続（fingerprint / 判定 / to_dict / AST）
# ---------------------------------------------------------------------------


def test_markers_do_not_appear_in_to_dict_or_the_semantic_fingerprint():
    from scripts.function_tracer_pcode.proof.obligations.snapshot import AnalysisSnapshot

    without = _analysis()
    with_marker = _analysis(expansion_budget_truncations=(_record(),))
    assert "expansion_budget_truncations" not in without.to_dict()
    assert with_marker.to_dict() == without.to_dict()
    assert (
        AnalysisSnapshot.from_function_analysis(with_marker).semantic_fingerprint
        == AnalysisSnapshot.from_function_analysis(without).semantic_fingerprint
    )
    snapshot = AnalysisSnapshot.from_function_analysis(with_marker)
    assert "expansion_budget_truncations" not in snapshot.semantic_fields


def test_marker_field_is_registered_as_a_diagnostic_field():
    from scripts.function_tracer_pcode.proof.obligations.snapshot import (
        FUNCTION_ANALYSIS_FIELD_CLASSIFICATION,
    )

    assert FUNCTION_ANALYSIS_FIELD_CLASSIFICATION["expansion_budget_truncations"] == "diagnostic"
    assert {item.name for item in dataclasses.fields(FunctionReturnAnalysis)} == set(
        FUNCTION_ANALYSIS_FIELD_CLASSIFICATION
    )


def test_markers_do_not_change_the_analysis_level_unsafety_verdicts():
    without = _analysis()
    with_marker = _analysis(expansion_budget_truncations=(_record(),))
    assert (
        with_marker.get_decisive_sat_unsafety_reasons()
        == without.get_decisive_sat_unsafety_reasons()
    )
    assert (
        with_marker.get_equivalence_blocking_unsafety_reasons()
        == without.get_equivalence_blocking_unsafety_reasons()
    )
    assert with_marker.has_unresolved_return_value() == without.has_unresolved_return_value()


def test_markers_survive_derived_views_without_being_cleared():
    marker = _record()
    analysis = _analysis(expansion_budget_truncations=(marker,))
    accepted = analysis.with_accepted_return_partition([])
    assert accepted.expansion_budget_truncations == (marker,)
    diagnostics_view = analysis.with_summary_return_diagnostics()
    assert diagnostics_view.expansion_budget_truncations == (marker,)
    successor = analysis.semantic_successor(returns=[])
    assert successor.expansion_budget_truncations == (marker,)


def test_pr_a_does_not_reference_the_marker_from_decision_or_proof_modules():
    """PR-A の非接続検査（補助）。snapshot の分類登録・除外だけを例外として許可する。"""
    import ast
    import pathlib

    root = pathlib.Path(__file__).resolve().parents[2]
    allowed = {root / "proof" / "obligations" / "snapshot.py"}
    offenders = []
    for layer in ("proof", "checker", "authority", "reporting"):
        for path in (root / layer).rglob("*.py"):
            if path in allowed:
                continue
            tree = ast.parse(path.read_text(encoding="utf-8"))
            for node in ast.walk(tree):
                name = None
                if isinstance(node, ast.Attribute):
                    name = node.attr
                elif isinstance(node, ast.Constant) and isinstance(node.value, str):
                    name = node.value
                if name in {
                    "expansion_budget_truncations",
                    "has_expansion_budget_truncation",
                    "expansion_case_budget_exceeded",
                }:
                    offenders.append(str(path.relative_to(root)))
    assert offenders == []


def test_snapshot_only_classifies_the_marker_and_never_projects_it():
    import pathlib

    root = pathlib.Path(__file__).resolve().parents[2]
    source = (root / "proof" / "obligations" / "snapshot.py").read_text(encoding="utf-8")
    # 分類登録以外の場所からは参照しない
    assert source.count("expansion_budget_truncations") == 1
    assert '"expansion_budget_truncations": "diagnostic"' in source


# ---------------------------------------------------------------------------
# 設定と診断出力
# ---------------------------------------------------------------------------


def test_dedup_case_limit_setting_rejects_non_positive_and_malformed_values():
    from scripts.function_tracer_pcode.config.settings import _positive_int_setting

    assert _positive_int_setting("X", 16, {"X": "2"}) == 2
    assert _positive_int_setting("X", 16, {}) == 16
    assert _positive_int_setting("X", 16, {"X": ""}) == 16
    assert _positive_int_setting("X", 16, {"X": "0"}) == 16
    assert _positive_int_setting("X", 16, {"X": "-4"}) == 16
    assert _positive_int_setting("X", 16, {"X": "abc"}) == 16


def test_expander_uses_a_single_configurable_dedup_case_limit():
    from scripts.function_tracer_pcode.config.settings import EXPANDER_DEDUP_CASE_LIMIT

    assert ExpressionExpander.MAX_CASES_PER_MULTIEQUAL == EXPANDER_DEDUP_CASE_LIMIT
    collector = ExpansionBudgetCollector()
    expander = _bare_expander(collector)
    expander.MAX_CASES_PER_MULTIEQUAL = 2
    values = [
        ExpandedValue(Expression.constant(index, 4), [Condition(_atom(1 + index))])
        for index in range(5)
    ]
    assert len(expander._deduplicate_expanded_values(values, 0)) == 2
    assert collector.as_tuple()[0].dedup == (5, 2, 2)


def test_diagnostic_output_is_emitted_only_when_markers_exist():
    stream = io.StringIO()
    assert emit_analysis_expansion_budget_diagnostics(_analysis(), stream=stream) is False
    assert stream.getvalue() == ""

    marker = _record(owner_scope_key=("scope", "f"))
    analysis = _analysis(expansion_budget_truncations=(marker,))
    assert emit_analysis_expansion_budget_diagnostics(analysis, stream=stream) is True
    text = stream.getvalue()
    payload = json.loads(text.splitlines()[1])
    assert payload["binary_id"] == "bin"
    assert payload["function_name"] == "f"
    assert payload["truncation_count"] == 1
    assert payload["truncations"][0]["event_id"] == marker.event_id
    assert payload["truncations"][0]["dedup"] == {
        "candidate_count": 18,
        "kept_count": 16,
        "limit": 16,
    }
    assert analysis_expansion_budget_payload(_analysis()) is None


# ---------------------------------------------------------------------------
# analyze_function を実際に流した同期（結果構築後 / view の marker 保護 / 早期 return）
# ---------------------------------------------------------------------------


class _AnalyzeFunctionTracer:
    def __init__(self, *_args, **_kwargs):
        self.high_function = Mock()
        self.debug = False
        self.unknown_tracker = Mock(events=[])
        self.record_deferred_call = None
        self._function_binary_id = "B"
        self._function_program_id = 1
        self._function_entry_space = "ram"
        self._function_entry_offset = 0x401000

    def find_return_ops(self):
        return []

    def clear_cache(self):
        return None


class _AnalyzeFunctionTracker:
    def __init__(self, _tracer):
        self.block_by_index = {}

    def build(self):
        return None

    def refine_branch_conditions(self, **_kwargs):
        return None


def _run_analyze_function(analyzer, patches):
    from unittest.mock import patch

    function = Mock()
    function.getName.return_value = "f"
    function.getEntryPoint.return_value = "0x401000"

    decompile_results = Mock()
    decompile_results.decompileCompleted.return_value = True
    decompile_results.getHighFunction.return_value = Mock(
        getFunctionPrototype=Mock(return_value=None)
    )
    analyzer._get_decompiler = Mock(
        return_value=Mock(decompileFunction=Mock(return_value=decompile_results))
    )
    analyzer.program.getImageBase.return_value.getOffset.return_value = 0

    stack = [
        patch(
            "scripts.function_tracer_pcode.analysis.returns.analyzer.PcodeTracer",
            _AnalyzeFunctionTracer,
        ),
        patch(
            "scripts.function_tracer_pcode.analysis.returns.analyzer.ConditionTracker",
            _AnalyzeFunctionTracker,
        ),
        patch("scripts.function_tracer_pcode.analysis.phi_resolver.PhiHandler", Mock),
        patch.object(analyzer, "_collect_parameters", return_value=[]),
        patch.object(
            analyzer,
            "_augment_parameters_with_implicit_passthrough",
            side_effect=lambda params, *_a, **_k: params,
        ),
        patch.object(analyzer, "_get_return_type_info", return_value=(None, "int")),
        patch.object(analyzer, "_detect_signedness", return_value=None),
        patch.object(analyzer, "_apply_bounded_call_refinement", return_value=None),
        *patches,
    ]
    entered = [item.__enter__() for item in stack]
    try:
        return analyzer.analyze_function(function, timeout=1), entered
    finally:
        for item in reversed(stack):
            item.__exit__(None, None, None)


def test_marker_recorded_after_result_construction_reaches_the_cached_analysis():
    """call wrapper / 要約適用など、結果構築より後に出た marker も cache 前に同期される。"""
    from unittest.mock import patch

    analyzer = _analyzer()
    late_marker = _record(label="late_recovery")

    def _late_summary(_function, _high_function, analysis, _tracer):
        analyzer._current_expansion_budget_collector.record(late_marker)
        return None

    result, _ = _run_analyze_function(
        analyzer,
        [
            patch.object(
                analyzer,
                "_recover_control_region_returns_early",
                return_value=([], []),
            ),
            patch.object(
                analyzer,
                "_apply_structural_recurrence_summary",
                side_effect=_late_summary,
            ),
        ],
    )

    assert result is not None
    assert [item.label for item in result.expansion_budget_truncations] == ["late_recovery"]
    cached = analyzer._call_analysis_cache[result.analysis_scope_key]
    assert cached.expansion_budget_truncations == result.expansion_budget_truncations


def test_markers_already_on_a_returned_view_are_not_erased_by_an_empty_session():
    from unittest.mock import patch

    analyzer = _analyzer()
    view_marker = _record(label="from_summary_view")
    calls = {"count": 0}

    def _summary(_function, _high_function, analysis, _tracer):
        calls["count"] += 1
        if calls["count"] == 1:
            return None
        return dataclasses.replace(
            analysis,
            expansion_budget_truncations=(
                tuple(analysis.expansion_budget_truncations) + (view_marker,)
            ),
        )

    result, _ = _run_analyze_function(
        analyzer,
        [
            patch.object(
                analyzer,
                "_recover_control_region_returns_early",
                return_value=([], []),
            ),
            patch.object(
                analyzer, "_apply_structural_recurrence_summary", side_effect=_summary
            ),
        ],
    )

    assert result is not None
    # session は空だが view が持っていた marker は残る
    assert analyzer._current_expansion_budget_collector.as_tuple() == ()
    assert [item.label for item in result.expansion_budget_truncations] == ["from_summary_view"]


def test_pre_return_summary_early_return_syncs_before_its_cache_write():
    from unittest.mock import patch

    analyzer = _analyzer()
    early_marker = _record(label="pre_return_summary")

    early_result = _analysis(function_name="f", entry_point="0x401000")

    def _pre_return(**kwargs):
        analyzer._current_expansion_budget_collector.record(early_marker)
        early_result.analysis_scope_key = kwargs["analysis_scope_key"]
        return early_result

    result, _ = _run_analyze_function(
        analyzer,
        [
            patch.object(
                analyzer,
                "_recover_control_region_returns_early",
                return_value=(None, []),
            ),
            patch.object(analyzer, "_invoke_build_effect_summary", return_value=Mock(
                incomplete_reasons=(),
                call_target_resolution_evidence=None,
                synthetic_expr=None,
                has_unsupported_call=False,
                effects=[],
            )),
            patch.object(
                analyzer, "_try_pre_return_counted_loop_summary", side_effect=_pre_return
            ),
        ],
    )

    assert result is early_result
    assert [item.label for item in result.expansion_budget_truncations] == ["pre_return_summary"]
    cached = analyzer._call_analysis_cache[result.analysis_scope_key]
    assert cached.expansion_budget_truncations == result.expansion_budget_truncations

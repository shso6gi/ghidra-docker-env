# -*- coding: utf-8 -*-
"""Issue #22 PR-22-D: 式サイズ予算と、authority 確定前の出力準備。

固定する契約:

* 予算の **値** は `BudgetPolicy`（config が組み立て、pair 境界が scope を開く）、
  **数え方** は各 checkpoint の owner、**超過の扱い** は
  `core/budget_policy.raise_expression_size_budget_exceeded` 1 箇所（M-1）。
* 展開・solver 向け描画・直列化のどこで超えても同じ reason
  （`expression_size_budget_exceeded`）の pair terminal な限界になり、
  phase 再解析も conditional lane もしない（D1）。
* 出力の準備は `connector.finish` より **前**。解析も solver も EQ に届く pair で
  出力だけが超えても、EQ の receipt は発行されず reason 付き UNKNOWN になる（D4s）。
* payload の所有者は 3 層（A 準備 / B authority / C 診断）。A は B を上書きしない
  （O-1）、authority 後の追加は準備を作り直さない（O-2 / O-3）、B は切り詰めない
  （O-4）。診断を足すのは出力層の 1 行で済む（M-3）。
* 見積りと encoder は同じ `JsonEncodingPolicy` を使い、見積り >= 実際（D5s）。
"""

from __future__ import annotations

import dataclasses
import json
import time
from types import SimpleNamespace

import pytest

from scripts.function_tracer_pcode.authority.lifecycle import production_boundary
from scripts.function_tracer_pcode.checker import output_preparation
from scripts.function_tracer_pcode.checker.output_preparation import (
    FieldOwner,
    OutputEnvelopeInvariantViolation,
    OutputField,
    OutputPreparer,
    PreparedPayloadStale,
    RESULT_FIELDS,
    build_final_result_envelope,
    fields_owned_by,
    prepared_payload_for,
)
from scripts.function_tracer_pcode.config.settings import (
    EXPRESSION_BUDGET_DEFAULTS,
    expression_budget_policy,
)
from scripts.function_tracer_pcode.core import Condition, Expression, ExpressionType
from scripts.function_tracer_pcode.core.budget_policy import (
    BudgetKind,
    BudgetPolicy,
    active_budget_policy,
    budget_observations,
    budget_policy_scope,
    enforce_budget,
)
from scripts.function_tracer_pcode.core.errors import (
    ExpressionSizeBudgetExceeded,
    PairStopState,
    current_pair_ledger,
    pair_failure_scope,
    reset_pair_failure_scopes,
)
from scripts.function_tracer_pcode.core.expression import estimate_legacy_dict_bytes
from scripts.function_tracer_pcode.core.json_encoding import (
    RESULT_JSON_POLICY,
    JsonEncodingPolicy,
    JsonOutputLimitExceeded,
)
from scripts.function_tracer_pcode.core.render_smt import (
    expression_to_smt,
    render_expression_smt_evidence,
)
from scripts.function_tracer_pcode.core.semantic_freeze import publish
from scripts.function_tracer_pcode.core.semantic_snapshot import SemanticGraphMeter
from scripts.function_tracer_pcode.smt import SolverStatus
from scripts.function_tracer_pcode.tests.unit.test_issue106_pair_limitation_propagation import (
    _emit_one_production_signal,
    _new_checker,
    _run_pair,
)
from scripts.function_tracer_pcode.tests.unit.test_issue125_limitation_finalization import (
    _connector,
)
from scripts.function_tracer_pcode.tests.unit import (
    test_issue131_expansion_budget_observation as issue131,
)

from conftest import create_mock_analysis, create_mock_result


REASON = ExpressionSizeBudgetExceeded.REASON_ID


@pytest.fixture(autouse=True)
def _clean_pair_state():
    reset_pair_failure_scopes()
    yield
    reset_pair_failure_scopes()


# ---------------------------------------------------------------------------
# 共通の材料
# ---------------------------------------------------------------------------


def _shared_dag(depth=40, name="p"):
    """左右が同じ子を参照する深さ `depth` の DAG（木に展開すると 2^depth）。"""
    node = Expression.parameter(name, 0, 4)
    for _ in range(depth):
        node = Expression.binary_op("INT_ADD", node, node)
    return node


def _analyses():
    return (
        create_mock_analysis("func1", return_type="int"),
        create_mock_analysis("func2", return_type="int"),
    )


def _analyze_from(analysis1, analysis2):
    def _analyze(self, name, timeout):
        return analysis1 if name == "func1" else analysis2

    return _analyze


class _CountingCounterexample:
    """`to_dict()` を何回呼ばれたか数える反例（重い解析由来 payload の代役）。"""

    def __init__(self, payload):
        self.payload = payload
        self.calls = 0

    def __bool__(self):
        return True

    def to_dict(self):
        self.calls += 1
        return dict(self.payload)

    def to_string(self, format_type="text"):
        return "counterexample"


def _reason_ids(result):
    return [reason.reason_id for reason in result.unknown_reasons]


def _policy(**values):
    return BudgetPolicy(**values)


# ---------------------------------------------------------------------------
# BudgetPolicy / config（M-1）
# ---------------------------------------------------------------------------


def test_budget_policy_holds_only_typed_values():
    assert BudgetPolicy.unlimited().limit(BudgetKind.RENDER_BYTES) is None
    policy = _policy(render_bytes=10, serialization_bytes=100, envelope_headroom_bytes=40)
    assert policy.prepared_payload_limit() == 60
    assert policy.exceeds(BudgetKind.RENDER_BYTES, 11)
    assert not policy.exceeds(BudgetKind.RENDER_BYTES, 10)
    for bad in (0, -1, 1.5, True, "10"):
        with pytest.raises(ValueError):
            BudgetPolicy(render_bytes=bad)
    with pytest.raises(ValueError):
        BudgetPolicy(serialization_bytes=100, envelope_headroom_bytes=100)
    # 種類と field は 1 対 1
    assert {kind.value for kind in BudgetKind} <= {
        item.name for item in dataclasses.fields(BudgetPolicy)
    }


def test_the_policy_is_resolved_from_one_table_of_defaults_and_env():
    """M-1: 既定値は config の表 1 つ。環境変数は個別に上書き / 無効化できる。"""
    defaults = {name: default for name, _env, default in EXPRESSION_BUDGET_DEFAULTS}
    policy = expression_budget_policy({})
    for name, default in defaults.items():
        assert getattr(policy, name) == default, name
    env = {name: env_name for name, env_name, _default in EXPRESSION_BUDGET_DEFAULTS}
    overridden = expression_budget_policy({
        env["render_bytes"]: "12345",
        env["expansion_cases"]: "off",
        env["expression_nodes"]: "not-a-number",
    })
    assert overridden.render_bytes == 12345
    assert overridden.expansion_cases is None
    assert overridden.expression_nodes == defaults["expression_nodes"]


def test_scope_outside_is_unlimited_and_inner_scope_wins():
    assert active_budget_policy() == BudgetPolicy.unlimited()
    outer = _policy(render_bytes=100)
    inner = _policy(render_bytes=5)
    with budget_policy_scope(outer):
        with budget_policy_scope(inner):
            assert active_budget_policy() is inner
        assert active_budget_policy() is outer
    assert active_budget_policy() == BudgetPolicy.unlimited()


def test_m1_a_different_value_changes_only_the_decision_not_the_code():
    """M-1: 同じ checkpoint が、policy の値だけで止まったり止まらなかったりする。"""
    for limit, trips in ((3, True), (4, False)):
        with pair_failure_scope(("m1", limit), None), budget_policy_scope(
            _policy(expansion_cases=limit)
        ):
            if trips:
                with pytest.raises(ExpressionSizeBudgetExceeded):
                    enforce_budget(BudgetKind.EXPANSION_CASES, 4, site="s", target_key=("t",))
            else:
                enforce_budget(BudgetKind.EXPANSION_CASES, 4, site="s", target_key=("t",))


def test_enforcement_records_before_raising_and_is_pair_terminal():
    with pair_failure_scope(("pair",), None) as ledger, budget_policy_scope(
        _policy(render_bytes=1)
    ):
        try:
            enforce_budget(
                BudgetKind.RENDER_BYTES, 2, site="core.render_smt.emit",
                target_key=("t",), evidence=("x=1",),
            )
        except ExpressionSizeBudgetExceeded as exc:
            raised = exc
        # 例外を握り潰しても台帳には残っている
        pending = ledger.pending_failure()
    assert pending is not None and pending.exception is raised
    assert ledger.stop_state() is PairStopState.PAIR_TERMINAL_LIMITATION
    assert raised.reason_id == REASON
    assert raised.evidence_refs == (
        "budget=render_bytes", "limit=1", "observed=2", "x=1",
    )


# ---------------------------------------------------------------------------
# 展開の予算（D1）
# ---------------------------------------------------------------------------


def test_the_graph_meter_counts_distinct_nodes_once_and_the_tree_saturates():
    meter = SemanticGraphMeter()
    dag = _shared_dag(40)
    started = time.perf_counter()
    meter.add_root(dag)
    meter.add_root(dag)
    assert time.perf_counter() - started < 1.0
    assert meter.distinct_nodes == 41
    assert meter.tree_nodes == 2 * (2 ** 41 - 1)


def test_d1_the_real_expander_stops_before_deduplication():
    """本物の `_expand_multiequal_internal`（#131 の 18 case CFG）が予算で止まる。"""
    with pair_failure_scope(("d1",), None) as ledger, budget_policy_scope(
        _policy(expansion_cases=10)
    ):
        with pytest.raises(ExpressionSizeBudgetExceeded) as caught:
            issue131._a1_expansion([100, 101, 102, 103])
    exc = caught.value
    assert exc.site == (
        "semantics.transform.expander_multiequal._expand_multiequal_internal"
    )
    assert "budget=expansion_cases" in exc.evidence_refs
    assert "cases=11" in exc.evidence_refs
    assert any(ref.startswith("distinct_nodes=") for ref in exc.evidence_refs)
    assert any(ref.startswith("tree_nodes=") for ref in exc.evidence_refs)
    # target = (展開の所有 scope, MULTIEQUAL の op)
    owner, op_key = exc.target_key
    assert owner is None and op_key
    assert ledger.stop_state() is PairStopState.PAIR_TERMINAL_LIMITATION


def test_d1_within_budget_the_expansion_is_unchanged():
    baseline, baseline_collector, _expander = issue131._a1_expansion([100, 101, 102, 103])
    with pair_failure_scope(("d1-ok",), None), budget_policy_scope(
        _policy(expansion_cases=18, expression_nodes=10_000)
    ):
        bounded, bounded_collector, _ = issue131._a1_expansion([100, 101, 102, 103])
        observed = budget_observations()
    assert [ev.value.to_string() for ev in bounded] == [
        ev.value.to_string() for ev in baseline
    ]
    assert bounded_collector.as_tuple() == baseline_collector.as_tuple()
    site = "semantics.transform.expander_multiequal._expand_multiequal_internal"
    assert observed[f"expansion_cases@{site}"]["max"] == 18


def test_d1_expansion_limit_becomes_unknown_with_receipt_and_no_second_analysis():
    """D1: 解析中の超過 → reason 付き UNKNOWN + receipt、phase も lane も回らない。"""
    analysis1, analysis2 = _analyses()
    stage_calls = []

    def _analyze(self, name, timeout):
        if name == "func1":
            issue131._a1_expansion([100, 101, 102, 103])
        return analysis1 if name == "func1" else analysis2

    def _stage_plan(*_args, **_kwargs):
        stage_calls.append(1)
        return create_mock_result(is_equivalent=True, solver_status=SolverStatus.UNSAT)

    checker = _new_checker(_connector())
    checker.budget_policy = _policy(expansion_cases=10)
    lanes = []
    original_lane = production_boundary._run_conditional_lane

    def _spy_lane(*args, **kwargs):
        lanes.append(1)
        return original_lane(*args, **kwargs)

    production_boundary._run_conditional_lane = _spy_lane
    try:
        result = _run_pair(
            analyze=_analyze, stage_plan=_stage_plan, checker=checker,
            retry_with_type_fix=True,
        )
    finally:
        production_boundary._run_conditional_lane = original_lane
    assert result.final_outcome == "UNKNOWN"
    assert result.decision_receipt is not None
    assert _reason_ids(result) == [REASON]
    assert result.pair_stop_state == PairStopState.PAIR_TERMINAL_LIMITATION.value
    assert stage_calls == []  # 限界の後に判定段へ進まない
    assert result.diagnostics["conditional_lane"]["skipped"] == "pair_terminal"


# ---------------------------------------------------------------------------
# 描画の予算（書き出し口は CountingWriter のまま）
# ---------------------------------------------------------------------------


def _published_wide_expression(width=200):
    node = Expression.parameter("p0", 0, 4)
    for index in range(1, width):
        node = Expression.binary_op("INT_XOR", node, Expression.parameter(f"p{index}", index, 4))
    return publish(node)


def test_solver_rendering_over_budget_is_a_pair_terminal_limitation():
    expr = _published_wide_expression()
    full = expression_to_smt(expr)
    with pair_failure_scope(("render",), None) as ledger, budget_policy_scope(
        _policy(render_bytes=len(full) - 1)
    ):
        with pytest.raises(ExpressionSizeBudgetExceeded) as caught:
            expression_to_smt(expr)
        # 証拠・表示用の入口は判定に使わないので予算で止めない
        assert render_expression_smt_evidence(expr) == full
    exc = caught.value
    assert exc.site == "core.render_smt.emit"
    assert "budget=render_bytes" in exc.evidence_refs
    assert exc.target_key[0] == "smt_render" and exc.target_key[1]
    assert ledger.stop_state() is PairStopState.PAIR_TERMINAL_LIMITATION


def test_solver_rendering_within_budget_is_unchanged_and_observed():
    expr = _published_wide_expression()
    full = expression_to_smt(expr)
    with budget_policy_scope(_policy(render_bytes=len(full))):
        assert expression_to_smt(expr) == full
        observed = budget_observations()
    assert observed["render_bytes@core.render_smt.emit"]["max"] == len(full.encode())


# ---------------------------------------------------------------------------
# 木表現の直列化予算（`Expression.to_dict`）
# ---------------------------------------------------------------------------


def test_the_tree_representation_is_refused_before_it_is_built():
    dag = _shared_dag(40)
    with pair_failure_scope(("tree",), None), budget_policy_scope(
        _policy(serialization_bytes=1 << 20)
    ):
        started = time.perf_counter()
        with pytest.raises(ExpressionSizeBudgetExceeded) as caught:
            dag.to_dict()
        assert time.perf_counter() - started < 1.0
    assert caught.value.site == "core.expression.to_dict"


def test_the_shared_schema_adds_no_recursion_frames():
    """見積りと schema を共有しても、木表現の 1 段あたりの frame は増えない。

    `to_dict` は従来どおり再帰。1 段 3 frame（`_to_dict` → `_to_dict_active` →
    operand の内包表記）を保つので、変更前に書けた深さの式は今も書ける。
    """
    import sys

    node = Expression.parameter("p", 0, 4)
    depth = (sys.getrecursionlimit() // 3) - 60
    for index in range(depth):
        node = Expression.binary_op("INT_ADD", node, Expression.constant(index, 4))
    assert _actual(node.to_dict()) == estimate_legacy_dict_bytes(node)


def test_the_tree_representation_within_budget_is_unchanged():
    dag = _shared_dag(6)
    expected = dag.to_dict()  # scope の外 = 無制限
    with budget_policy_scope(_policy(serialization_bytes=1 << 20)):
        assert dag.to_dict() == expected


# ---------------------------------------------------------------------------
# D5s: 見積り >= 実際（encoder policy 共有）
# ---------------------------------------------------------------------------


_STRINGS = [
    "ascii",
    "日本語の名前",
    "😀 non-BMP 😀",
    'quote " and back\\slash',
    "newline\n tab\t cr\r bs\b ff\f",
    "control \x00\x01\x1f del \x7f",
    "long " * 5000,
]


def _actual(value, policy=RESULT_JSON_POLICY):
    return len(json.dumps(
        value, ensure_ascii=policy.ensure_ascii, sort_keys=policy.sort_keys,
        separators=policy.separators,
    ).encode("utf-8"))


@pytest.mark.parametrize("ensure_ascii", [False, True])
def test_d5s_value_estimate_matches_the_encoder_for_every_character_class(ensure_ascii):
    policy = JsonEncodingPolicy(ensure_ascii=ensure_ascii)
    shared = {"k": _STRINGS, "日本": [1, 2.5, None, True, False]}
    values = [
        *_STRINGS,
        shared,
        [shared, shared, {"nested": shared}],
        {1: "int key", 20: "int"},
        {2.5: "float key"},
        {True: "bool"},
        {None: "none"},
        [float("nan"), float("inf"), -float("inf"), 10 ** 30, -7],
        (1, (2, (3,))),
    ]
    for value in values:
        assert policy.value_bytes(value) == _actual(value, policy)
        assert policy.encode_bounded(value, max_bytes=None) == json.dumps(
            value, ensure_ascii=ensure_ascii, sort_keys=True, separators=policy.separators,
        )


def test_d5s_estimate_saturates_and_stops_walking():
    visits = []

    def _count(_value):
        visits.append(1)
        return 10

    payload = [object() for _ in range(100_000)]
    assert RESULT_JSON_POLICY.value_bytes(payload, max_bytes=50, opaque_bytes=_count) == 51
    assert len(visits) < 10


def test_d5s_bounded_encoder_refuses_past_the_limit():
    value = {"text": "x" * 1000}
    exact = _actual(value)
    assert RESULT_JSON_POLICY.encode_bounded(value, max_bytes=exact) == json.dumps(
        value, ensure_ascii=False, sort_keys=True,
    )
    with pytest.raises(JsonOutputLimitExceeded):
        RESULT_JSON_POLICY.encode_bounded(value, max_bytes=exact - 1)


def _phi_dag():
    shared = Expression.binary_op(
        "INT_ADD", Expression.parameter("名前😀", 0, 4), Expression.constant(1, 4),
    )
    guard = Condition(Expression.binary_op("INT_SLESS", shared, Expression.constant(0, 4)))
    return Expression.phi(
        [(guard, shared), (guard.negate(), Expression.binary_op("INT_MULT", shared, shared))],
    )


@pytest.mark.parametrize(
    "build",
    [
        lambda: _shared_dag(10, name='long " \\ ' + "文字" * 500),
        lambda: _shared_dag(12),
        lambda: Expression.binary_op(
            "INT_ADD",
            *[Expression.binary_op("INT_ADD", Expression.parameter(f"p{i}", i, 4),
                                   Expression.constant(i, 4)) for i in range(2)],
        ),
        _phi_dag,
    ],
    ids=["shared-long-string", "shared-depth-12", "many-small", "phi-condition"],
)
def test_d5s_tree_estimate_equals_the_actual_tree_json(build):
    expr = build()
    actual = _actual(expr.to_dict())
    assert estimate_legacy_dict_bytes(expr) == actual
    assert estimate_legacy_dict_bytes(expr, max_bytes=actual - 1) == actual


def test_d5s_tree_estimate_of_a_depth_40_dag_is_linear():
    started = time.perf_counter()
    size = estimate_legacy_dict_bytes(_shared_dag(40))
    assert time.perf_counter() - started < 1.0
    assert size > 2 ** 40  # 木としての大きさ（作ってはいない）


# ---------------------------------------------------------------------------
# D4s / D7s: 出力だけが超える pair は receipt 前に UNKNOWN（pilot 無しは ERROR）
# ---------------------------------------------------------------------------


def _oversized_equivalent_plan(counterexample):
    def _plan(*_args, **_kwargs):
        result = create_mock_result(is_equivalent=True, solver_status=SolverStatus.UNSAT)
        result.sat_pair_info = {"case1_summary": "x" * 200_000, "case2_summary": "y"}
        result.counterexample = counterexample
        return result

    return _plan


def _small_output_policy():
    return _policy(serialization_bytes=64_000, envelope_headroom_bytes=16_000)


def _run_with_finish_spy(checker, plan, monkeypatch, *, analyses=None):
    seen = []
    original = production_boundary._profiled_finish

    def _spy(connector, session, result):
        seen.append((result.is_equivalent, _reason_ids(result)))
        evidence = original(connector, session, result)
        seen.append("finished")
        return evidence

    monkeypatch.setattr(production_boundary, "_profiled_finish", _spy)
    analysis1, analysis2 = analyses or _analyses()
    result = _run_pair(
        analyze=_analyze_from(analysis1, analysis2), stage_plan=plan, checker=checker,
    )
    return result, seen


def test_d4s_output_only_overflow_never_issues_an_equivalent_receipt(monkeypatch):
    analysis1, analysis2 = _analyses()
    dag = _shared_dag(40)
    analysis1.returns[0].value = dag  # 巨大 DAG を持つ解析（木に展開すると 2^40）
    counterexample = _CountingCounterexample({"x": 1})
    checker = _new_checker(_connector())
    checker.budget_policy = _small_output_policy()

    result, seen = _run_with_finish_spy(
        checker, _oversized_equivalent_plan(counterexample), monkeypatch,
        analyses=(analysis1, analysis2),
    )

    # finish（最初の不可逆な判定）へ渡ったのは限界の UNKNOWN だけ
    assert seen == [(None, [REASON]), "finished"]
    assert result.final_outcome == "UNKNOWN"
    assert result.decision_receipt.outcome.value == "UNKNOWN"
    assert _reason_ids(result) == [REASON]
    assert result.pair_stop_state == PairStopState.PAIR_TERMINAL_LIMITATION.value
    failure = result.diagnostics["failures"]["analysis_limitation"]
    assert failure["site"] == "checker.output_preparation.prepare"
    assert failure["disposition"] == "ATTRIBUTED_NEW_CAUSE"
    assert result.diagnostics["conditional_lane"]["skipped"] == "pair_terminal"

    # 確定の後は解析 object も巨大 DAG も辿らない
    walked = []
    monkeypatch.setattr(
        Expression, "_to_dict_active", lambda self, *_a, **_k: walked.append(self),
    )
    monkeypatch.setattr(
        "scripts.function_tracer_pcode.core.render_smt.render.render_smt_term",
        lambda *a, **k: walked.append(a),
    )
    calls_before = counterexample.calls
    envelope = build_final_result_envelope(result)
    assert walked == []
    assert counterexample.calls == calls_before
    payload = json.loads(envelope.text)
    assert payload["final_outcome"] == "UNKNOWN"
    assert [row["reason_id"] for row in payload["unknown_reasons"]] == [REASON]
    assert envelope.total_bytes <= 64_000
    assert payload["diagnostics"]["expression_budget"]["policy"]["serialization_bytes"] == 64_000


def test_d4s_within_budget_the_prepared_payload_equals_a_fresh_one(monkeypatch):
    counterexample = _CountingCounterexample({"x": 1})

    def _plan(*_args, **_kwargs):
        _emit_one_production_signal()
        result = create_mock_result(is_equivalent=None, solver_status=SolverStatus.UNKNOWN)
        result.sat_pair_info = {"case1_summary": "small", "case2_summary": "日本😀"}
        result.counterexample = counterexample
        return result

    checker = _new_checker(_connector())
    checker.budget_policy = _small_output_policy()
    result, seen = _run_with_finish_spy(checker, _plan, monkeypatch)
    assert result.prepared_semantic_payload is not None
    assert seen[0][1] != [REASON]
    calls_after_boundary = counterexample.calls
    prepared_view = result.to_dict()
    assert counterexample.calls == calls_after_boundary  # 準備済みの値を使う
    fresh = OutputPreparer(BudgetPolicy.unlimited()).prepare(result)
    assert counterexample.calls == calls_after_boundary + 1
    result.prepared_semantic_payload = fresh
    assert result.to_dict() == prepared_view


def test_d7s_without_a_pilot_output_overflow_is_an_unattributed_error(monkeypatch):
    checker = _new_checker(None)
    checker.budget_policy = _small_output_policy()
    result = _run_pair(
        analyze=_analyze_from(*_analyses()),
        stage_plan=_oversized_equivalent_plan(_CountingCounterexample({})),
        checker=checker,
    )
    assert result.is_equivalent is None
    assert result.error_message == "limitation_unattributed"
    assert result.failure_status == "limitation_unattributed"


# ---------------------------------------------------------------------------
# O-1〜O-4: 所有者の分離
# ---------------------------------------------------------------------------


def test_o1_every_field_has_exactly_one_owner_and_prepared_holds_no_authority_field():
    keys = [item.key for item in RESULT_FIELDS]
    assert len(keys) == len(set(keys))
    authority = set(fields_owned_by(FieldOwner.AUTHORITY))
    assert {
        "is_equivalent", "final_outcome", "decision_receipt", "unknown_reasons",
        "unknown_recovery_actions", "c_active_base", "q_open_base",
        "conditional_outcome", "conditional_decision_receipt", "error_message",
        "failure_status", "canonical_result_finalization_bundle",
    } <= authority
    result = create_mock_result(is_equivalent=None)
    prepared = OutputPreparer(BudgetPolicy.unlimited()).prepare(result)
    assert not (set(prepared.keys()) & authority)


def test_o1_the_authority_reason_replaces_the_legacy_one_everywhere(monkeypatch):
    """legacy reason A → finish が canonical reason B に置換 → JSON も B だけ。"""
    from scripts.function_tracer_pcode.checker.unknown_reason import (
        make_internal_v2_reason_diagnostic,
    )

    legacy_reason = "pure_call_semantics_unproven"

    def _plan(*_args, **_kwargs):
        _emit_one_production_signal()  # canonical 側の cause（B）
        result = create_mock_result(is_equivalent=None, solver_status=SolverStatus.UNKNOWN)
        result.unknown_reasons = [
            make_internal_v2_reason_diagnostic(legacy_reason, stage="S_TEST")
        ]
        return result

    checker = _new_checker(_connector())
    result, seen = _run_with_finish_spy(checker, _plan, monkeypatch)
    assert seen[0] == (None, [legacy_reason])
    canonical = _reason_ids(result)
    assert canonical and legacy_reason not in canonical
    prepared = result.prepared_semantic_payload
    assert (legacy_reason, "S_TEST") in prepared.raw_limitation_evidence
    payload = json.loads(build_final_result_envelope(result).text)
    assert [row["reason_id"] for row in payload["unknown_reasons"]] == canonical
    assert legacy_reason not in json.dumps(payload["unknown_reasons"])


def test_o2_authority_additions_after_preparation_do_not_re_expand_payload(monkeypatch):
    counterexample = _CountingCounterexample({"x": 1})

    def _plan(*_args, **_kwargs):
        _emit_one_production_signal()
        result = create_mock_result(is_equivalent=None, solver_status=SolverStatus.UNKNOWN)
        result.counterexample = counterexample
        return result

    def _lane(checker, result, *, projection):
        result.diagnostics = {**(result.diagnostics or {}), "conditional_lane": {"ran": True}}

    monkeypatch.setattr(production_boundary, "_run_conditional_lane", _lane)
    checker = _new_checker(_connector())
    result, _seen = _run_with_finish_spy(checker, _plan, monkeypatch)
    calls_after_boundary = counterexample.calls
    prepared = result.prepared_semantic_payload
    payload = json.loads(build_final_result_envelope(result).text)
    assert payload["diagnostics"]["conditional_lane"] == {"ran": True}
    assert payload["decision_receipt"]["outcome"] == result.decision_receipt.outcome.value
    assert result.prepared_semantic_payload is prepared
    assert counterexample.calls == calls_after_boundary  # 再展開 0


def test_o3_m3_a_new_diagnostic_field_is_one_output_row(monkeypatch):
    """M-3: 判定に関わらない field を 1 行足すだけで出る。判定・reason・準備は不変。"""
    from scripts.function_tracer_pcode.core.structural import structural_identity_digest

    def _plan(*_args, **_kwargs):
        _emit_one_production_signal()
        return create_mock_result(is_equivalent=None, solver_status=SolverStatus.UNKNOWN)

    dag = publish(_shared_dag(8))
    digest_before = structural_identity_digest(dag)
    checker = _new_checker(_connector())
    result, _seen = _run_with_finish_spy(checker, _plan, monkeypatch)
    prepared = result.prepared_semantic_payload
    before = json.loads(build_final_result_envelope(result).text)

    extra = OutputField(
        "extra_observation", FieldOwner.METADATA,
        lambda r: (True, {"observed": 1}), truncatable=True,
    )
    monkeypatch.setattr(output_preparation, "RESULT_FIELDS", RESULT_FIELDS + (extra,))
    after = json.loads(build_final_result_envelope(result).text)

    assert after["extra_observation"] == {"observed": 1}
    for key in ("final_outcome", "decision_receipt", "unknown_reasons", "c_active_base"):
        assert after[key] == before[key]
    assert result.prepared_semantic_payload is prepared
    assert structural_identity_digest(dag) == digest_before


def _decided_result():
    """authority が UNKNOWN を確定済みの結果（receipt は本物）。"""
    checker = _new_checker(_connector())

    def _plan(*_args, **_kwargs):
        _emit_one_production_signal()
        return create_mock_result(is_equivalent=None, solver_status=SolverStatus.UNKNOWN)

    return _run_pair(analyze=_analyze_from(*_analyses()), stage_plan=_plan, checker=checker)


def test_o4_authority_fields_fit_the_headroom_and_non_bmp_bytes_are_counted():
    result = _decided_result()
    natural = build_final_result_envelope(result)
    assert natural.total_bytes == len(natural.text.encode("utf-8"))
    result.diagnostics = {**(result.diagnostics or {}), "note": "😀" * 100}
    envelope = build_final_result_envelope(result)
    assert envelope.total_bytes == len(envelope.text.encode("utf-8"))


def test_o4_diagnostics_are_truncated_before_authority_fields():
    result = _decided_result()
    natural = build_final_result_envelope(result)
    diagnostics_bytes = RESULT_JSON_POLICY.value_bytes(natural.payload["diagnostics"])
    result.diagnostics = {**(result.diagnostics or {}), "stages": {"huge": "d" * 50_000}}
    limit = natural.total_bytes + 1_000
    prepared = result.prepared_semantic_payload
    result.prepared_semantic_payload = dataclasses.replace(
        prepared,
        plan=dataclasses.replace(prepared.plan, max_bytes=limit, headroom_bytes=limit - 1),
    )
    envelope = build_final_result_envelope(result)
    assert "diagnostics" in envelope.truncated_metadata
    assert envelope.payload["diagnostics"]["truncated"] is True
    assert envelope.payload["decision_receipt"] == natural.payload["decision_receipt"]
    assert envelope.payload["unknown_reasons"] == natural.payload["unknown_reasons"]
    assert envelope.total_bytes <= limit
    assert diagnostics_bytes > 0


def test_o4_an_authority_overflow_is_an_invariant_violation_not_a_limitation():
    result = _decided_result()
    decided = (result.final_outcome, result.decision_receipt)
    prepared = result.prepared_semantic_payload
    result.prepared_semantic_payload = dataclasses.replace(
        prepared,
        plan=dataclasses.replace(prepared.plan, max_bytes=200, headroom_bytes=100),
    )
    with pytest.raises(OutputEnvelopeInvariantViolation) as caught:
        build_final_result_envelope(result)
    assert not isinstance(caught.value, ExpressionSizeBudgetExceeded)
    # 判定は書き換えない
    assert (result.final_outcome, result.decision_receipt) == decided


def test_replacing_a_prepared_source_after_preparation_is_an_internal_error():
    result = create_mock_result(is_equivalent=None)
    result.prepared_semantic_payload = OutputPreparer(BudgetPolicy.unlimited()).prepare(result)
    result.sat_pair_info = {"changed": True}
    with pytest.raises(PreparedPayloadStale):
        result.to_dict()


def test_debug_trace_is_a_diagnostic_and_never_causes_a_limitation():
    result = create_mock_result(is_equivalent=None)
    result.debug_trace = SimpleNamespace(to_dict=lambda: {"records": ["t" * 50_000]})
    result.emit_debug_trace = True
    policy = _policy(serialization_bytes=40_000, envelope_headroom_bytes=10_000)
    prepared = OutputPreparer(policy).prepare(result)
    trace = dict(prepared.fields)["debug_trace"]
    assert trace["truncated"] is True and trace["field"] == "debug_trace"
    assert "debug_trace" in prepared.plan.to_diagnostic()["truncated_fields"]


def test_prepared_payload_for_a_directly_built_result_is_prepared_on_demand():
    result = create_mock_result(is_equivalent=True)
    assert result.prepared_semantic_payload is None
    prepared = prepared_payload_for(result)
    assert prepared.plan.max_bytes is None


# ---------------------------------------------------------------------------
# D2: 既定値 ON / 予算 OFF で出力が変わらない（予算内の入力）
# ---------------------------------------------------------------------------


def test_d2_production_defaults_do_not_change_the_render_corpus():
    """PR-22-C の描画 corpus（SMT / 木表現）は既定の予算の内側で不変。"""
    from scripts.function_tracer_pcode.tests.fixtures.render.corpus import build_corpus

    def _render_all():
        rendered = {}
        for name, spec in sorted(build_corpus().items()):
            expr = publish(spec["expression"])
            # 木表現（`to_dict`）は従来どおり再帰なので、Python の再帰制限に
            # 当たる深い case（C2 の線形 10,000 段）は SMT だけを比べる。
            tree = None
            if (expr.tree_size() or 0) < 2_000:
                try:
                    tree = json.dumps(expr.to_dict(), sort_keys=True, default=str)
                except TypeError as exc:  # 木表現を持たない形は同じ例外になること
                    tree = f"TypeError: {exc}"
            rendered[name] = (
                expression_to_smt(expr, float_mode=spec.get("float_mode", "uf")),
                tree,
            )
        return rendered

    unlimited = _render_all()
    with pair_failure_scope(("d2",), None) as ledger, budget_policy_scope(
        expression_budget_policy({})
    ):
        bounded = _render_all()
    assert bounded == unlimited
    assert ledger.pending_failure() is None


def test_d2_the_checker_uses_the_config_policy():
    checker = _new_checker(None)
    assert checker.budget_policy == expression_budget_policy()


# ---------------------------------------------------------------------------
# authority 確定後の予算超過は判定を変えない
# ---------------------------------------------------------------------------


def test_a_budget_hit_inside_the_conditional_lane_leaves_the_decision(monkeypatch):
    """lane は authority 確定の **後**。そこで予算に当たっても lane が fail closed
    になるだけで、確定した UNKNOWN と receipt は変わらない。"""
    from scripts.function_tracer_pcode.authority.decision import conditional_lane
    from scripts.function_tracer_pcode.core.budget_policy import (
        raise_expression_size_budget_exceeded,
    )

    def _plan(*_args, **_kwargs):
        _emit_one_production_signal()
        return create_mock_result(is_equivalent=None, solver_status=SolverStatus.UNKNOWN)

    def _exceeding_proof(*_args, **_kwargs):
        raise_expression_size_budget_exceeded(
            BudgetKind.RENDER_BYTES, observed=2, limit=1,
            site="core.render_smt.emit", target_key=("lane",),
        )

    monkeypatch.setattr(conditional_lane, "conditional_lane_is_eligible", lambda _d: True)
    monkeypatch.setattr(
        "scripts.function_tracer_pcode.proof.conditional_lane.run_conditional_proof",
        _exceeding_proof,
    )
    checker = _new_checker(_connector())
    result, seen = _run_with_finish_spy(checker, _plan, monkeypatch)
    lane = result.diagnostics["conditional_lane"]
    assert lane["conditional_lane"] == "failed"
    assert "ExpressionSizeBudgetExceeded" in lane["error"]
    assert result.final_outcome == "UNKNOWN"
    assert result.conditional_decision_receipt is None
    assert seen[-1] == "finished"


# ---------------------------------------------------------------------------
# CLI: headroom 契約の違反は ERROR（判定の書き換えではない）
# ---------------------------------------------------------------------------


def test_the_cli_reports_an_envelope_violation_as_an_internal_error(monkeypatch, tmp_path):
    from scripts.function_tracer_pcode.authority.contracts import Outcome
    from scripts.function_tracer_pcode.authority.decision.production_cutover import (
        CLI_EXIT_MATRIX,
    )
    from scripts.function_tracer_pcode.cli.commands import equivalence

    written = []
    monkeypatch.setattr(equivalence, "output_result", lambda text, *_a: written.append(text))
    decided = _decided_result()
    violation = OutputEnvelopeInvariantViolation("too big", max_bytes=10, requested_bytes=20)
    args = SimpleNamespace(output=None, quiet=True, verbose=False, debug=False)
    with pytest.raises(SystemExit) as exit_info:
        equivalence._emit_output_invariant_error_result(
            args, result=decided, violation=violation,
            binary1_path=str(tmp_path / "a"), binary2_path=str(tmp_path / "b"),
            func_name1="f", func_name2="f", start_time=time.time(),
        )
    assert exit_info.value.code == CLI_EXIT_MATRIX[Outcome.ERROR]
    block = next(text for text in written if "EQUIVALENCE_RESULT_JSON_BEGIN" in text)
    payload = json.loads(block.splitlines()[1])
    assert payload["final_outcome"] == "ERROR"
    assert payload["error_message"].startswith("OUTPUT_ENVELOPE_INVARIANT_VIOLATION")
    # 確定済みの判定は ERROR の証跡に残す（UNKNOWN にも書き換えない）
    assert "decided_outcome=UNKNOWN" in payload["error_message"]
    assert decided.decision_receipt.receipt_digest in payload["error_message"]


def test_growing_observations_reach_the_stage_journal_logarithmically(tmp_path):
    """kill された pair でも膨張の大きさを読めるよう、2 の冪を越えたときだけ残す。"""
    from scripts.function_tracer_pcode.core.stage_journal import (
        StageJournal,
        close_active_stage_journal,
        set_active_stage_journal,
    )
    from scripts.function_tracer_pcode.tests.unit.test_issue124b_stage_journal import (
        read_journal,
    )

    path = tmp_path / "budget.stage.jsonl"
    previous = set_active_stage_journal(StageJournal(path))
    try:
        with budget_policy_scope(BudgetPolicy.unlimited()):
            for value in range(1, 1025):
                enforce_budget(BudgetKind.EXPRESSION_NODES, value, site="s", target_key=())
    finally:
        close_active_stage_journal()
        set_active_stage_journal(previous)
    rows, _broken = read_journal(path)
    values = [
        row["payload"]["value"] for row in rows
        if row["payload"].get("note") == "expression_budget_observed"
    ]
    assert values == [1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024]

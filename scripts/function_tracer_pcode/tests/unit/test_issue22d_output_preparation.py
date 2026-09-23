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
from scripts.function_tracer_pcode.checker.debug_trace import Attempt, DebugTrace
from scripts.function_tracer_pcode.checker.output_preparation import (
    FieldOwner,
    OutputEnvelopeInvariantViolation,
    OutputField,
    OutputOptions,
    OutputPreparer,
    Overflow,
    PreparedField,
    PreparedPayloadStale,
    PreparedSemanticPayload,
    RESULT_FIELDS,
    build_final_result_envelope,
    fields_owned_by,
    prepared_payload_for,
)
from scripts.function_tracer_pcode.config.settings import (
    EXPRESSION_BUDGET_DEFAULTS,
    expression_budget_policy,
)
from scripts.function_tracer_pcode.core import Condition, Expression
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
    pair_failure_scope,
    reset_pair_failure_scopes,
)
from scripts.function_tracer_pcode.core.expression import estimate_legacy_dict_bytes
from scripts.function_tracer_pcode.core.json_encoding import (
    RESULT_JSON_POLICY,
    JsonBudgetExhausted,
    JsonEncodingPolicy,
    JsonOutputLimitExceeded,
    JsonValueRejected,
    PreparedJson,
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


def _field_value(prepared, key):
    """準備済み payload の 1 field の値（canonical な複製）。"""
    for row in prepared.fields:
        if row.key == key:
            return None if row.json is None else row.json.value()
    raise KeyError(key)


#: 区切りを変えた policy（見積り・準備・書き出しが同じ規則で追従することを確かめる）
_POLICIES = [
    JsonEncodingPolicy(),
    JsonEncodingPolicy(ensure_ascii=True),
    JsonEncodingPolicy(item_separator=",", key_separator=":"),
    JsonEncodingPolicy(ensure_ascii=True, item_separator=" ,  ", key_separator=" :"),
]


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
    # 所有 scope は大きくなり得るので決定的な digest に落としてある
    assert isinstance(owner, str) and len(owner) == 32 and op_key
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


@pytest.mark.parametrize("policy", _POLICIES, ids=["default", "ascii", "compact", "odd"])
def test_d5s_value_estimate_matches_the_encoder_for_every_character_class(policy):
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
        assert policy.measure(value) == _actual(value, policy)
        assert policy.measure_elements(value) == _actual(value, policy)
        prepared = policy.prepare(value)
        # 準備した値は canonical な JSON（json.loads と同じ形）で、大きさは実際の byte
        assert json.dumps(prepared.value(), sort_keys=True) == json.dumps(
            json.loads(json.dumps(value)), sort_keys=True,
        )
        assert prepared.encoded_bytes == _actual(value, policy)
        assert prepared.encoded_bytes == len(
            policy.encode_bounded(prepared.value(), max_bytes=None).encode("utf-8")
        )
        assert policy.encode_bounded(value, max_bytes=None) == json.dumps(
            value, ensure_ascii=policy.ensure_ascii, sort_keys=True, separators=policy.separators,
        )


def test_d5s_estimate_saturates_and_stops_walking():
    visits = []

    def _count(_value):
        visits.append(1)
        return 10

    payload = [object() for _ in range(100_000)]
    with pytest.raises(JsonBudgetExhausted):
        RESULT_JSON_POLICY.measure(payload, max_bytes=50, opaque_bytes=_count)
    assert len(visits) < 10
    # 準備（出力）では JSON source でない値は数えずに拒む
    with pytest.raises(JsonValueRejected):
        RESULT_JSON_POLICY.prepare(payload, max_bytes=50)


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
        lambda r, o: {"observed": 1}, Overflow.TRUNCATE,
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
    diagnostics_bytes = RESULT_JSON_POLICY.measure(natural.payload["diagnostics"])
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
    # 準備の後に A の元を差し替えるのは、出力に現れない更新（書く側で拒む）
    with pytest.raises(PreparedPayloadStale):
        result.sat_pair_info = {"changed": True}
    # B / C は authority 確定後に決まるので差し替えてよい
    result.diagnostics = {"after": True}


def test_debug_trace_is_a_diagnostic_and_never_causes_a_limitation():
    result = create_mock_result(is_equivalent=None)
    result.debug_trace = _trace_with_attempts(1, final_smt="t" * 50_000)
    result.emit_debug_trace = True
    policy = _policy(serialization_bytes=40_000, envelope_headroom_bytes=10_000)
    prepared = OutputPreparer(policy).prepare(result)
    trace = _field_value(prepared, "debug_trace")
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

    from scripts.function_tracer_pcode.core.errors import current_pair_ledger

    pair_ledgers = []

    def _plan(*_args, **_kwargs):
        pair_ledgers.append(current_pair_ledger())
        _emit_one_production_signal()
        return create_mock_result(is_equivalent=None, solver_status=SolverStatus.UNKNOWN)

    lane_ledgers = []

    def _exceeding_proof(*_args, **_kwargs):
        lane_ledgers.append(current_pair_ledger())
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
    assert lane == {
        "conditional_lane": "stopped_by_limitation",
        "reason_id": REASON,
        "site": "core.render_smt.emit",
        "swallowed": False,
    }
    assert result.final_outcome == "UNKNOWN"
    assert result.conditional_decision_receipt is None
    assert seen[-1] == "finished"
    # lane は pair とは別の台帳で走り、限界はその台帳に閉じる。pair の台帳は lane の
    # 後も何も記録していない（result 側の stop state は lane より前に確定しているので、
    # 台帳そのものを見る）。
    (pair_ledger,) = set(pair_ledgers)
    (lane_ledger,) = lane_ledgers
    assert lane_ledger is not pair_ledger
    assert lane_ledger.stop_state() is PairStopState.PAIR_TERMINAL_LIMITATION
    assert pair_ledger.stop_state() is PairStopState.NONE
    assert pair_ledger.recorded_failure_count() == 0
    assert result.pair_stop_state is None


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


def test_production_defaults_stop_an_exponential_tree_before_building_it():
    """既定値（config）のままで、指数的な木表現は作る前に止まる。"""
    with pair_failure_scope(("defaults",), None) as ledger, budget_policy_scope(
        expression_budget_policy({})
    ):
        started = time.perf_counter()
        with pytest.raises(ExpressionSizeBudgetExceeded) as caught:
            _shared_dag(40).to_dict()
        assert time.perf_counter() - started < 1.0
    assert caught.value.site == "core.expression.to_dict"
    assert ledger.stop_state() is PairStopState.PAIR_TERMINAL_LIMITATION


def test_the_frozen_size_cache_returns_the_same_exact_size_and_skips_the_walk(monkeypatch):
    """凍結済み node の大きさは再利用する（snapshot は同じ解析を何度も書く）。"""
    expr = publish(_shared_dag(12, name="名前"))
    actual = _actual(expr.to_dict())
    assert estimate_legacy_dict_bytes(expr) == actual
    built = []
    original = Expression._to_dict_active

    def _counting(self, *args, **kwargs):
        built.append(self)
        return original(self, *args, **kwargs)

    monkeypatch.setattr(Expression, "_to_dict_active", _counting)
    assert estimate_legacy_dict_bytes(expr) == actual
    assert built == []  # 2 回目は 1 node も組み立てない
    # 未凍結の式は cache しない（書き換わり得る）
    loose = _shared_dag(3)
    estimate_legacy_dict_bytes(loose)
    estimate_legacy_dict_bytes(loose)
    assert len(built) == 2 * 4


def test_d6s_full_identity_of_a_depth_40_dag_does_not_expand_the_tree():
    """D6s: 予算超過の target に使う identity も、比較も、DAG のまま（木展開しない）。"""
    from scripts.function_tracer_pcode.core.structural import (
        structural_equals,
        structural_identity_digest,
    )

    left = publish(_shared_dag(40))
    right = publish(_shared_dag(40))
    started = time.perf_counter()
    assert structural_equals(left, right)
    assert structural_identity_digest(left) == structural_identity_digest(right)
    assert time.perf_counter() - started < 1.0


# ---------------------------------------------------------------------------
# bounded preparation の adversarial test（巨大な producer でも写すのを止める）
# ---------------------------------------------------------------------------


def _peak_allocation(function):
    import tracemalloc

    tracemalloc.start()
    try:
        function()
        return tracemalloc.get_traced_memory()[1]
    finally:
        tracemalloc.stop()


def _huge_result(**fields):
    result = create_mock_result(is_equivalent=True)
    for name, value in fields.items():
        setattr(result, name, value)
    return result


_SMALL = BudgetPolicy(serialization_bytes=64_000, envelope_headroom_bytes=16_000)


def test_a_huge_semantic_leaf_is_refused_without_being_copied():
    """50 MB の文字列を持つ反例でも、予算に届いた時点で写すのをやめて限界にする。"""
    huge = "日" * (50 * 1024 * 1024 // 3)
    result = _huge_result(
        counterexample=_CountingCounterexample({"x": huge}),
    )

    def _prepare():
        with pair_failure_scope(("huge-leaf",), None), budget_policy_scope(_SMALL):
            with pytest.raises(ExpressionSizeBudgetExceeded):
                OutputPreparer(_SMALL).prepare(result)

    started = time.perf_counter()
    peak = _peak_allocation(_prepare)
    assert time.perf_counter() - started < 1.0
    assert peak < 4 * 1024 * 1024  # 巨大な文字列を encode / 複製していない


def test_many_small_nodes_stop_at_the_budget():
    result = _huge_result(sat_pair_info={"cases": list(range(2_000_000))})

    def _prepare():
        with pair_failure_scope(("many-small",), None), budget_policy_scope(_SMALL):
            with pytest.raises(ExpressionSizeBudgetExceeded):
                OutputPreparer(_SMALL).prepare(result)

    started = time.perf_counter()
    peak = _peak_allocation(_prepare)
    assert time.perf_counter() - started < 1.0
    assert peak < 4 * 1024 * 1024  # 2,000,000 要素の写しを作っていない


def _trace_with_attempts(count, *, final_smt="(assert true)", events=0):
    """本物の `DebugTrace`（attempt と causal event を大量に持てる）。"""
    from scripts.function_tracer_pcode.checker.debug_trace import (
        AttemptIdentity,
        ProofCompletionEvent,
    )

    trace = DebugTrace(planned_phases=["P0_BASE"], known_phases=["P0_BASE"])
    for index in range(count):
        trace.add_attempt(Attempt(
            attempt_id=index, retry_count=0, phase="P0_BASE", stage_path=["P0_BASE"],
            strategy="pairwise", result=None, transition_reason="UNKNOWN",
            final_smt=final_smt, solver_results={"all_results": []},
        ))
    identity = AttemptIdentity("pairwise", 0)
    for index in range(events):
        trace.add_proof_completion(ProofCompletionEvent(
            completion_id=("c", index), proof_requirement_id={"k": index},
            proof_artifact_ref=("a", index), proof_status="ok",
            completed_at_attempt=identity,
        ))
    return trace


def test_a_huge_diagnostic_is_replaced_by_a_marker_without_being_copied(monkeypatch):
    """本物の DebugTrace に大量の attempt / event を持たせても、全体の `to_dict()` を
    作らずに予算で止まり、marker に置き換わる（判定は変えない）。"""
    trace = _trace_with_attempts(20_000, final_smt="t" * 1024, events=20_000)
    result = _huge_result(debug_trace=trace, emit_debug_trace=True)
    views = []
    original_view = Attempt.json_view

    def _counting_view(self):
        views.append(self)
        return original_view(self)

    monkeypatch.setattr(Attempt, "json_view", _counting_view)
    monkeypatch.setattr(
        DebugTrace, "to_dict", lambda self: pytest.fail("the whole trace was built"),
    )
    holder = {}

    def _prepare():
        holder["prepared"] = OutputPreparer(_SMALL).prepare(result)

    started = time.perf_counter()
    peak = _peak_allocation(_prepare)
    assert time.perf_counter() - started < 1.0
    prepared = holder["prepared"]
    marker = _field_value(prepared, "debug_trace")
    assert marker["truncated"] is True and marker["field"] == "debug_trace"
    assert "debug_trace" in prepared.plan.to_diagnostic()["truncated_fields"]
    assert len(views) < 100  # 予算に届くまでの attempt しか表現していない
    assert peak < 4 * 1024 * 1024


def test_a_shared_subtree_is_counted_per_reference_like_the_encoder():
    shared = {"name": "共有😀", "items": list(range(50))}
    value = {"left": shared, "right": [shared, shared], "nested": {"again": shared}}
    prepared = RESULT_JSON_POLICY.prepare(value)
    projected = prepared.value()
    assert projected == value
    assert projected["left"] is not shared  # 写しは live な値と共有しない
    assert prepared.encoded_bytes == _actual(value)


def test_deeply_nested_containers_are_walked_without_python_recursion():
    shallow = []
    node = shallow
    for _ in range(300):
        node.append([])
        node = node[-1]
    prepared = RESULT_JSON_POLICY.prepare(shallow)
    assert prepared.value() == shallow and prepared.encoded_bytes == _actual(shallow)

    deep = []
    node = deep
    for _ in range(100_000):
        node.append([])
        node = node[-1]
    started = time.perf_counter()
    assert RESULT_JSON_POLICY.measure(deep) == 2 * 100_001
    with pytest.raises(JsonBudgetExhausted):
        RESULT_JSON_POLICY.prepare(deep, max_bytes=1000)
    assert time.perf_counter() - started < 2.0


@pytest.mark.parametrize("policy", _POLICIES, ids=["default", "ascii", "compact", "odd"])
def test_projection_counts_cjk_non_bmp_and_escapes_like_the_encoder(policy):
    value = {text: [text, {"k": text}] for text in _STRINGS[:-1]}
    prepared = policy.prepare(value)
    assert prepared.value() == value
    assert prepared.encoded_bytes == _actual(value, policy)
    # 1 byte 手前の上限なら写しを作らずに止まる
    with pytest.raises(JsonBudgetExhausted):
        policy.prepare(value, max_bytes=prepared.encoded_bytes - 1)


def test_a_long_string_is_counted_in_chunks_and_stops_early():
    text = "😀" * 5_000_000
    started = time.perf_counter()
    assert RESULT_JSON_POLICY.string_bytes(text, max_bytes=100) == 101
    assert time.perf_counter() - started < 0.1
    assert RESULT_JSON_POLICY.string_bytes(text[:70_000]) == len(
        json.dumps(text[:70_000], ensure_ascii=False).encode()
    )


# ---------------------------------------------------------------------------
# 解析 1 件分の直列化（aggregate）
# ---------------------------------------------------------------------------


def _analysis_with_trees(count, depth=4):
    from scripts.function_tracer_pcode.core.analysis import ReturnInfo

    analysis = create_mock_analysis("func1", return_type="int")
    analysis.returns = [
        ReturnInfo(address=f"0x{index:x}", conditions=[], value=_shared_dag(depth, name=f"p{index}"))
        for index in range(count)
    ]
    return analysis


def test_the_snapshot_aggregate_refuses_before_building_the_tree_that_overflows(monkeypatch):
    """1 つずつは小さい木が集まって予算を超える snapshot は、超える木を作る前に止まる。"""
    from scripts.function_tracer_pcode.proof.obligations.snapshot import AnalysisSnapshot

    analysis = _analysis_with_trees(200)
    one_tree = estimate_legacy_dict_bytes(analysis.returns[0].value)
    built = []
    original = Expression._to_dict

    def _counting(self, active):
        if not active:
            built.append(self)
        return original(self, active)

    monkeypatch.setattr(Expression, "_to_dict", _counting)
    policy = BudgetPolicy(serialization_bytes=one_tree * 50, envelope_headroom_bytes=0)
    with pair_failure_scope(("aggregate",), None) as ledger, budget_policy_scope(policy):
        with pytest.raises(ExpressionSizeBudgetExceeded) as caught:
            AnalysisSnapshot.from_function_analysis(analysis)
    assert caught.value.site == "proof.obligations.snapshot.from_function_analysis"
    assert "budget=serialization_bytes" in caught.value.evidence_refs
    assert len(built) < 50  # 超えた木は作っていない
    assert ledger.stop_state() is PairStopState.PAIR_TERMINAL_LIMITATION


def test_the_aggregate_distinct_node_budget_counts_shared_nodes_once():
    from scripts.function_tracer_pcode.core.analysis import ReturnInfo

    shared = _shared_dag(20)
    analysis = create_mock_analysis("func1", return_type="int")
    analysis.returns = [
        ReturnInfo(address=f"0x{index}", conditions=[], value=shared) for index in range(3)
    ]
    # 21 distinct node（共有は 1 回）: 21 なら通り、20 なら止まる
    with pair_failure_scope(("nodes-ok",), None), budget_policy_scope(
        BudgetPolicy(serialization_nodes=21)
    ):
        analysis.to_dict()
    with pair_failure_scope(("nodes",), None), budget_policy_scope(
        BudgetPolicy(serialization_nodes=20)
    ):
        with pytest.raises(ExpressionSizeBudgetExceeded) as caught:
            analysis.to_dict()
    assert "budget=serialization_nodes" in caught.value.evidence_refs
    assert caught.value.site == "core.analysis.FunctionReturnAnalysis.to_dict"


# ---------------------------------------------------------------------------
# authority 前 / 後の限界
# ---------------------------------------------------------------------------


def test_a_render_overflow_before_authority_is_a_pair_limitation(monkeypatch):
    """authority 確定 **前**（解析中）の描画超過は pair の限界: UNKNOWN + receipt。"""
    expr = _published_wide_expression()
    full = expression_to_smt(expr)
    analysis1, analysis2 = _analyses()

    def _analyze(self, name, timeout):
        if name == "func1":
            expression_to_smt(expr)  # solver へ渡す描画が予算を超える
        return analysis1 if name == "func1" else analysis2

    def _stage_plan(*_args, **_kwargs):
        return create_mock_result(is_equivalent=True, solver_status=SolverStatus.UNSAT)

    checker = _new_checker(_connector())
    checker.budget_policy = _policy(render_bytes=len(full) - 1)
    seen = []
    original = production_boundary._profiled_finish

    def _spy(connector, session, result):
        seen.append((result.is_equivalent, _reason_ids(result)))
        return original(connector, session, result)

    monkeypatch.setattr(production_boundary, "_profiled_finish", _spy)
    result = _run_pair(analyze=_analyze, stage_plan=_stage_plan, checker=checker)
    assert seen == [(None, [REASON])]
    assert result.final_outcome == "UNKNOWN"
    assert result.pair_stop_state == PairStopState.PAIR_TERMINAL_LIMITATION.value
    assert result.diagnostics["failures"]["analysis_limitation"]["site"] == "core.render_smt.emit"


def test_a_post_decision_scope_keeps_its_failures_out_of_the_pair_ledger():
    """authority 確定 **後** の計算の限界は、その計算の台帳に閉じる（pair は不変）。"""
    from scripts.function_tracer_pcode.authority.decision.conditional_lane import (
        post_decision_failure_scope,
    )
    from scripts.function_tracer_pcode.core.errors import current_pair_ledger

    expr = _published_wide_expression()
    full = expression_to_smt(expr)
    with pair_failure_scope(("pair",), None) as pair_ledger, budget_policy_scope(
        _policy(render_bytes=len(full) - 1)
    ):
        with post_decision_failure_scope() as lane_ledger:
            assert current_pair_ledger() is lane_ledger
            with pytest.raises(ExpressionSizeBudgetExceeded):
                expression_to_smt(expr)
        assert current_pair_ledger() is pair_ledger
        assert lane_ledger.pending_failure().exception.reason_id == REASON
        assert pair_ledger.pending_failure() is None
        assert pair_ledger.stop_state() is PairStopState.NONE


def test_the_boundary_prepares_the_output_before_finish(monkeypatch):
    seen = []
    original = production_boundary._profiled_finish

    def _spy(connector, session, result):
        seen.append(type(result.prepared_semantic_payload) is PreparedSemanticPayload)
        return original(connector, session, result)

    monkeypatch.setattr(production_boundary, "_profiled_finish", _spy)

    def _plan(*_args, **_kwargs):
        _emit_one_production_signal()
        return create_mock_result(is_equivalent=None, solver_status=SolverStatus.UNKNOWN)

    _run_pair(analyze=_analyze_from(*_analyses()), stage_plan=_plan, checker=_new_checker(_connector()))
    assert seen == [True]


# ---------------------------------------------------------------------------
# 出力 option は準備時に 1 回だけ決まる
# ---------------------------------------------------------------------------


def _traced_result(emit):
    result = create_mock_result(is_equivalent=None)
    result.debug_trace = _trace_with_attempts(1)
    result.emit_debug_trace = emit
    return result


@pytest.mark.parametrize("prepared_with, flipped_to", [(True, False), (False, True)])
def test_the_debug_option_is_fixed_when_the_output_is_prepared(prepared_with, flipped_to):
    result = _traced_result(prepared_with)
    result.prepared_semantic_payload = OutputPreparer(BudgetPolicy.unlimited()).prepare(result)
    result.emit_debug_trace = flipped_to  # 準備の後で flag を変えても
    payload = result.to_dict()
    envelope = build_final_result_envelope(result)
    # 添付の有無は準備時の option のまま（to_dict と最終 envelope で同じ）
    assert ("debug_trace" in payload) is prepared_with
    assert ("debug_trace" in envelope.payload) is prepared_with


def test_the_smt_formula_is_a_prepared_artifact_that_never_blocks_a_decision():
    from scripts.function_tracer_pcode.checker.output_preparation import prepared_smt_formula

    result = create_mock_result(is_equivalent=True)
    result.smt_formula = "(assert true)" * 10_000
    small = BudgetPolicy(serialization_bytes=20_000, envelope_headroom_bytes=0)
    # 頼まれていなければ準備しない
    not_asked = OutputPreparer(BudgetPolicy.unlimited()).prepare(result, OutputOptions())
    assert not_asked.smt_formula.text is None
    # 頼まれて収まれば準備済みの文字列、収まらなければ省く（限界にしない）
    asked = OutputOptions(include_smt_formula=True)
    with pair_failure_scope(("formula",), None) as ledger, budget_policy_scope(small):
        result.prepared_semantic_payload = OutputPreparer(small).prepare(result, asked)
        assert ledger.pending_failure() is None
    artifact = prepared_smt_formula(result)
    assert artifact.text is None and artifact.omitted_over_bytes == 20_000
    result.prepared_semantic_payload = OutputPreparer(BudgetPolicy.unlimited()).prepare(result, asked)
    assert prepared_smt_formula(result).text == result.smt_formula


def test_metadata_counters_are_truncated_not_turned_into_a_limitation():
    """診断カウンタが大きくても、pair terminal な UNKNOWN にはならない。"""
    result = _decided_result()
    result.pairwise_debug_stats = {f"k{index}": index for index in range(200_000)}
    prepared = result.prepared_semantic_payload
    limit = prepared.plan.prepared_bytes + 400_000
    result.prepared_semantic_payload = dataclasses.replace(
        prepared,
        plan=dataclasses.replace(prepared.plan, max_bytes=limit, headroom_bytes=limit - 1),
    )
    envelope = build_final_result_envelope(result)
    assert "pairwise_debug_stats" in envelope.truncated_metadata
    assert envelope.payload["pairwise_debug_stats"]["truncated"] is True
    assert envelope.payload["final_outcome"] == result.final_outcome


def test_node_counting_stops_once_the_budget_is_known_to_be_exceeded():
    """distinct node の計数も予算の分までしか辿らない（数えること自体を有界に）。"""
    node = Expression.parameter("p", 0, 4)
    for index in range(200_000):
        node = Expression.binary_op("INT_ADD", node, Expression.constant(index, 4))
    meter = SemanticGraphMeter()
    started = time.perf_counter()
    meter.add_root(node, max_distinct=100)
    assert time.perf_counter() - started < 0.1
    assert meter.distinct_nodes == 101


def test_a_swallowed_limitation_after_authority_still_stops_the_lane(monkeypatch):
    """確定後の consumer の中で限界が握り潰されても、lane は結果を作らない。"""
    from scripts.function_tracer_pcode.authority.decision import conditional_lane
    from scripts.function_tracer_pcode.core.budget_policy import (
        raise_expression_size_budget_exceeded,
    )

    def _plan(*_args, **_kwargs):
        _emit_one_production_signal()
        return create_mock_result(is_equivalent=None, solver_status=SolverStatus.UNKNOWN)

    def _swallowing_proof(*_args, **_kwargs):
        try:
            raise_expression_size_budget_exceeded(
                BudgetKind.RENDER_BYTES, observed=2, limit=1,
                site="core.render_smt.emit", target_key=("lane",),
            )
        except Exception:
            pass  # 深い broad except が握り潰し、計算を「成功」として続けた
        return SimpleNamespace(
            assumption_set=("a",), decisive=True, non_decisive_reasons=(), diagnostics={},
        )

    monkeypatch.setattr(conditional_lane, "conditional_lane_is_eligible", lambda _d: True)
    monkeypatch.setattr(
        "scripts.function_tracer_pcode.proof.conditional_lane.run_conditional_proof",
        _swallowing_proof,
    )
    result, _seen = _run_with_finish_spy(_new_checker(_connector()), _plan, monkeypatch)
    assert result.diagnostics["conditional_lane"] == {
        "conditional_lane": "stopped_by_limitation",
        "reason_id": REASON,
        "site": "core.render_smt.emit",
        "swallowed": True,
    }
    assert result.conditional_decision_receipt is None
    assert result.final_outcome == "UNKNOWN"


# ---------------------------------------------------------------------------
# snapshot 全体の aggregate（式は小さいが木以外の値が巨大）
# ---------------------------------------------------------------------------


def _snapshot_analysis():
    return create_mock_analysis("func1", return_type="int")


def _unknown_outcomes(count):
    from scripts.function_tracer_pcode.core.analysis import UnknownOutcome

    return [
        UnknownOutcome(guard=(), reason=f"reason-{index}", evidence={"index": index})
        for index in range(count)
    ]


@pytest.mark.parametrize(
    "field_name, build",
    [
        ("analysis_notes", lambda: [f"note-{index}" for index in range(300_000)]),
        (
            "completed_recovery_proof_evidence",
            lambda: [("evidence", index, "x" * 20) for index in range(200_000)],
        ),
        ("unknown_outcomes", lambda: _unknown_outcomes(100_000)),
        ("signature_hypotheses", lambda: [{"h": index} for index in range(200_000)]),
    ],
)
def test_a_snapshot_with_small_expressions_but_huge_other_payload_stops_early(
    monkeypatch, field_name, build,
):
    """式は小さくても、解析 1 件分の表現が予算を超える snapshot は途中で止まる。"""
    from scripts.function_tracer_pcode.core.analysis import UnknownOutcome
    from scripts.function_tracer_pcode.proof.obligations.snapshot import AnalysisSnapshot

    analysis = _snapshot_analysis()
    setattr(analysis, field_name, build())
    records = []
    original = UnknownOutcome.to_dict

    def _counting(self):
        records.append(self)
        return original(self)

    monkeypatch.setattr(UnknownOutcome, "to_dict", _counting)
    policy = BudgetPolicy(serialization_bytes=64_000, envelope_headroom_bytes=0)

    def _snapshot():
        with pair_failure_scope(("huge-snapshot", field_name), None), budget_policy_scope(policy):
            with pytest.raises(ExpressionSizeBudgetExceeded) as caught:
                AnalysisSnapshot.from_function_analysis(analysis)
        return caught.value

    caught = []
    started = time.perf_counter()
    peak = _peak_allocation(lambda: caught.append(_snapshot()))
    assert time.perf_counter() - started < 2.0
    (exc,) = caught
    assert exc.site == "proof.obligations.snapshot.from_function_analysis"
    assert "budget=serialization_bytes" in exc.evidence_refs
    assert peak < 4 * 1024 * 1024  # 巨大な値を写し終えてから測っていない
    assert len(records) < 5_000  # record は予算に届くまでしか作っていない


def test_many_small_fields_exceed_the_snapshot_aggregate_together():
    """どの field も単独では予算内だが、合計が超える snapshot は止まる。"""
    from scripts.function_tracer_pcode.proof.obligations.snapshot import AnalysisSnapshot

    analysis = _snapshot_analysis()
    analysis.analysis_notes = [f"n{index}" for index in range(3_000)]
    analysis.unknown_event_reasons = [f"u{index}" for index in range(3_000)]
    analysis.signature_hypotheses = [{"h": index} for index in range(3_000)]
    sizes = [
        RESULT_JSON_POLICY.measure(getattr(analysis, name))
        for name in ("analysis_notes", "unknown_event_reasons", "signature_hypotheses")
    ]
    limit = max(sizes) + min(sizes) // 2  # どれも単独では収まり、合計は超える
    assert sum(sizes) > limit
    policy = BudgetPolicy(serialization_bytes=limit, envelope_headroom_bytes=0)
    for name in ("analysis_notes", "unknown_event_reasons", "signature_hypotheses"):
        assert RESULT_JSON_POLICY.measure(getattr(analysis, name)) < limit
    with pair_failure_scope(("many-small-fields",), None) as ledger, budget_policy_scope(policy):
        with pytest.raises(ExpressionSizeBudgetExceeded) as caught:
            AnalysisSnapshot.from_function_analysis(analysis)
    assert "budget=serialization_bytes" in caught.value.evidence_refs
    assert ledger.stop_state() is PairStopState.PAIR_TERMINAL_LIMITATION
    # 予算内なら snapshot の値は予算の scope の外と同じ
    small = _snapshot_analysis()
    outside = AnalysisSnapshot.from_function_analysis(small)
    with pair_failure_scope(("small",), None), budget_policy_scope(expression_budget_policy({})):
        inside = AnalysisSnapshot.from_function_analysis(small)
    assert inside.semantic_fingerprint == outside.semantic_fingerprint


def test_the_snapshot_counts_the_whole_representation_exactly():
    """aggregate が数える byte = snapshot に入る to_dict の JSON byte（木を含めて）。"""
    from scripts.function_tracer_pcode.core.budget_policy import serialization_scope

    analysis = _analysis_with_trees(5)
    analysis.analysis_notes = ["日本語😀", 'q"\\']
    analysis.unknown_outcomes = _unknown_outcomes(3)
    with budget_policy_scope(expression_budget_policy({})):
        with serialization_scope(site="t", target_parts=("t",)) as work:
            payload = analysis.to_dict()
            counted = work.total_bytes
    # 数えた byte = `to_dict` の値を実際に JSON にした byte（木も木以外も framing も）
    assert counted == _actual(payload)


# ---------------------------------------------------------------------------
# prepared payload の型契約（canonical JSON だけ・authority 前に拒否）
# ---------------------------------------------------------------------------


class _Opaque:
    pass


def test_an_opaque_object_is_rejected_before_authority(monkeypatch):
    """A の field に JSON でない object があれば、finish の前に内部エラーになる。"""

    def _plan(*_args, **_kwargs):
        _emit_one_production_signal()
        result = create_mock_result(is_equivalent=True, solver_status=SolverStatus.UNSAT)
        result.sat_pair_info = {"model": _Opaque()}
        return result

    checker = _new_checker(_connector())
    result, seen = _run_with_finish_spy(checker, _plan, monkeypatch)
    # EQ の receipt は発行されない: 内部エラーは finish ではなく既存の ERROR の
    # durable 化へ進む（finish は一度も EQ を受け取らない）
    assert all(item == "finished" or item[0] is not True for item in seen)
    assert result.final_outcome == "ERROR"
    assert result.failure_status == "internal_exception"
    assert "JsonValueRejected" in result.error_message
    prepared = result.prepared_semantic_payload
    assert all(row.json is None or type(row.json) is PreparedJson for row in prepared.fields)
    # 書き出しは型変換なしで通る（authority 後に型エラーが見つかる経路は無い）
    payload = json.loads(build_final_result_envelope(result).text)
    assert payload["final_outcome"] == "ERROR"
    assert "model" not in json.dumps(payload.get("sat_pair_info"))


def test_the_prepared_payload_accepts_only_prepared_json():
    raw = {"model": _Opaque()}
    with pytest.raises(TypeError):
        PreparedJson(raw, 10, RESULT_JSON_POLICY, _token=object())
    with pytest.raises(TypeError):
        PreparedField("sat_pair_info", raw, "json")
    good = OutputPreparer(BudgetPolicy.unlimited()).prepare(create_mock_result(is_equivalent=None))
    with pytest.raises(TypeError):
        dataclasses.replace(good, fields=good.fields + (("sat_pair_info", raw),))
    with pytest.raises(TypeError):
        # B の field は A に入れられない
        dataclasses.replace(
            good, fields=(PreparedField("decision_receipt", RESULT_JSON_POLICY.prepare({}), "json"),),
        )


def test_mutating_live_objects_after_preparation_does_not_leak_into_the_output():
    result = create_mock_result(is_equivalent=None)
    result.sat_pair_info = {"case1_summary": "before"}
    result.constrained_fragments = ["f1"]
    result.prepared_semantic_payload = OutputPreparer(BudgetPolicy.unlimited()).prepare(result)
    # live な container を中身だけ書き換える（差し替えではないので書く側では拒めない）
    result.sat_pair_info["case1_summary"] = "after"
    result.constrained_fragments.append("f2")
    payload = result.to_dict()
    assert payload["sat_pair_info"] == {"case1_summary": "before"}
    assert payload["constrained_fragments"] == ["f1"]
    # 受け取った出力を壊しても準備済みの値は変わらない
    payload["sat_pair_info"]["case1_summary"] = "tampered"
    assert build_final_result_envelope(result).payload["sat_pair_info"] == {
        "case1_summary": "before",
    }


# ---------------------------------------------------------------------------
# JSON の framing は policy だけが持つ（区切りを変えても見積り == 書き出し）
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("policy", _POLICIES, ids=["default", "ascii", "compact", "odd"])
def test_the_final_envelope_bytes_equal_the_encoder_for_any_separator(policy):
    result = _decided_result()
    result.diagnostics = {**(result.diagnostics or {}), "note": "日本語😀 \"q\""}
    unlimited = OutputPreparer(BudgetPolicy.unlimited(), encoding=policy).prepare(
        result, result.prepared_semantic_payload.options,
    )
    result.prepared_semantic_payload = unlimited
    envelope = build_final_result_envelope(result)
    assert envelope.total_bytes == len(envelope.text.encode("utf-8"))
    assert envelope.text == policy.dumps(envelope.payload)
    # 上限をちょうどにしても収まり、1 byte 減らすと C が切り詰められる（B は不変）
    exact = envelope.total_bytes
    for limit, truncated in ((exact, False), (exact - 1, True)):
        result.prepared_semantic_payload = dataclasses.replace(
            unlimited,
            plan=dataclasses.replace(unlimited.plan, max_bytes=limit, headroom_bytes=limit - 1),
        )
        bounded = build_final_result_envelope(result)
        assert bounded.total_bytes == len(bounded.text.encode("utf-8")) <= limit
        assert bool(bounded.truncated_metadata) is truncated
        assert bounded.payload["decision_receipt"] == envelope.payload["decision_receipt"]


@pytest.mark.parametrize("policy", _POLICIES, ids=["default", "ascii", "compact", "odd"])
def test_the_object_budget_counts_framing_like_the_encoder(policy):
    from scripts.function_tracer_pcode.core.json_encoding import JsonObjectBudget

    members = {"a": 1, "日本": ["x", {"y": None}], "z": "😀"}
    budget = JsonObjectBudget(policy, None)
    assert budget.total_bytes == len(policy.dumps({}).encode())
    for key, value in members.items():
        budget.add(key, policy.measure(value))
    assert budget.total_bytes == len(policy.dumps(members).encode("utf-8"))


def test_an_authority_value_that_is_not_json_is_an_invariant_violation():
    result = _decided_result()
    result.canonical_c_active_base = ({"row": _Opaque()},)
    with pytest.raises(OutputEnvelopeInvariantViolation):
        build_final_result_envelope(result)


def test_a_malformed_diagnostic_is_a_marker_not_an_error():
    """JSON にならない値を含む診断は marker になる（診断の欠陥で判定を変えない）。"""
    result = _decided_result()
    decided = (result.final_outcome, result.decision_receipt)
    result.pairwise_debug_stats = {"odd": _Opaque()}
    envelope = build_final_result_envelope(result)
    marker = envelope.payload["pairwise_debug_stats"]
    assert marker["truncated"] is True and marker["reason"] == "not_json"
    assert marker["rejected_at"] == "$.odd"
    assert "pairwise_debug_stats" in envelope.truncated_metadata
    assert (result.final_outcome, result.decision_receipt) == decided
    assert json.loads(envelope.text)["final_outcome"] == result.final_outcome


def test_the_counted_effect_projection_equals_the_codec_projection():
    """効果要約の投影を要素ごとに数えて作っても、codec の投影と同じ値・同じ fingerprint。"""
    from scripts.function_tracer_pcode.core.budget_policy import serialization_scope
    from scripts.function_tracer_pcode.proof.obligations.snapshot import (
        AnalysisSnapshot,
        SnapshotFingerprintCodec,
        _semantic_effect_summary_projection,
    )
    from scripts.function_tracer_pcode.tests.unit.test_effect_comparison_surface import (
        _equivalent_void_effect_analyses,
    )

    for analysis in _equivalent_void_effect_analyses():
        effect_summary = analysis.effect_summary
        expected = SnapshotFingerprintCodec.freeze(effect_summary)
        outside = AnalysisSnapshot.from_function_analysis(analysis)
        with pair_failure_scope(("effects",), None), budget_policy_scope(
            expression_budget_policy({})
        ):
            with serialization_scope(site="t", target_parts=("t",)) as work:
                counted = _semantic_effect_summary_projection(effect_summary, work)
                assert work.total_bytes > 0 and work.records_built > 0
            inside = AnalysisSnapshot.from_function_analysis(analysis)
        assert counted == expected
        assert inside.semantic_fingerprint == outside.semantic_fingerprint


def test_a_huge_effect_summary_stops_the_snapshot_before_projecting_every_effect(monkeypatch):
    from scripts.function_tracer_pcode.proof.obligations.snapshot import (
        AnalysisSnapshot,
        SnapshotFingerprintCodec,
    )
    from scripts.function_tracer_pcode.tests.unit.test_effect_comparison_surface import (
        _equivalent_void_effect_analyses,
    )

    analysis = _equivalent_void_effect_analyses()[0]
    effect = analysis.effect_summary.effects[0]
    analysis.effect_summary.effects = [effect] * 50_000
    frozen = []
    original = SnapshotFingerprintCodec.freeze.__func__

    def _counting(cls, value):
        if value is effect:
            frozen.append(value)
        return original(cls, value)

    monkeypatch.setattr(SnapshotFingerprintCodec, "freeze", classmethod(_counting))
    policy = BudgetPolicy(serialization_bytes=200_000, envelope_headroom_bytes=0)
    with pair_failure_scope(("huge-effects",), None), budget_policy_scope(policy):
        with pytest.raises(ExpressionSizeBudgetExceeded) as caught:
            AnalysisSnapshot.from_function_analysis(analysis)
    assert caught.value.site == "proof.obligations.snapshot.from_function_analysis"
    assert 0 < len(frozen) < 1_000  # 予算に届くまでの効果しか投影していない

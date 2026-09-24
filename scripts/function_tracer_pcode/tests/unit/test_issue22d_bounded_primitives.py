# -*- coding: utf-8 -*-
"""Issue #22 PR-22-D（4 回目）: 有界化する処理そのものが有界であること（adversarial）。

各 test は「最終的な値が小さい」だけでなく、**処理時間・peak memory・引き出す数**が入力でなく
上限に比例して止まることを確かめる。入力は本物の producer（`make_unknown_reason` の record・
`EquivalenceResult`・`Expression`）で作る。
"""

from __future__ import annotations

import dataclasses
import time
import tracemalloc
from types import SimpleNamespace

import pytest

from scripts.function_tracer_pcode.checker.output_preparation import (
    BUNDLE_KEY,
    OutputEnvelopeInvariantViolation,
    build_final_result_envelope,
    compose_result_preimage,
    finitize_legacy_reasons,
)
from scripts.function_tracer_pcode.checker.unknown_reason import (
    EVIDENCE_REFS_MAX_COUNT,
    finitize_unknown_reason_record,
    make_unknown_reason,
    recovery_backlog_source,
    unknown_reason_counts_source,
)
from scripts.function_tracer_pcode.core.budget_policy import (
    BudgetPolicy,
    budget_policy_scope,
    serialization_scope,
)
from scripts.function_tracer_pcode.core.errors import AnalysisLimitation, reset_pair_failure_scopes
from scripts.function_tracer_pcode.core.expression import Expression, ExpressionType
from scripts.function_tracer_pcode.core.json_encoding import (
    RESULT_JSON_POLICY,
    BoundedEvidence,
    JsonBudget,
    JsonBudgetExhausted,
    UNFINGERPRINTED_CYCLE,
    UNFINGERPRINTED_WORK_EXHAUSTED,
)
from scripts.function_tracer_pcode.tests.unit.test_issue22d_output_preparation import _decided_result


@pytest.fixture(autouse=True)
def _clean_scopes():
    reset_pair_failure_scopes()
    yield
    reset_pair_failure_scopes()


class _CountedSequence:
    """長さは分かるが、引き出した数を数える列（`tuple(...)` で写せば全部数えられる）。"""

    def __init__(self, length, item):
        self.length = length
        self.item = item
        self.pulled = 0

    def __len__(self):
        return self.length

    def __iter__(self):
        for _ in range(self.length):
            self.pulled += 1
            yield self.item


def _measured(fn):
    tracemalloc.start()
    started = time.perf_counter()
    try:
        value = fn()
    finally:
        _, peak = tracemalloc.get_traced_memory()
        tracemalloc.stop()
    return value, time.perf_counter() - started, peak


_POLICY = BudgetPolicy(serialization_bytes=1 << 26, envelope_headroom_bytes=1 << 25)


# ---------------------------------------------------------------------------
# 集合（reason / action）の件数
# ---------------------------------------------------------------------------


def test_a_million_legacy_reasons_are_bounded_by_count_before_any_is_finitized():
    record = make_unknown_reason("unknown", stage="S", detail="d")
    reasons = [record] * 1_000_000
    result = SimpleNamespace(unknown_reasons=reasons, unknown_recovery_actions=None)
    with budget_policy_scope(_POLICY):
        # pilot のある経路: 先頭の行数の上限だけを有界化し、残りは件数
        _, elapsed, peak = _measured(lambda: finitize_legacy_reasons(result, authority_projects_reasons=True))
    assert len(result.unknown_reasons) < 50_000
    assert result.legacy_reason_overflow == 1_000_000 - len(result.unknown_reasons)
    assert elapsed < 5.0 and peak < 64 * 1024 * 1024
    # pilot の無い経路（legacy reason がそのまま出力の行）: 件数だけで判定の前の限界
    result = SimpleNamespace(unknown_reasons=[record] * 1_000_000, unknown_recovery_actions=None)
    with budget_policy_scope(_POLICY):
        started = time.perf_counter()
        with pytest.raises(AnalysisLimitation):
            finitize_legacy_reasons(result, authority_projects_reasons=False)
        assert time.perf_counter() - started < 0.5


def test_a_million_recovery_actions_are_a_limitation_without_finitizing_them():
    from scripts.function_tracer_pcode.checker.unknown_reason import UnknownRecoveryAction, coerce_unknown_recovery_action

    action = coerce_unknown_recovery_action("x")
    assert isinstance(action, UnknownRecoveryAction)
    result = SimpleNamespace(unknown_reasons=None, unknown_recovery_actions=[action] * 1_000_000)
    with budget_policy_scope(_POLICY):
        started = time.perf_counter()
        with pytest.raises(AnalysisLimitation):
            finitize_legacy_reasons(result, authority_projects_reasons=True)
        assert time.perf_counter() - started < 0.5


# ---------------------------------------------------------------------------
# record の中の列・key・文字列
# ---------------------------------------------------------------------------


def test_a_million_refs_and_requirement_ids_are_pulled_only_up_to_the_prefix():
    refs = _CountedSequence(1_000_000, "ref")
    requirements = _CountedSequence(1_000_000, "req:x")
    record = make_unknown_reason("unknown", stage="S")
    record = dataclasses.replace(record, evidence_refs=refs, proof_requirement_ids=requirements)
    finitized, elapsed, peak = _measured(
        lambda: finitize_unknown_reason_record(record, work=JsonBudget(1 << 20)),
    )
    assert refs.pulled == EVIDENCE_REFS_MAX_COUNT and requirements.pulled == EVIDENCE_REFS_MAX_COUNT
    assert finitized.evidence_refs[-1] == f"…(+{1_000_000 - EVIDENCE_REFS_MAX_COUNT} refs)"
    assert elapsed < 0.5 and peak < 4 * 1024 * 1024


def test_a_very_wide_target_key_is_summarized_within_the_work():
    wide = {f"k{index}": index for index in range(1_000_000)}
    record = make_unknown_reason("unknown", stage="S", object_target_key=wide)
    work = JsonBudget(1 << 16)
    finitized, elapsed, peak = _measured(lambda: finitize_unknown_reason_record(record, work=work))
    key = finitized.object_target_key
    assert type(key) is BoundedEvidence and key.unfingerprinted == UNFINGERPRINTED_WORK_EXHAUSTED
    # 幅を数えた時点で止まる（100 万の組を並べない・写さない）
    assert elapsed < 1.0 and peak < 8 * 1024 * 1024


def test_a_deeply_shared_dag_key_is_not_expanded():
    node = ("leaf",)
    for _ in range(64):
        node = (node, node)
    record = make_unknown_reason("unknown", stage="S", object_target_key=node, object_evidence=node)
    finitized, elapsed, peak = _measured(
        lambda: finitize_unknown_reason_record(record, work=JsonBudget(1 << 20)),
    )
    assert finitized.object_target_key.unfingerprinted == UNFINGERPRINTED_WORK_EXHAUSTED
    # 作業量（1 MiB）の分だけ辿って止まる（2^64 の葉を展開しない）
    assert elapsed < 3.0 and peak < 8 * 1024 * 1024


def test_self_referential_evidence_is_a_typed_cycle_not_an_endless_walk():
    cycle_list = []
    cycle_list.append(cycle_list)
    cycle_list.extend(range(3_000))
    cycle_dict = {"pad": list(range(3_000))}
    cycle_dict["self"] = cycle_dict
    # producer（`make_unknown_reason`）は閉路のある key を作れないので、作った後に差し込む
    record = dataclasses.replace(
        make_unknown_reason("unknown", stage="S"), object_target_key=cycle_list, object_evidence=cycle_dict,
    )
    finitized, elapsed, _ = _measured(
        lambda: finitize_unknown_reason_record(record, work=JsonBudget(1 << 24)),
    )
    assert finitized.object_target_key.unfingerprinted == UNFINGERPRINTED_CYCLE
    assert finitized.object_evidence.unfingerprinted == UNFINGERPRINTED_CYCLE
    assert elapsed < 1.0


def test_a_huge_string_the_producer_already_holds_is_not_hashed_past_the_work():
    huge = "x" * (128 * 1024 * 1024)
    record = make_unknown_reason("unknown", stage="S", detail=huge)
    finitized, elapsed, peak = _measured(
        lambda: finitize_unknown_reason_record(record, work=JsonBudget(1 << 20)),
    )
    # marker は先頭と長さだけ（hash を求める作業量が無い）。128 MB を hash・写しない
    assert "sha256" not in finitized.detail and "chars" in finitized.detail
    assert len(finitized.detail) <= 1024
    assert elapsed < 0.5 and peak < 4 * 1024 * 1024


# ---------------------------------------------------------------------------
# 集計の source（K × N の数え直しをしない）
# ---------------------------------------------------------------------------


def test_reason_counts_and_backlog_are_one_pass_and_bounded_by_the_walk():
    from scripts.function_tracer_pcode.proof.unknown_reason import UnknownReasonId

    reason_ids = [member.value for member in UnknownReasonId]
    records = [
        make_unknown_reason(reason_ids[index % len(reason_ids)], stage=f"S{index}")
        for index in range(100_000)
    ]
    distinct = len({record.reason_id for record in records})
    counts, elapsed, _ = _measured(lambda: RESULT_JSON_POLICY.prepare(unknown_reason_counts_source(records)).value())
    assert len(counts) == distinct and sum(counts.values()) == 100_000
    assert elapsed < 3.0  # K × N ではなく N 回
    backlog, elapsed, _ = _measured(lambda: RESULT_JSON_POLICY.prepare(recovery_backlog_source(records)).value())
    assert len(backlog) == distinct
    assert elapsed < 6.0
    # 作業量を超える集計は、途中の値を出さずに予算の超過
    with pytest.raises(JsonBudgetExhausted):
        RESULT_JSON_POLICY.prepare(unknown_reason_counts_source(records), max_bytes=4_096)


# ---------------------------------------------------------------------------
# 最終 JSON（bundle を含む）の契約
# ---------------------------------------------------------------------------


def test_the_bundle_is_inside_the_contract_and_a_bundle_past_it_is_a_violation():
    result = _decided_result()
    natural = build_final_result_envelope(result, seal=lambda _preimage: {"bundle": "small"})
    assert natural.total_bytes == len(natural.text.encode("utf-8"))
    assert natural.total_bytes <= natural.plan.max_bytes
    prepared = result.prepared_semantic_payload
    room = natural.plan.max_bytes - natural.preimage_bytes
    pulled = []

    def huge_bundle(_preimage):
        def events():
            for index in range(10_000_000):
                pulled.append(index)
                yield {"event": index, "pad": "e" * 64}
        return {"sealed_event_stream": events()}

    result.prepared_semantic_payload = dataclasses.replace(
        prepared,
        plan=dataclasses.replace(prepared.plan, max_bytes=natural.preimage_bytes + 10_000),
    )
    freeable = compose_result_preimage(result).freeable_bytes
    with pytest.raises(OutputEnvelopeInvariantViolation, match="does not fit the rest of the envelope"):
        build_final_result_envelope(result, seal=huge_bundle)
    # 封印は高々 2 回だけ数える（残り / 残り + 切り詰められる byte）。どちらも上限の中で止まり、
    # 1000 万の event を書き出さない
    event_bytes = RESULT_JSON_POLICY.measure({"event": 0, "pad": "e" * 64})
    assert len(pulled) * event_bytes <= 2 * (10_000 + freeable) + 2 * event_bytes
    assert room > 0


def test_a_bundle_crowded_out_by_truncatable_diagnostics_recomposes_instead_of_failing():
    # 切り詰めてよい診断（C）が場所を取っていても、封印は ERROR にならず、診断が先に marker になる
    result = _decided_result()
    natural = build_final_result_envelope(result, seal=lambda _preimage: {"bundle": "small"})
    result.diagnostics = {**(result.diagnostics or {}), "stages": {"huge": "d" * 25_000}}
    limit = natural.total_bytes + 30_000
    prepared = result.prepared_semantic_payload
    result.prepared_semantic_payload = dataclasses.replace(
        prepared, plan=dataclasses.replace(prepared.plan, max_bytes=limit, headroom_bytes=limit - 1),
    )
    seen = []

    def bundle(preimage):
        seen.append(preimage.get("diagnostics", {}).get("truncated"))
        return {"sealed": "b" * 20_000}

    envelope = build_final_result_envelope(result, seal=bundle)
    assert envelope.total_bytes <= limit
    assert envelope.payload[BUNDLE_KEY]["sealed"] == "b" * 20_000
    assert "diagnostics" in envelope.truncated_metadata
    # 封印し直したのは組み直した preimage（切り詰めた後の digest を持つ）
    assert seen[0] is not True and seen[-1] is True
    # 組み直しを外すと、同じ入力は契約違反になる（組み直しが効いていることの確認）
    from scripts.function_tracer_pcode.checker import output_preparation

    with pytest.raises(OutputEnvelopeInvariantViolation):
        output_preparation.finalize_result_envelope(compose_result_preimage(result), seal=bundle)


def test_the_final_encode_is_bounded_by_the_contract_not_by_the_produced_size():
    import inspect

    from scripts.function_tracer_pcode.checker import output_preparation

    source = inspect.getsource(output_preparation.finalize_result_envelope)
    assert "encode_bounded(payload, max_bytes=limit)" in source
    assert "max_bytes=total" not in source


def test_a_violation_error_keeps_the_superseded_decision_receipt(monkeypatch, tmp_path):
    """出力の契約違反は durable な ERROR で、取って代わられた DecisionReceipt をそのまま持つ。"""

    import json

    from scripts.function_tracer_pcode.authority.decision import canonical_result
    from scripts.function_tracer_pcode.authority.decision.production_cutover import decision_receipt_payload
    from scripts.function_tracer_pcode.cli.commands import equivalence

    decided = _decided_result()
    original = decision_receipt_payload(decided.decision_receipt)
    written = []
    monkeypatch.setattr(equivalence, "output_result", lambda content, *_a, **_k: written.append(content))
    monkeypatch.setattr(canonical_result, "persist_canonical_result_envelope", lambda _payload: None)
    args = SimpleNamespace(verbose=False, debug=False, output=None, quiet=True)
    with pytest.raises(SystemExit):
        equivalence._emit_output_invariant_error_result(
            args, result=decided,
            violation=OutputEnvelopeInvariantViolation("too big", max_bytes=1, requested_bytes=2),
            binary1_path=str(tmp_path / "a"), binary2_path=str(tmp_path / "b"),
            func_name1="f", func_name2="f", start_time=0.0,
        )
    block = next(content for content in written if "EQUIVALENCE_RESULT_JSON_BEGIN" in content)
    payload = json.loads(block.split("\n")[1])
    assert payload["final_outcome"] == "ERROR"
    assert payload["superseded_decision_receipt"] == original
    assert "OUTPUT_ENVELOPE_INVARIANT_VIOLATION" in payload["error_message"]
    # ERROR 自身の receipt は別（取って代わられた判定を上書きしない）
    assert payload["decision_receipt"]["receipt_digest"] != original["receipt_digest"]


# ---------------------------------------------------------------------------
# 入れ子の予算・診断の準備物
# ---------------------------------------------------------------------------


def test_a_diagnostic_scope_inside_a_terminal_scope_keeps_its_own_bound():
    with budget_policy_scope(_POLICY):
        with serialization_scope(site="outer", target_parts=("o",), max_bytes=1 << 20) as outer:
            with serialization_scope(site="inner", target_parts=("i",), terminal=False, max_bytes=100) as inner:
                assert inner is not outer
                with pytest.raises(JsonBudgetExhausted):
                    inner.charge(101)
            # 診断の超過は外側（意味の限界）の作業量を使わない
            assert outer.consumed == 0


def test_the_diagnostic_artifacts_share_one_budget():
    result = _decided_result()
    prepared = result.prepared_semantic_payload
    total = (
        prepared.raw_limitation_evidence.encoded_bytes
        + prepared.trace_timings.encoded_bytes
        + prepared.cause_evidence.encoded_bytes
    )
    assert total <= prepared.plan.headroom_bytes


# ---------------------------------------------------------------------------
# 式の木の見積り（兄弟の部分木の合計で止まる）
# ---------------------------------------------------------------------------


def test_the_tree_estimate_stops_on_the_distinct_node_total_across_siblings():
    """兄弟の部分木がそれぞれ上限未満でも、distinct な node の合計で止まる（兄弟を全部数えない）。"""

    from scripts.function_tracer_pcode.core.expression import estimate_legacy_dict_bytes

    def chain(seed, length):
        node = Expression(ExpressionType.CONSTANT, value=seed, size=4)
        for depth in range(length):
            node = Expression.binary_op("+", node, Expression(ExpressionType.CONSTANT, value=depth, size=4))
        return node

    one = estimate_legacy_dict_bytes(chain(0, 600), max_bytes=None)
    limit = int(one / 0.6)
    # 1 つの node の直接の子が 64 本の独立な chain（どれも上限の 6 割）
    root = Expression(ExpressionType.BINARY_OP, operator="+", operands=[chain(seed, 600) for seed in range(64)], size=4)
    estimate, elapsed, _ = _measured(lambda: estimate_legacy_dict_bytes(root, max_bytes=limit))
    assert estimate == limit + 1
    full, full_elapsed, _ = _measured(lambda: estimate_legacy_dict_bytes(root, max_bytes=None))
    assert full > 30 * limit
    # 上限で止まる見積りは 2 本目の途中で止まる（64 本を数える見積りより十分に早い）
    assert elapsed < full_elapsed / 8


# ---------------------------------------------------------------------------
# primitive ごとの作業量（mutation で外すと落ちる形）
# ---------------------------------------------------------------------------


def test_a_scan_charges_every_pulled_element_even_when_the_output_is_tiny():
    from scripts.function_tracer_pcode.core.json_encoding import Tally, scan

    pulled = []

    def elements():
        for index in range(1_000_000):
            pulled.append(index)
            yield index

    # 結果は `{"0": n}` の 1 組だけ: 出力の byte ではなく、引き出す作業量で止まる
    with pytest.raises(JsonBudgetExhausted):
        RESULT_JSON_POLICY.prepare(scan(elements(), Tally(lambda _item: 0)), max_bytes=1_000)
    assert len(pulled) <= 1_001


def test_the_fast_path_stops_on_container_frames_without_leaves():
    empty_lists = [[] for _ in range(1_000_000)]
    started = time.perf_counter()
    with pytest.raises(JsonBudgetExhausted):
        RESULT_JSON_POLICY.measure(empty_lists, max_bytes=100)
    assert time.perf_counter() - started < 0.2


def test_token_fingerprints_charge_a_wide_mapping_before_sorting_it():
    wide = {object(): index for index in range(1_000_000)}  # 非 canonical（key が object）
    work = JsonBudget(10_000)
    started = time.perf_counter()
    with pytest.raises(JsonBudgetExhausted):
        RESULT_JSON_POLICY.token_fingerprint(wide, work=work)
    assert time.perf_counter() - started < 0.5


def test_long_strings_are_not_measured_past_the_caller_bound():
    from scripts.function_tracer_pcode.core.json_encoding import cached_string_bytes

    huge = "\x01" * (64 * 1024 * 1024)
    started = time.perf_counter()
    assert cached_string_bytes(RESULT_JSON_POLICY, huge, max_bytes=100) == 101
    assert time.perf_counter() - started < 0.05


def test_the_trace_totals_are_folded_under_the_walk_budget():
    from scripts.function_tracer_pcode.checker.diagnostics import TraceTimingsView

    rows = SimpleNamespace(results=[SimpleNamespace(elapsed_time=0.001)] * 1_000)
    attempts = [SimpleNamespace(solver_results=rows, attempt_id="a", phase="P", strategy="s", elapsed_time=0.0)] * 5_000
    result = SimpleNamespace(debug_trace=SimpleNamespace(attempts=attempts), solver_results=None)
    started = time.perf_counter()
    with pytest.raises(JsonBudgetExhausted):
        RESULT_JSON_POLICY.prepare(TraceTimingsView(result), max_bytes=10_000)
    assert time.perf_counter() - started < 0.5
    small = SimpleNamespace(debug_trace=SimpleNamespace(attempts=attempts[:2]), solver_results=None)
    value = RESULT_JSON_POLICY.prepare(TraceTimingsView(small)).value()
    assert value["solver_invocations"] == 2_000 and value["solver_seconds"] == pytest.approx(2.0)


def test_the_cause_aggregate_reads_canonical_reasons_under_its_diagnostic_work():
    from scripts.function_tracer_pcode.checker.cause_aggregate import attach_cause_aggregate

    result = _decided_result()
    prepared = result.prepared_semantic_payload
    result.prepared_semantic_payload = dataclasses.replace(
        prepared, plan=dataclasses.replace(prepared.plan, headroom_bytes=4_096),
    )
    result.unknown_reasons = list(result.unknown_reasons) * 200_000
    result.unknown_cause_aggregate = None
    started = time.perf_counter()
    attach_cause_aggregate(result)
    # 作業量（headroom）を超えれば集計は `error` を持つ値（診断の marker）。判定は変えない
    assert "error" in result.unknown_cause_aggregate
    assert time.perf_counter() - started < 2.0


def test_the_diagnostic_artifacts_draw_on_one_shared_budget(monkeypatch):
    from scripts.function_tracer_pcode.checker import output_preparation
    from scripts.function_tracer_pcode.core.json_encoding import JsonEncodingPolicy

    limits = []
    original = JsonEncodingPolicy.prepare

    def recording(self, source, *, max_bytes=None):
        prepared = original(self, source, max_bytes=max_bytes)
        limits.append((max_bytes, prepared.encoded_bytes))
        return prepared

    result = _decided_result()
    monkeypatch.setattr(JsonEncodingPolicy, "prepare", recording)
    policy = BudgetPolicy(serialization_bytes=1 << 26, envelope_headroom_bytes=1 << 25)
    preparer = output_preparation.OutputPreparer(policy)
    diagnostic = JsonBudget(policy.envelope_headroom_bytes)
    preparer._prepare_limitation_evidence(result, diagnostic=diagnostic)
    preparer._prepare_trace_timings(result, diagnostic=diagnostic)
    first, second = limits[-2], limits[-1]
    # 2 つ目は 1 つ目が使った分だけ少ない上限で準備する（それぞれが全体の上限を持たない）
    assert second[0] == first[0] - first[1]



def test_the_internal_legacy_evidence_draws_on_the_shared_budget_last(monkeypatch):
    # 出力される C の本体（trace の時間・原因集計）を先に、出力されない legacy の証拠を最後に
    from scripts.function_tracer_pcode.checker import output_preparation

    calls = []
    for name in ("_prepare_limitation_evidence", "_prepare_trace_timings", "_prepare_cause_evidence"):
        original = getattr(output_preparation.OutputPreparer, name)

        def wrapped(self, *args, _name=name, _original=original, **kwargs):
            calls.append((_name, kwargs["diagnostic"].remaining()))
            return _original(self, *args, **kwargs)

        monkeypatch.setattr(output_preparation.OutputPreparer, name, wrapped)
    _decided_result()
    names = [name for name, _ in calls[-3:]]
    assert names == ["_prepare_trace_timings", "_prepare_cause_evidence", "_prepare_limitation_evidence"]

# ---------------------------------------------------------------------------
# yield しない仕事（`metered`）・producer の失敗・LEGACY の列
# ---------------------------------------------------------------------------


def _counted(values, pulled):
    for value in values:
        pulled.append(1)
        yield value


def test_recovery_actions_charge_the_records_they_skip():
    from scripts.function_tracer_pcode.checker.unknown_reason import recovery_actions_source

    # 同じ集計単位の record は最初の 1 件だけが action になる: 残りは yield されずに読み飛ばされる
    record = make_unknown_reason("unknown", stage="S")
    pulled = []
    started = time.perf_counter()
    with pytest.raises(JsonBudgetExhausted):
        RESULT_JSON_POLICY.prepare(
            recovery_actions_source(_counted([record] * 1_000_000, pulled), primary_by_aggregation_unit=True),
            max_bytes=10_000,
        )
    assert len(pulled) <= 10_001
    assert time.perf_counter() - started < 1.0


def test_recovery_actions_charge_the_key_they_copy_into_the_obligation_id():
    from scripts.function_tracer_pcode.checker.unknown_reason import (
        build_unknown_recovery_actions,
        recovery_actions_source,
    )

    pulled = []

    class _CountingList(list):
        def __iter__(self):
            for item in list.__iter__(self):
                pulled.append(1)
                yield item

    inner = _CountingList(range(1_000))
    wide = [inner] * 1_000  # 写すと 100 万要素
    record = dataclasses.replace(
        make_unknown_reason("return_width_bridge_missing", stage="S"), object_target_key=wide, evidence_kind="k",
    )
    # 登録済みの obligation を持つ reason: key を写して proof obligation id を作る経路
    assert any(action.proof_obligation_id is not None for action in build_unknown_recovery_actions([record]))
    pulled.clear()
    with pytest.raises(JsonBudgetExhausted):
        RESULT_JSON_POLICY.prepare(recovery_actions_source([record]), max_bytes=10_000)
    # 写す前に要素の数を数えて止まる（入れ子の列を 1 つも写さない）
    assert len(pulled) < 10_000


def test_the_final_attempt_search_and_observed_reasons_are_charged_per_attempt():
    from scripts.function_tracer_pcode.checker.debug_trace import DebugTrace
    from scripts.function_tracer_pcode.checker.unknown_reason import unknown_reason_counts_source
    from scripts.function_tracer_pcode.core.json_encoding import metered

    # reason の無い attempt を 100 万: 引き出す要素が無くても、探した attempt を数える
    attempts = [SimpleNamespace(result=True, transition_reason="UNSAT", unknown_reasons=())] * 1_000_000
    trace = DebugTrace(attempts=attempts)
    for source in (
        metered(lambda work: unknown_reason_counts_source(trace._final_unknown_reasons(work))),
        metered(lambda work: unknown_reason_counts_source(trace._iter_observed_unknown_reasons(work))),
    ):
        started = time.perf_counter()
        with pytest.raises(JsonBudgetExhausted):
            RESULT_JSON_POLICY.prepare(source, max_bytes=10_000)
        assert time.perf_counter() - started < 0.5


def _reference_phase_usage(trace):
    # 旧実装（phase ごとに attempt を全部辿る）と同じ値
    phases = []
    for phase in list(trace.known_phases) + [attempt.phase for attempt in trace.attempts]:
        if phase not in phases:
            phases.append(phase)
    rows = []
    for phase in phases:
        mine = [attempt for attempt in trace.attempts if attempt.phase == phase]
        counts = {key: 0 for key in ("UNSAT", "SAT", "SAT->Phase4B", "UNKNOWN", "TIMEOUT", "critical_error", "no_changes")}
        for attempt in mine:
            counts[attempt.transition_reason] = counts.get(attempt.transition_reason, 0) + 1
        results = [attempt for attempt in mine if attempt.transition_reason != "no_changes"]
        rows.append({
            "phase": phase, "planned": phase in trace.planned_phases, "reached": bool(mine),
            "used": bool(results), "attempt_count": len(mine), "result_attempt_count": len(results),
            "no_change_skip_count": len(mine) - len(results), "transition_counts": counts,
            "last_transition_reason": mine[-1].transition_reason if mine else None,
            "last_result": mine[-1].result if mine else None,
        })
    return rows


def test_phase_usage_is_one_pass_and_equals_the_per_phase_count():
    from scripts.function_tracer_pcode.checker.debug_trace import DebugTrace

    reasons = ["UNSAT", "UNKNOWN", "no_changes", "TIMEOUT"]
    attempts = [
        SimpleNamespace(phase=f"P{index % 40}", transition_reason=reasons[index % 4], result=None)
        for index in range(200)
    ]
    trace = DebugTrace(attempts=attempts, planned_phases=["P1", "PX"], known_phases=["PX", "P3"])
    expected = _reference_phase_usage(trace)
    assert trace.get_phase_usage() == expected
    assert trace.get_used_phases() == [row["phase"] for row in expected if row["used"]]
    prepared = RESULT_JSON_POLICY.prepare(trace.phase_usage_source()).value()
    assert prepared == RESULT_JSON_POLICY.prepare(expected).value()
    # phase の数 × attempt の数ではなく attempt の数に比例する
    many = DebugTrace(attempts=[
        SimpleNamespace(phase=f"P{index % 5_000}", transition_reason="UNSAT", result=None)
        for index in range(100_000)
    ])
    _, elapsed, _ = _measured(many.get_phase_usage)
    assert elapsed < 1.0
    with pytest.raises(JsonBudgetExhausted):
        RESULT_JSON_POLICY.prepare(many.phase_usage_source(), max_bytes=10_000)


def test_a_producer_failure_is_a_rejected_value_not_an_escaped_exception():
    from scripts.function_tracer_pcode.core.json_encoding import JsonValueRejected, Tally, scan

    class _Broken:
        def json_items(self):
            yield "ok", 1
            raise TypeError("broken producer")

    with pytest.raises(JsonValueRejected, match="producer failed"):
        RESULT_JSON_POLICY.prepare(_Broken())

    def explode(_item):
        raise ValueError("broken key")

    with pytest.raises(JsonValueRejected, match="producer failed"):
        RESULT_JSON_POLICY.prepare(scan([1, 2], Tally(explode)))


def test_unsized_solver_rows_are_a_rejected_value_not_an_uncounted_copy():
    from scripts.function_tracer_pcode.checker.diagnostics import TraceTimingsView
    from scripts.function_tracer_pcode.core.json_encoding import JsonValueRejected

    rows = SimpleNamespace(results=iter([SimpleNamespace(elapsed_time=1.0)] * 1_000_000))
    attempts = [SimpleNamespace(solver_results=rows, attempt_id="a", phase="P", strategy="s", elapsed_time=0.0)]
    result = SimpleNamespace(debug_trace=SimpleNamespace(attempts=attempts), solver_results=None)
    with pytest.raises(JsonValueRejected, match="producer failed"):
        RESULT_JSON_POLICY.prepare(TraceTimingsView(result), max_bytes=10_000)


def test_finitized_requirement_ids_keep_their_legacy_dict_form():
    ids = [{"requirement": "r", "index": 0}, {"requirement": "r" * 5_000, "index": 1}]
    ids += [{"requirement": "q", "index": index} for index in range(EVIDENCE_REFS_MAX_COUNT + 1)]
    record = dataclasses.replace(make_unknown_reason("unknown", stage="S"), proof_requirement_ids=ids)
    finitized = finitize_unknown_reason_record(record, work=JsonBudget(1 << 22))
    legacy = finitized.to_dict()["proof_requirement_ids"]
    # mapping だけを dict にし、大きい要素（有界な証拠）と件数の marker はそのまま置く
    assert legacy[0] == {"requirement": "r", "index": 0}
    assert type(legacy[1]) is BoundedEvidence
    assert legacy[-1] == "…(+3 refs)"


def test_the_diagnostics_view_does_not_prepare_trace_rows_under_another_budget():
    from scripts.function_tracer_pcode.checker.diagnostics import result_diagnostics_payload

    pulled = []

    class _Attempts:
        def __len__(self):
            return 1_000_000

        def __iter__(self):
            for _ in range(1_000_000):
                pulled.append(1)
                yield SimpleNamespace(solver_results=None, attempt_id="a", phase="P", strategy="s", elapsed_time=0.0)

    result = SimpleNamespace(
        debug_trace=SimpleNamespace(attempts=_Attempts()), solver_results=None, diagnostics={},
        prepared_semantic_payload=None, total_time=0.0, pairwise_stats=None, stage_path=(),
    )
    view = result_diagnostics_payload(result, lazy=True)
    # 作っただけでは trace を辿らない（別の予算で先に準備しない）
    assert pulled == []
    with pytest.raises(JsonBudgetExhausted):
        RESULT_JSON_POLICY.prepare(view, max_bytes=10_000)
    # 1 要素 1 以上を数えるので、引き出すのは予算の byte 数まで
    assert len(pulled) <= 10_001


# ---------------------------------------------------------------------------
# projection の診断: legacy の索引・1:1 の照合・requirement id の文字列
# ---------------------------------------------------------------------------


def _cause(key, requirements=()):
    from scripts.function_tracer_pcode.authority.contracts import canonical_value

    return SimpleNamespace(
        cause_id=SimpleNamespace(canonical_target_key=canonical_value(key)),
        proof_requirement_ids=requirements,
    )


def test_a_unique_match_is_not_claimed_when_legacy_reasons_were_dropped():
    from scripts.function_tracer_pcode.checker.unknown_reason import (
        MATCH_UNIQUE,
        _match_legacy_reasons,
        legacy_reason_index,
    )

    legacy = (make_unknown_reason("unknown", stage="S"),)
    work = JsonBudget(1 << 20)
    whole = legacy_reason_index(legacy, work=work)
    assert _match_legacy_reasons("unknown", _cause(("x",)), whole, {"unknown": 1}, work=work)[1] == MATCH_UNIQUE
    # 件数の上限で残さなかった reason があれば、残した 1 件が 1:1 とは言えない
    cut = legacy_reason_index(legacy, work=work, overflow=5)
    assert _match_legacy_reasons("unknown", _cause(("x",)), cut, {"unknown": 1}, work=work) == ((), None)


def test_the_legacy_index_is_built_once_not_rescanned_per_cause():
    from scripts.function_tracer_pcode.checker.unknown_reason import _match_legacy_reasons, legacy_reason_index

    records = [make_unknown_reason("unknown", stage=f"S{index}") for index in range(10_000)]
    pulled = []
    work = JsonBudget(1 << 24)
    index = legacy_reason_index(_counted(records, pulled), work=work)
    started = time.perf_counter()
    for number in range(1_000):
        _match_legacy_reasons("unknown", _cause(("k", number)), index, {"unknown": 1_000}, work=work)
    assert len(pulled) == 10_000
    assert time.perf_counter() - started < 2.0
    # 索引を作る作業量を使い切っても例外にしない（authority の finish を止めない）
    assert legacy_reason_index(records, work=JsonBudget(10)).truncated


def test_requirement_ids_are_measured_before_they_are_written_as_text():
    from scripts.function_tracer_pcode.checker.unknown_reason import _match_legacy_reasons

    written = []

    class _Requirement(tuple):
        def __str__(self):
            written.append(1)
            return tuple.__str__(self)

    huge = _Requirement(range(200_000))
    # 照合は `str(requirement) == str(canonical_value(obligation))`（obligation の canonical な形は tuple）
    small = _Requirement((("requirement", "r"),))
    record = dataclasses.replace(
        make_unknown_reason("unknown", stage="S"), proof_obligation_id={"requirement": "r"},
    )
    matched, _ = _match_legacy_reasons(
        "unknown", _cause(("k",), (small, huge)), (record,), {"unknown": 2}, work=JsonBudget(50_000),
    )
    assert matched == (record,)
    # 大きい requirement は数えきれないので文字列にしない（小さい方だけ）
    assert len(written) == 1

# -*- coding: utf-8 -*-
"""Issue #22 PR-22-D（4 回目）: 有界化する処理そのものが有界であること（adversarial）。

各 test は「最終的な値が小さい」だけでなく、**処理時間・peak memory・引き出す数**が入力でなく
上限に比例して止まることを確かめる。入力は本物の producer（`make_unknown_reason` の record・
`EquivalenceResult`・`Expression`）で作る。
"""

from __future__ import annotations

import dataclasses
import enum
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
    # 全体の hash を求める作業量が無い: marker は先頭・長さと、先頭・末尾の窓の digest だけ
    # （128 MB を hash・写しない。marker を集計の key にしても digest が無い marker にならない）
    assert "sha256w:" in finitized.detail and " sha256:" not in finitized.detail
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
    assert payload["superseded_decision_receipt"] == {"decision_receipt": original}
    # 確定した判定は message の先頭（上限で切れるのは後ろの違反の文だけ）
    assert payload["error_message"].startswith("OUTPUT_ENVELOPE_INVARIANT_VIOLATION: decided_outcome=")
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
    pulled = []

    class _Counted(list):
        def __iter__(self):
            for item in list.__iter__(self):
                pulled.append(1)
                yield item

    result.unknown_reasons = _Counted(list(result.unknown_reasons) * 200_000)
    result.unknown_cause_aggregate = None
    started = time.perf_counter()
    attach_cause_aggregate(result)
    # 作業量（headroom）を超えれば集計は `error` を持つ値（診断の marker）。判定は変えない
    assert "error" in result.unknown_cause_aggregate
    assert time.perf_counter() - started < 2.0
    # canonical reason は数えながら引き出す（作業量を超えた後の reason を写さない）
    assert len(pulled) < 1_000


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
    names = [name for name, _ in calls]
    order = ["_prepare_trace_timings", "_prepare_cause_evidence", "_prepare_limitation_evidence"]
    # 準備 1 回ごとに 3 つを 1 回ずつ、この順で
    assert names and len(names) % 3 == 0
    assert all(names[index:index + 3] == order for index in range(0, len(names), 3))

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


def test_the_decided_text_is_written_only_after_the_envelope_fits():
    # 契約違反の ERROR の前に、確定した判定の text を書かない。JSON を出すときの text は最終
    # envelope の値から作る（JSON と同じ有界な値）
    import inspect

    from scripts.function_tracer_pcode.cli.commands import equivalence

    source = inspect.getsource(equivalence.run_equivalence_check)
    branch = source[source.index("    if emit_json:\n"):]
    envelope = branch.index("envelope = _final_envelope_or_error_result(")
    text = branch.index("payload=envelope.payload")
    write = branch.index("output_result(output_content, args.output, args.quiet)")
    assert envelope < text < write
    # JSON を出さないときは envelope を作らず、to_dict() から作った text を書く
    assert "if not emit_json:\n        output_content = _text_or_error_result(" in source

def test_payload_occurrence_views_draw_on_one_work_not_one_each():
    from scripts.function_tracer_pcode.checker.cause_aggregate import _payload_occurrence_views

    records = [make_unknown_reason("unknown", stage="S", detail="d" * 400) for _ in range(100)]
    one = RESULT_JSON_POLICY.prepare(records[0]).encoded_bytes
    # 1 件は収まるが 100 件は収まらない作業量: record ごとに作業量の全体を使い直さない
    with budget_policy_scope(_POLICY):
        with serialization_scope(site="test", target_parts=("t",), terminal=False, max_bytes=one * 10):
            with pytest.raises(JsonBudgetExhausted):
                _payload_occurrence_views(records)


def test_cyclic_nodes_walks_each_edge_once():
    import random as _random

    from scripts.function_tracer_pcode.checker.cause_aggregate import cyclic_nodes

    def reference(edges):
        cyclic = set()
        for start in edges:
            path, positions, current = [], {}, start
            while current in edges:
                if current in positions:
                    cyclic.update(path[positions[current]:])
                    break
                positions[current] = len(path)
                path.append(current)
                current = edges[current]
        return cyclic

    rng = _random.Random(7)
    for _ in range(300):
        size = rng.randint(0, 12)
        edges = {node: rng.randint(0, size + 2) for node in range(size) if rng.random() < 0.9}
        assert cyclic_nodes(edges) == reference(edges)
    # 長い鎖（閉路は末尾の 2 node だけ）: 始点ごとに辿り直すと 2 乗
    chain = {index: index + 1 for index in range(200_000)}
    chain[200_000] = 199_999
    started = time.perf_counter()
    assert cyclic_nodes(chain) == {199_999, 200_000}
    assert time.perf_counter() - started < 1.0


def test_the_fast_path_rewalk_above_a_deep_live_leaf_is_charged():
    class _Leaf:
        def json_items(self):
            yield "leaf", 1

    deep = [_Leaf()]
    for _ in range(4_000):
        deep = [deep]
    # 各段の高速経路が底まで辿り直す（深さの 2 乗）: その分を作業量へ数えて止まる
    started = time.perf_counter()
    with pytest.raises(JsonBudgetExhausted):
        RESULT_JSON_POLICY.prepare(deep, max_bytes=100_000)
    assert time.perf_counter() - started < 1.0
    # 浅ければ（辿り直しが作業量に収まれば）そのまま書ける
    shallow = [[[_Leaf()]]]
    assert RESULT_JSON_POLICY.prepare(shallow, max_bytes=100_000).value() == [[[{"leaf": 1}]]]


def test_the_truncation_marker_fits_its_schema_bound_for_any_rejected_path():
    from scripts.function_tracer_pcode.checker import output_schema
    from scripts.function_tracer_pcode.checker.output_preparation import _truncation_marker
    from scripts.function_tracer_pcode.core.json_encoding import JsonValueRejected

    rejected = JsonValueRejected("x", path="$" + ".é " * 5_000)
    marker = _truncation_marker("diagnostics", list(range(10)), remaining_bytes=10 ** 18, rejected=rejected)
    assert len(marker["rejected_at"]) == output_schema.MARKER_PATH_MAX_CHARS
    assert RESULT_JSON_POLICY.measure(marker) <= output_schema._truncation_marker_max_bytes(
        RESULT_JSON_POLICY, "diagnostics",
    )


def test_diagnostic_legacy_reasons_keep_the_schema_row_count():
    from scripts.function_tracer_pcode.checker.output_schema import MAX_UNKNOWN_REASON_ROWS

    result = SimpleNamespace(
        unknown_reasons=[make_unknown_reason("unknown", stage=f"S{index}") for index in range(1_000)],
        unknown_recovery_actions=[], legacy_reason_overflow=0,
    )
    with budget_policy_scope(_POLICY):
        finitize_legacy_reasons(result, authority_projects_reasons=True)
    assert len(result.unknown_reasons) == MAX_UNKNOWN_REASON_ROWS
    assert result.legacy_reason_overflow == 1_000 - MAX_UNKNOWN_REASON_ROWS


def test_a_wide_scope_key_in_a_truncation_record_is_charged_before_it_is_sorted():
    from scripts.function_tracer_pcode.core.runtime_refs.unknowns import ExpansionBudgetTruncation

    from collections.abc import Mapping as _Mapping

    pulled = []

    class _Wide(_Mapping):
        def __len__(self):
            return 1_000_000

        def __iter__(self):
            for index in range(1_000_000):
                pulled.append(1)
                yield f"k{index}"

        def __getitem__(self, key):
            return 0

    record = ExpansionBudgetTruncation(kind="k")
    object.__setattr__(record, "owner_scope_key", (_Wide(),))
    object.__setattr__(record, "_event_id_cache", "e" * 64)
    with pytest.raises(JsonBudgetExhausted):
        RESULT_JSON_POLICY.prepare(record, max_bytes=10_000)
    # 幅を数えた時点で止まる（100 万の key を並べるために引き出さない）
    assert len(pulled) < 20_000


# ---------------------------------------------------------------------------
# 最終 envelope: surrogate・key の衝突・C の場所の予約
# ---------------------------------------------------------------------------


def test_a_lone_surrogate_is_written_as_counted_in_the_final_envelope():
    import json

    result = _decided_result()
    result.pairwise_stats = {"note": "file\udcff\ud800name"}
    envelope = build_final_result_envelope(result)
    encoded = envelope.text.encode("utf-8")  # strict: 書ける
    assert envelope.total_bytes == len(encoded)
    assert json.loads(envelope.text)["pairwise_stats"]["note"] == "file\udcff\ud800name"


def test_colliding_keys_are_rejected_on_the_fast_path_too():
    from scripts.function_tracer_pcode.core.json_encoding import JsonValueRejected

    for value in ({1: "a", "1": "b"}, {True: 1, "true": 2}, {None: 1, "null": 2}):
        with pytest.raises(JsonValueRejected, match="collides"):
            RESULT_JSON_POLICY.prepare(value)
    # 診断の中なら marker（判定を変えない）
    result = _decided_result()
    decided = (result.final_outcome, result.decision_receipt)
    result.pairwise_stats = {1: "a", "1": "b"}
    envelope = build_final_result_envelope(result)
    assert envelope.payload["pairwise_stats"]["truncated"] is True
    assert (result.final_outcome, result.decision_receipt) == decided


def test_an_earlier_diagnostic_body_never_erases_a_later_field():
    result = _decided_result()
    natural = build_final_result_envelope(result)
    present = [key for key in ("pairwise_stats", "stage_path", "diagnostics", "unknown_cause_aggregate")
               if key in natural.payload]
    assert "unknown_cause_aggregate" in present and "diagnostics" in present
    # 先に準備する診断（pairwise_stats）を、後の field の場所まで使えばちょうど入る大きさにする
    later = sum(RESULT_JSON_POLICY.measure(natural.payload[key]) for key in ("diagnostics", "unknown_cause_aggregate"))
    limit = natural.total_bytes + 150_000
    result.pairwise_stats = {"pad": "p" * (150_000 + later - 200)}
    prepared = result.prepared_semantic_payload
    result.prepared_semantic_payload = dataclasses.replace(
        prepared, plan=dataclasses.replace(prepared.plan, max_bytes=limit, headroom_bytes=limit - 1),
    )
    envelope = build_final_result_envelope(result)
    assert envelope.total_bytes <= limit
    # どの field も本体か marker で出る（黙って消えない）。小さい後の field は本体のまま
    for key in present:
        assert key in envelope.payload, key
    assert envelope.payload["pairwise_stats"]["truncated"] is True
    assert envelope.payload["unknown_cause_aggregate"] == natural.payload["unknown_cause_aggregate"]


def test_untruncatable_metadata_is_capped_at_its_schema_bound():
    result = _decided_result()
    result.binary1_content_identity = ("sha256", "d" * 5_000)
    with pytest.raises(OutputEnvelopeInvariantViolation, match="schema bound"):
        build_final_result_envelope(result)


def test_any_failure_building_the_envelope_after_authority_is_a_durable_error(monkeypatch, tmp_path):
    import json

    from scripts.function_tracer_pcode.authority.decision import canonical_result
    from scripts.function_tracer_pcode.cli.commands import equivalence

    decided = _decided_result()
    written, ended = [], []
    monkeypatch.setattr(equivalence, "output_result", lambda content, *_a, **_k: written.append(content))
    monkeypatch.setattr(canonical_result, "persist_canonical_result_envelope", lambda _payload: None)
    monkeypatch.setattr(equivalence, "journal_stage_end", lambda stage, *_a, **_k: ended.append((stage, _a)))
    args = SimpleNamespace(verbose=False, debug=False, output=None, quiet=True)

    def broken_seal(_preimage):
        raise ValueError("seal could not encode the preimage")

    with pytest.raises(SystemExit):
        equivalence._final_envelope_or_error_result(
            args, result=decided, seal=broken_seal,
            binary1_path=str(tmp_path / "a"), binary2_path=str(tmp_path / "b"),
            func_name1="f", func_name2="f", start_time=0.0, emission_started=0.0,
        )
    block = next(content for content in written if "EQUIVALENCE_RESULT_JSON_BEGIN" in content)
    payload = json.loads(block.split("\n")[1])
    assert payload["final_outcome"] == "ERROR"
    assert "ValueError: seal could not encode the preimage" in payload["error_message"]
    assert payload["superseded_decision_receipt"]["decision_receipt"]["outcome"] == decided.final_outcome
    # 確定した判定の emission の区間は ERROR の区間を開く前に閉じる
    assert ended and ended[0][0] == "result_emit" and ended[0][1][1]["superseded_by"] == "output_final_envelope"


def test_the_persisted_envelope_is_no_larger_than_the_result_json_plus_its_wrapper(monkeypatch, tmp_path):
    import json

    from scripts.function_tracer_pcode.authority.decision import canonical_result

    result = _decided_result()
    result.pairwise_stats = {"note": "日本語😀" * 2_000}
    evidence, session = result._canonical_finalization_context
    envelope = build_final_result_envelope(
        result,
        seal=lambda preimage: canonical_result.build_canonical_result_finalization_bundle(
            result_payload_preimage=preimage, evidence=evidence, session=session,
        ),
    )
    monkeypatch.setenv("UNKNOWN_TAXONOMY_V2_SUPERVISOR_ROOT", str(tmp_path))
    monkeypatch.setenv("UNKNOWN_TAXONOMY_V2_EXECUTION_NONCE", "n")
    path = canonical_result.persist_canonical_result_envelope(envelope.payload)
    persisted = path.read_bytes()
    # 文字列は同じ書き方（非 ASCII を 6 / 12 byte の escape に膨らませない）、区切りは詰める
    wrapper = len(json.dumps({
        "schema": "canonical-result-envelope-v1", "canonical_result_payload": None,
        "canonical_result_bundle_digest": "0" * 64, "envelope_digest": "0" * 64,
    }, separators=(",", ":")))
    assert len(persisted) <= envelope.total_bytes + wrapper + 1
    assert json.loads(persisted)["canonical_result_payload"] == json.loads(envelope.text)


# ---------------------------------------------------------------------------
# producer の失敗・1 回しか辿れない列・小さい live な証拠
# ---------------------------------------------------------------------------


@dataclasses.dataclass
class _NeedsFields:
    required: int


class _ExplodingMapping(dict):
    def items(self):
        raise RuntimeError("items() failed")


def test_evidence_that_fails_while_being_fingerprinted_is_an_unsupported_summary():
    from scripts.function_tracer_pcode.core.json_encoding import bounded_evidence

    work = JsonBudget(1 << 20)
    # dataclass の class object（field を getattr できない）・items() が落ちる mapping
    for value in (("x" * 3_000, _NeedsFields), ("x" * 3_000, _ExplodingMapping(a=1))):
        summary = bounded_evidence(value, work=work)
        assert type(summary) is BoundedEvidence
    # finitize（authority 前）も落ちない: 診断にしか使わない証拠で pair を止めない
    record = dataclasses.replace(
        make_unknown_reason("unknown", stage="S"), object_evidence=("x" * 3_000, _NeedsFields),
    )
    finitized = finitize_unknown_reason_record(record, work=work)
    assert type(finitized.object_evidence) is BoundedEvidence


def test_producer_failures_outside_json_items_are_rejected_values_too():
    from scripts.function_tracer_pcode.core.json_encoding import JsonValueRejected, each, scan

    def explode(_item):
        raise KeyError("fn failed")

    with pytest.raises(JsonValueRejected, match="producer failed"):
        RESULT_JSON_POLICY.prepare(each([1], explode))

    class _Reducer:
        def cost(self, _element):
            return 0

        def add(self, _element):
            pass

        def result(self):
            raise AttributeError("result failed")

    with pytest.raises(JsonValueRejected, match="producer failed"):
        RESULT_JSON_POLICY.prepare(scan([1], _Reducer()))


def test_a_diagnostic_whose_reader_fails_is_a_marker():
    from scripts.function_tracer_pcode.checker import output_preparation

    result = _decided_result()
    decided = (result.final_outcome, result.decision_receipt)

    class _Broken:
        @property
        def pairwise_stats(self):
            raise ValueError("no stats")

        def __getattr__(self, name):
            return getattr(result, name)

    envelope = output_preparation.build_final_result_envelope(_Broken())
    assert envelope.payload["pairwise_stats"]["truncated"] is True
    assert (result.final_outcome, result.decision_receipt) == decided


def _counting(prefix):
    for index in range(5_000):
        yield f"{prefix}{index}"


def test_a_one_shot_iterator_inside_evidence_is_not_fingerprinted_after_it_was_consumed():
    from scripts.function_tracer_pcode.core.json_encoding import evidence, text

    for make in (lambda gen: text(("k", gen), 256), lambda gen: evidence(("k", gen))):
        left = RESULT_JSON_POLICY.prepare(make(_counting("AAAA"))).value()
        right = RESULT_JSON_POLICY.prepare(make(_counting("BBBB"))).value()
        # 同じ fingerprint を別の値に付けない（辿った後の列は同じ値として辿り直せない）
        assert left["fingerprint"] is None and right["fingerprint"] is None
        assert left["unfingerprinted"] == "unsupported"


class _Plain(enum.Enum):
    A = object()


def test_small_live_evidence_is_summarized_like_large_live_evidence():
    from scripts.function_tracer_pcode.core.json_encoding import evidence

    small = RESULT_JSON_POLICY.prepare(evidence((_Plain.A,))).value()
    large = RESULT_JSON_POLICY.prepare(evidence(("x" * 5_000, object()))).value()
    assert small["bounded_evidence"] == "v2" and large["bounded_evidence"] == "v2"


def test_scope_key_bytes_and_non_str_keys_are_charged_before_they_are_built():
    from scripts.function_tracer_pcode.core.runtime_refs.unknowns import ExpansionBudgetTruncation

    for scope in ((b"\x00" * 20_000_000,), ({tuple(range(2_000_000)): 1},)):
        record = ExpansionBudgetTruncation(kind="k")
        object.__setattr__(record, "owner_scope_key", scope)
        object.__setattr__(record, "_event_id_cache", "e" * 64)
        started = time.perf_counter()
        # 他の field（event_id など）は収まり、scope key の途中で止まる上限
        _, _, peak = _measured(lambda: pytest.raises(JsonBudgetExhausted, RESULT_JSON_POLICY.prepare, record, max_bytes=2_000))
        assert time.perf_counter() - started < 0.5
        assert peak < 8 * 1024 * 1024


def _reference_match(reason_id, cause, legacy, counts):
    """旧来の照合（cause ごとに legacy を全部比べる）。索引の照合と同じ結果になること。"""

    from scripts.function_tracer_pcode.authority.contracts import authority_digest, canonical_value

    candidates = tuple(record for record in legacy if record.reason_id == reason_id)
    if not candidates:
        return (), None
    target = cause.cause_id.canonical_target_key
    texts = {str(item) for item in cause.proof_requirement_ids}
    exact, by_fingerprint = [], []
    for record in candidates:
        key = record.object_target_key
        if key is not None and target is not None:
            if type(key) is BoundedEvidence:
                if key.fingerprint_kind == "canonical_sha256" and key.fingerprint == authority_digest(target):
                    by_fingerprint.append(record)
                    continue
            elif canonical_value(key) == target:
                exact.append(record)
                continue
        obligation = record.proof_obligation_id
        if obligation is not None and texts and type(obligation) is not BoundedEvidence:
            if str(canonical_value(obligation)) in texts:
                exact.append(record)
                continue
    if exact or by_fingerprint:
        return tuple(exact) + tuple(by_fingerprint), ("exact" if exact else "fingerprint")
    if len(candidates) == 1 and counts.get(reason_id, 0) == 1:
        return candidates, "unique"
    return (), None


def test_indexed_legacy_matching_equals_the_per_candidate_comparison():
    import random as _random

    from scripts.function_tracer_pcode.authority.contracts import canonical_value
    from scripts.function_tracer_pcode.checker.unknown_reason import (
        MATCH_EXACT,
        MATCH_FINGERPRINT,
        MATCH_UNIQUE,
        _match_legacy_reasons,
        legacy_reason_index,
    )

    names = {MATCH_EXACT: "exact", MATCH_FINGERPRINT: "fingerprint", MATCH_UNIQUE: "unique", None: None}
    rng = _random.Random(9)
    keys = [("k", 1), ("k", 2), ("big",) + tuple(range(3_000)), None]
    obligations = [None, ("o", 1), ("o", 2)]
    for _ in range(200):
        legacy = []
        for index in range(rng.randint(0, 6)):
            record = dataclasses.replace(
                make_unknown_reason(rng.choice(["unknown", "unknown", "other"]), stage=f"S{index}"),
                object_target_key=rng.choice(keys), proof_obligation_id=rng.choice(obligations),
            )
            legacy.append(finitize_unknown_reason_record(record, work=JsonBudget(1 << 22)))
        target = rng.choice(keys)
        requirements = tuple(str(canonical_value(item)) for item in rng.sample(obligations[1:], rng.randint(0, 2)))
        cause = _cause(target, requirements) if target is not None else SimpleNamespace(
            cause_id=SimpleNamespace(canonical_target_key=None), proof_requirement_ids=requirements,
        )
        counts = {"unknown": rng.randint(1, 2)}
        work = JsonBudget(1 << 22)
        index = legacy_reason_index(legacy, work=work)
        matched, kind = _match_legacy_reasons("unknown", cause, index, counts, work=work)
        assert (matched, names[kind]) == _reference_match("unknown", cause, legacy, counts)


def test_legacy_matching_does_not_compare_every_cause_with_every_record():
    from scripts.function_tracer_pcode.checker.unknown_reason import _match_legacy_reasons, legacy_reason_index

    legacy = [
        dataclasses.replace(make_unknown_reason("unknown", stage=f"S{index}"),
                            object_target_key=("t", index, "x" * 1_500))
        for index in range(256)
    ]
    work = JsonBudget(1 << 26)
    index = legacy_reason_index(legacy, work=work)
    started = time.perf_counter()
    for number in range(2_000):
        _match_legacy_reasons("unknown", _cause(("t", number % 300, "x" * 1_500)), index, {"unknown": 2_000}, work=work)
    # 2,000 cause × 256 record の比較（約 51 万回の canonical 化）をしない
    assert time.perf_counter() - started < 2.0


def test_recompose_with_the_real_seal_in_a_regime_the_production_validator_accepts():
    from scripts.function_tracer_pcode.authority.decision import canonical_result
    from scripts.function_tracer_pcode.checker.output_preparation import OutputPreparer
    from scripts.function_tracer_pcode.checker.output_schema import (
        required_headroom_bytes,
        validate_envelope_headroom,
    )

    # 本番の検査が受け入れる設定（headroom = schema から導いた下限）で、封印も本物
    headroom = required_headroom_bytes()
    policy = BudgetPolicy(serialization_bytes=headroom + 64 * 1024, envelope_headroom_bytes=headroom)
    validate_envelope_headroom(policy)
    result = _decided_result()
    result.prepared_semantic_payload = OutputPreparer(policy).prepare(
        result, result.prepared_semantic_payload.options,
    )
    evidence, session = result._canonical_finalization_context

    def seal(preimage):
        return canonical_result.build_canonical_result_finalization_bundle(
            result_payload_preimage=preimage, evidence=evidence, session=session,
        )

    natural = build_final_result_envelope(result, seal=seal)
    bundle_bytes = RESULT_JSON_POLICY.measure(natural.payload[BUNDLE_KEY])
    # 診断の本体だけなら収まるが、本体と封印は収まらない大きさ
    free = natural.plan.max_bytes - natural.total_bytes
    result.pairwise_stats = {"pad": "p" * (free + bundle_bytes // 2)}
    envelope = build_final_result_envelope(result, seal=seal)
    assert envelope.total_bytes <= envelope.plan.max_bytes == natural.plan.max_bytes
    # 封印の場所は、切り詰めてよい診断を marker にして空ける（どれを切るかは順と大きさで決まる）
    assert envelope.truncated_metadata
    assert all(envelope.payload[key]["truncated"] is True for key in envelope.truncated_metadata)
    preimage = {key: value for key, value in envelope.payload.items() if key != BUNDLE_KEY}
    canonical_result.validate_canonical_result_finalization_bundle(
        envelope.payload[BUNDLE_KEY], result_payload_preimage=preimage,
    )


def test_composition_refuses_markers_that_cannot_fit_instead_of_overflowing():
    from scripts.function_tracer_pcode.checker.output_preparation import (
        FieldOwner,
        RESULT_FIELDS,
        compose_result_preimage,
    )

    from scripts.function_tracer_pcode.checker.output_preparation import Overflow

    result = _decided_result()
    natural = compose_result_preimage(result)
    # A + B と切り詰めてはいけない C は入るが、切り詰めてよい C は marker でも入らない
    kept = [
        item.key for item in RESULT_FIELDS
        if item.owner is not FieldOwner.METADATA or item.overflow is not Overflow.TRUNCATE
    ]
    limit = RESULT_JSON_POLICY.measure({key: natural.payload[key] for key in kept if key in natural.payload}) + 20
    prepared = result.prepared_semantic_payload
    result.prepared_semantic_payload = dataclasses.replace(
        prepared, plan=dataclasses.replace(prepared.plan, max_bytes=limit, headroom_bytes=limit - 1),
    )
    # 黙って省かず（marker すら無い field を作らず）、出力の契約違反にする
    with pytest.raises(OutputEnvelopeInvariantViolation, match="does not fit even as markers"):
        compose_result_preimage(result)

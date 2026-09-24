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
    OutputEnvelopeInvariantViolation,
    build_final_result_envelope,
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
    with pytest.raises(OutputEnvelopeInvariantViolation, match="does not fit the rest of the envelope"):
        build_final_result_envelope(result, seal=huge_bundle)
    # 残りの予算で止まる（1000 万の event を書き出さない）
    assert len(pulled) < 200
    assert room > 0


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
    from scripts.function_tracer_pcode.core.expression import estimate_legacy_dict_bytes

    siblings = []
    for branch in range(64):
        chain = Expression(ExpressionType.CONSTANT, value=branch, size=4)
        for depth in range(2_000):
            chain = Expression.binary_op("+", chain, Expression(ExpressionType.CONSTANT, value=depth, size=4))
        siblings.append(chain)
    root = siblings[0]
    for sibling in siblings[1:]:
        root = Expression.binary_op("+", root, sibling)
    limit = 200_000
    estimate, elapsed, _ = _measured(lambda: estimate_legacy_dict_bytes(root, max_bytes=limit))
    assert estimate == limit + 1
    full, full_elapsed, _ = _measured(lambda: estimate_legacy_dict_bytes(root, max_bytes=None))
    assert full > limit
    # 上限で止まる見積りは、全部を数える見積りより十分に早い
    assert elapsed < full_elapsed / 4

# -*- coding: utf-8 -*-
"""Issue #22 PR-22-D（3 回目の修正）: 有界性を **合成的** に閉じる。

固定する契約:

* live object から prepared representation までの全経路で、予算を知らない producer が
  入力の大きさに比例する完成 container / 文字列を先に作れない。record は `json_items()`
  で source を返し、walker が 1 要素ずつ引き出して数え、予算で止まる（C1〜C3）。
* B5: legacy reason の重い証拠は authority 確定 **前** に有界・canonical・live 非参照へ
  変換される。canonical reason の id と判定は変わらず、最終 envelope は巨大な object を
  辿り直さない（B5-1〜B5-3）。
* headroom は出力 schema から導く（H1〜H4）。B の field は schema の上限を超えられない。
"""

from __future__ import annotations

import json
import time
import tracemalloc
from collections.abc import Mapping
from types import SimpleNamespace

import pytest

from scripts.function_tracer_pcode.authority.lifecycle import production_boundary
from scripts.function_tracer_pcode.checker import output_preparation, output_schema
from scripts.function_tracer_pcode.checker.cause_aggregate import attach_cause_aggregate
from scripts.function_tracer_pcode.checker.debug_trace import Attempt, DebugTrace
from scripts.function_tracer_pcode.checker.output_preparation import (
    FieldOwner,
    OutputEnvelopeInvariantViolation,
    OutputField,
    OutputPreparer,
    Overflow,
    RESULT_FIELDS,
    BUNDLE_KEY,
    build_final_result_envelope,
    fields_owned_by,
    finitize_legacy_reasons,
)
from scripts.function_tracer_pcode.checker.output_schema import (
    EnvelopeHeadroomTooSmall,
    OutputSchemaMissing,
    authority_field_bounds,
    metadata_field_bounds,
    required_headroom_bytes,
    validate_envelope_headroom,
)
from scripts.function_tracer_pcode.checker.unknown_reason import (
    DETAIL_MAX_CHARS,
    MATCH_AUTHORITY_DIGEST,
    UNKNOWN_REASON_ROW,
    _match_legacy_reasons,
    bounded_match_evidence,
    make_unknown_reason,
)
from scripts.function_tracer_pcode.config.settings import expression_budget_policy
from scripts.function_tracer_pcode.core.analysis import DeferredCallInfo, ReturnInfo
from scripts.function_tracer_pcode.core.budget_policy import BudgetPolicy, budget_policy_scope
from scripts.function_tracer_pcode.core.call_target import CallTargetRef
from scripts.function_tracer_pcode.core.errors import (
    ExpressionSizeBudgetExceeded,
    pair_failure_scope,
    reset_pair_failure_scopes,
)
from scripts.function_tracer_pcode.core.expression import Expression
from scripts.function_tracer_pcode.core.json_encoding import (
    RESULT_JSON_POLICY,
    BoundedEvidence,
    row_max_bytes,
)
from scripts.function_tracer_pcode.core.signature import FunctionSignature
from scripts.function_tracer_pcode.smt import SolverStatus
from scripts.function_tracer_pcode.tests.unit.test_issue106_pair_limitation_propagation import (
    _emit_one_production_signal,
    _new_checker,
    _run_pair,
)
from scripts.function_tracer_pcode.tests.unit.test_issue125_limitation_finalization import (
    _connector,
)
from scripts.function_tracer_pcode.tests.unit.test_issue22d_output_preparation import (
    _analyses,
    _analyze_from,
    _decided_result,
)

from conftest import create_mock_analysis, create_mock_result


_SMALL = BudgetPolicy(serialization_bytes=64_000, envelope_headroom_bytes=16_000)


@pytest.fixture(autouse=True)
def _clean_pair_state():
    reset_pair_failure_scopes()
    yield
    reset_pair_failure_scopes()


def _measured(function):
    """(経過秒, 確保した最大 byte) を返す。"""

    tracemalloc.start()
    started = time.perf_counter()
    try:
        function()
        return time.perf_counter() - started, tracemalloc.get_traced_memory()[1]
    finally:
        tracemalloc.stop()


class _CountingSequence:
    """要素を引き出された回数を数える列（walker が 1 要素ずつ引き出すことを確かめる）。"""

    def __init__(self, count, item="x"):
        self.count = count
        self.item = item
        self.pulled = 0

    def __len__(self):
        return self.count

    def __bool__(self):
        return self.count > 0

    def __iter__(self):
        for _ in range(self.count):
            self.pulled += 1
            yield self.item


# ---------------------------------------------------------------------------
# C1〜C3: producer は予算を知らなくても、表現は予算で止まる
# ---------------------------------------------------------------------------


def test_c1_one_output_record_with_two_million_inner_elements_stops_at_the_budget():
    """signature の parameters が 200 万件でも、残り予算の分しか写さずに限界になる。"""

    parameters = _CountingSequence(2_000_000, {"name": "a", "data_type": "int", "index": 0})
    result = create_mock_result(is_equivalent=True)
    result.function1_signature = FunctionSignature(return_type="int", parameters=parameters)

    def _prepare():
        with pair_failure_scope(("c1-output",), None), budget_policy_scope(_SMALL):
            with pytest.raises(ExpressionSizeBudgetExceeded):
                OutputPreparer(_SMALL).prepare(result)

    elapsed, peak = _measured(_prepare)
    assert parameters.pulled < 5_000  # 48 KB の予算に届くまでの要素だけ
    assert elapsed < 1.0
    assert peak < 4 * 1024 * 1024


def test_c1_one_analysis_record_with_two_million_inner_elements_stops_at_the_budget():
    """return 1 件の validation_blockers が 200 万件でも、解析の表現は予算で止まる。"""

    analysis = create_mock_analysis("func1", return_type="int")
    blockers = _CountingSequence(2_000_000, "blocker")
    analysis.returns = [ReturnInfo(
        address="0x1", value=Expression.constant(1, 4), validation_blockers=blockers,
    )]

    def _serialize():
        with pair_failure_scope(("c1-analysis",), None), budget_policy_scope(_SMALL):
            with pytest.raises(ExpressionSizeBudgetExceeded):
                analysis.to_dict()

    elapsed, peak = _measured(_serialize)
    assert blockers.pulled < 10_000
    assert elapsed < 1.0
    assert peak < 4 * 1024 * 1024


def test_c2_a_nested_record_with_one_huge_field_is_not_copied_or_encoded():
    """deferred call（解析の中の record）の 1 field が 50 MB でも、写さず encode せずに止まる。"""

    analysis = create_mock_analysis("func1", return_type="int")
    huge = "日" * (50 * 1024 * 1024 // 3)
    info = DeferredCallInfo(
        target_ref=CallTargetRef.from_name("callee"), domain_policy={"blob": huge},
    )
    analysis.deferred_calls = {("k",): info}

    def _serialize():
        with pair_failure_scope(("c2",), None), budget_policy_scope(_SMALL):
            with pytest.raises(ExpressionSizeBudgetExceeded):
                analysis.to_dict()

    elapsed, peak = _measured(_serialize)
    assert elapsed < 1.0
    assert peak < 4 * 1024 * 1024


def test_c3_a_producer_built_huge_string_is_bounded_before_authority_and_in_the_row():
    """producer が作成時に連結した巨大な自由文でも、authority 前と出力の行で有界になる。"""

    detail = "".join(f"part{index};" for index in range(2_000_000))
    record = make_unknown_reason(
        "unknown", stage="S", detail=detail,
        object_target_key=("key",) + tuple(range(100_000)),
    )
    result = create_mock_result(is_equivalent=None)
    result.unknown_reasons = [record]
    result.unknown_recovery_actions = []
    finitize_legacy_reasons(result)
    finitized = result.unknown_reasons[0]
    assert len(finitized.detail) <= DETAIL_MAX_CHARS + 64
    assert type(finitized.object_target_key) is BoundedEvidence
    # 行 schema の上限: 有界化していない record でも出力の行は上限を超えない
    for candidate in (record, finitized):
        prepared = RESULT_JSON_POLICY.prepare(candidate)
        assert prepared.encoded_bytes <= row_max_bytes(UNKNOWN_REASON_ROW)
    # canonical reason の自由文（authority 後の producer）も有界な入力から作られる
    decided = _decided_result()
    decided.unknown_reasons = [record] * 3
    envelope = build_final_result_envelope(decided)
    rows = envelope.payload["unknown_reasons"]
    assert all(len(json.dumps(row, ensure_ascii=False)) <= row_max_bytes(UNKNOWN_REASON_ROW) for row in rows)


# ---------------------------------------------------------------------------
# B5: 重い証拠は authority 前に有界化、canonical reason は不変、envelope は辿り直さない
# ---------------------------------------------------------------------------


class _WatchedTuple(tuple):
    """引き出された要素の数を数える tuple（authority 後に辿り直していないことを確かめる）。"""

    watching = False
    visits = 0

    def __iter__(self):
        for item in super().__iter__():
            if _WatchedTuple.watching:
                _WatchedTuple.visits += 1
            yield item


def _legacy_reason(key, evidence):
    return make_unknown_reason(
        "unknown", stage="S_B5", detail="legacy", object_target_key=key,
        object_evidence=evidence,
    )


def _b5_plan(key, evidence):
    def _plan(*_args, **_kwargs):
        _emit_one_production_signal()
        result = create_mock_result(is_equivalent=None, solver_status=SolverStatus.UNKNOWN)
        reason = _legacy_reason(key, evidence)
        result.unknown_reasons = [reason]
        trace = DebugTrace(planned_phases=["P0_BASE"], known_phases=["P0_BASE"])
        trace.add_attempt(Attempt(
            attempt_id=0, retry_count=0, phase="P0_BASE", stage_path=["P0_BASE"],
            strategy="pairwise", result=None, transition_reason="UNKNOWN",
            unknown_reasons=[reason],
        ))
        result.debug_trace = trace
        return result

    return _plan


_ORIGINAL_FINISH = production_boundary._profiled_finish


def _run_b5(monkeypatch, key, evidence):
    seen = {}
    original = _ORIGINAL_FINISH

    def _spy(connector, session, result):
        legacy = result.unknown_reasons[0]
        seen["legacy_key_type"] = type(legacy.object_target_key)
        seen["legacy_evidence_type"] = type(legacy.object_evidence)
        seen["prepared"] = result.prepared_semantic_payload is not None
        return original(connector, session, result)

    monkeypatch.setattr(production_boundary, "_profiled_finish", _spy)
    checker = _new_checker(_connector())
    result = _run_pair(
        analyze=_analyze_from(*_analyses()), stage_plan=_b5_plan(key, evidence), checker=checker,
    )
    return result, seen


def test_b5_heavy_legacy_evidence_is_bounded_before_authority_and_never_rewalked(monkeypatch):
    huge_key = _WatchedTuple(("call_effect_blocker",) + tuple(range(300_000)))
    huge_evidence = {"blob": _WatchedTuple(tuple(range(300_000)))}
    result, seen = _run_b5(monkeypatch, huge_key, huge_evidence)
    control, _ = _run_b5(monkeypatch, ("call_effect_blocker", 1), {"blob": (1,)})

    # 1. authority（finish）へ入る前に有界化され、出力は準備済み
    assert seen["legacy_key_type"] is BoundedEvidence
    assert seen["legacy_evidence_type"] is BoundedEvidence
    assert seen["prepared"] is True
    # 2. legacy の証拠は有界な行として準備済み（予算の中）
    rows = result.prepared_semantic_payload.raw_limitation_evidence.value()
    assert rows and rows[0]["stage"] == "S_B5"
    assert result.prepared_semantic_payload.raw_limitation_evidence.encoded_bytes < 16_384
    # 3. canonical reason の id と判定は重い証拠に依らない
    assert [r.reason_id for r in result.unknown_reasons] == [r.reason_id for r in control.unknown_reasons]
    assert result.final_outcome == control.final_outcome == "UNKNOWN"
    # 4. authority 確定後（原因集計・最終 envelope・to_dict）は巨大な object を辿らない
    _WatchedTuple.visits = 0
    _WatchedTuple.watching = True
    try:
        attach_cause_aggregate(result)
        envelope = build_final_result_envelope(result)
        result.to_dict()
    finally:
        _WatchedTuple.watching = False
    assert _WatchedTuple.visits == 0
    payload = json.loads(envelope.text)
    assert payload["final_outcome"] == "UNKNOWN"
    assert payload["unknown_cause_aggregate"]["schema"] == "unknown-cause-aggregate-v1"
    assert "error" not in payload["unknown_cause_aggregate"]
    assert envelope.total_bytes < 2 * 1024 * 1024


def test_b5_a_sealed_canonical_key_is_only_peeked_within_the_inline_bound():
    """canonical reason の key（authority が封印した値）は、authority 後の集計・envelope でも
    有界な表現の分（EVIDENCE_INLINE_BYTES）しか辿らない。"""

    from scripts.function_tracer_pcode.checker.unknown_reason import UnknownReasonRecord

    result = _decided_result()
    sealed = _WatchedTuple(("return_observation_pair_v2",) + tuple(range(300_000)))
    canonical = [
        UnknownReasonRecord(**{**record.__dict__, "object_target_key": sealed})
        for record in result.unknown_reasons
    ]
    assert canonical
    result.unknown_reasons = canonical
    result.unknown_cause_aggregate = None
    _WatchedTuple.visits = 0
    _WatchedTuple.watching = True
    try:
        attach_cause_aggregate(result)
        envelope = build_final_result_envelope(result)
    finally:
        _WatchedTuple.watching = False
    assert _WatchedTuple.visits < 2_048 * len(canonical)
    row = envelope.payload["unknown_reasons"][0]
    assert row["object_target_key"]["bounded_evidence"] == "v1"


def test_c4_a_record_to_dict_inside_the_pair_budget_never_expands_a_shared_dag():
    """record の `to_dict()` は pair の予算の中では必ず数える（DAG を木に展開しない）。"""

    node = Expression.parameter("p", 0, 4)
    for _ in range(40):
        node = Expression.binary_op("INT_ADD", node, node)
    record = ReturnInfo(address="0x1", value=node)

    def _serialize():
        with pair_failure_scope(("c4",), None), budget_policy_scope(_SMALL):
            with pytest.raises(ExpressionSizeBudgetExceeded):
                record.to_dict()

    elapsed, _peak = _measured(_serialize)
    assert elapsed < 1.0


def test_b5_legacy_matching_uses_digests_equal_to_canonical_value_equality():
    """有界化した legacy key と cause の canonical key は digest で照合できる（等しさは同じ）。"""

    from scripts.function_tracer_pcode.authority.contracts import canonical_value

    key = ("return_coverage", ("target_schema_version", 3)) + tuple(range(5_000))
    legacy = make_unknown_reason("unknown", stage="S", object_target_key=key)
    finitized = bounded_match_evidence(legacy.object_target_key)
    assert type(finitized) is BoundedEvidence and finitized.match_digest(MATCH_AUTHORITY_DIGEST)
    bounded_record = legacy.__class__(**{**legacy.__dict__, "object_target_key": finitized})
    cause = SimpleNamespace(
        cause_id=SimpleNamespace(canonical_target_key=canonical_value(key)),
        proof_requirement_ids=(),
    )
    other = SimpleNamespace(
        cause_id=SimpleNamespace(canonical_target_key=canonical_value(key[:-1])),
        proof_requirement_ids=(),
    )
    matched, kind = _match_legacy_reasons("unknown", cause, (bounded_record,), {"unknown": 2})
    assert kind == "exact" and matched == (bounded_record,)
    matched, kind = _match_legacy_reasons("unknown", other, (bounded_record,), {"unknown": 2})
    assert matched == () and kind is None


# ---------------------------------------------------------------------------
# H1〜H4: headroom は出力 schema から導く
# ---------------------------------------------------------------------------


def test_h1_every_authority_and_metadata_field_has_a_schema_bound():
    authority = set(fields_owned_by(FieldOwner.AUTHORITY)) - {BUNDLE_KEY}
    metadata = set(fields_owned_by(FieldOwner.METADATA))
    assert set(authority_field_bounds()) == authority
    assert set(metadata_field_bounds()) == metadata


def test_h2_the_default_headroom_covers_the_schema_and_a_smaller_one_is_refused(monkeypatch):
    policy = expression_budget_policy({})
    assert required_headroom_bytes() <= policy.envelope_headroom_bytes
    validate_envelope_headroom(policy)
    with pytest.raises(EnvelopeHeadroomTooSmall):
        validate_envelope_headroom(BudgetPolicy(serialization_bytes=1 << 26, envelope_headroom_bytes=1000))
    monkeypatch.setenv("FT_ENVELOPE_HEADROOM_BYTES", "1000")
    with pytest.raises(EnvelopeHeadroomTooSmall):
        _new_checker(None)


def test_h3_the_schema_derived_headroom_holds_a_worst_case_authority_output(monkeypatch):
    """最大行数・最悪の行で埋めた B でも、schema から導いた headroom に収まる。"""

    monkeypatch.setattr(output_schema, "MAX_UNKNOWN_REASON_ROWS", 4)
    monkeypatch.setattr(output_schema, "MAX_RECOVERY_ACTION_ROWS", 4)
    monkeypatch.setattr(output_schema, "MAX_RELATION_ROWS", 8)
    result = _decided_result()
    worst = make_unknown_reason(
        "unknown", stage="s" * 10_000, pair_or_case="p" * 10_000, detail="\x00" * 100_000,
        object_target_key=tuple(range(50_000)), object_evidence={"e": tuple(range(50_000))},
        proof_obligation_id=tuple(range(50_000)),
    )
    result.unknown_reasons = [worst] * 4
    result.unknown_recovery_actions = []
    long_id = "\x01" * output_schema.ID_MAX_CHARS
    row = {name.key: long_id for name in output_schema.C_ACTIVE_BASE_ROW}
    result.canonical_c_active_base = tuple(dict(row) for _ in range(8))
    unlimited = result.prepared_semantic_payload
    headroom = required_headroom_bytes()
    limit = unlimited.plan.prepared_bytes + headroom
    result.prepared_semantic_payload = unlimited.__class__(**{
        **unlimited.__dict__,
        "plan": unlimited.plan.__class__(**{
            **unlimited.plan.__dict__, "max_bytes": limit, "headroom_bytes": headroom,
        }),
    })
    envelope = build_final_result_envelope(result)
    assert envelope.preimage_bytes <= limit
    assert envelope.payload["final_outcome"] == result.final_outcome


def test_h4_authority_output_beyond_its_schema_is_an_invariant_violation(monkeypatch):
    result = _decided_result()
    row = {column.key: "x" for column in output_schema.C_ACTIVE_BASE_ROW}
    result.canonical_c_active_base = tuple(dict(row) for _ in range(output_schema.MAX_RELATION_ROWS + 1))
    with pytest.raises(OutputEnvelopeInvariantViolation, match="rows over"):
        build_final_result_envelope(result)

    result = _decided_result()
    bounds = authority_field_bounds()
    tight = {**bounds, "unknown_reasons": bounds["unknown_reasons"].__class__(
        "unknown_reasons", 10, "test", max_rows=256, rows_attr="unknown_reasons",
    )}
    monkeypatch.setattr(output_schema, "authority_field_bounds", lambda _policy=None: tight)
    result.unknown_reasons = [make_unknown_reason("unknown", detail="d")]
    with pytest.raises(OutputEnvelopeInvariantViolation, match="schema bound"):
        build_final_result_envelope(result)


def test_h4_m3_a_new_authority_field_must_extend_the_output_schema(monkeypatch):
    """M-3: B の field を足すなら、変わるのは出力 schema（上限の 1 行）だけ。"""

    result = _decided_result()
    extra = OutputField("extra_authority", FieldOwner.AUTHORITY, lambda r, o: "v", Overflow.INVARIANT)
    monkeypatch.setattr(output_preparation, "RESULT_FIELDS", RESULT_FIELDS + (extra,))
    with pytest.raises(OutputSchemaMissing):
        build_final_result_envelope(result)
    bounds = authority_field_bounds()
    extended = {**bounds, "extra_authority": bounds["final_outcome"].__class__("extra_authority", 64, "test")}
    monkeypatch.setattr(output_schema, "authority_field_bounds", lambda _policy=None: extended)
    assert build_final_result_envelope(result).payload["extra_authority"] == "v"

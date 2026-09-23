# -*- coding: utf-8 -*-
"""Issue #22 PR-22-D: 横断監査（3 回目の修正後）で見つけた経路を固定する。

各 test は、監査で見つけた欠陥の形を 1 つずつ再現する（直す前の head では落ちる）。
"""

from __future__ import annotations

import ast
import enum
import hashlib
import inspect
import json
import time
import tracemalloc
from types import SimpleNamespace

import pytest

from scripts.function_tracer_pcode.authority.lifecycle import production_boundary
from scripts.function_tracer_pcode.checker import cause_aggregate, output_schema
from scripts.function_tracer_pcode.checker.debug_trace import Attempt, DebugTrace
from scripts.function_tracer_pcode.checker.output_preparation import (
    OutputEnvelopeInvariantViolation,
    OutputPreparer,
    build_final_result_envelope,
    finitize_legacy_reasons,
)
from scripts.function_tracer_pcode.checker.unknown_reason import (
    TYPED_CAUSE_KEY_INLINE_BYTES,
    UNKNOWN_REASON_ROW,
    _production_target_key,
    bounded_match_evidence,
    make_unknown_reason,
)
from scripts.function_tracer_pcode.core.budget_policy import BudgetPolicy
from scripts.function_tracer_pcode.core.canonical_digest import canonical_merkle_digest
from scripts.function_tracer_pcode.core.errors import reset_pair_failure_scopes
from scripts.function_tracer_pcode.core.expression import Expression
from scripts.function_tracer_pcode.core.json_encoding import (
    EVIDENCE_SUMMARY_MAX_BYTES,
    LEGACY,
    RESULT_JSON_POLICY,
    TEXT,
    BoundedEvidence,
    Column,
    JsonBudget,
    JsonBudgetExhausted,
    JsonEncodingPolicy,
    nested,
    row_max_bytes,
)
from scripts.function_tracer_pcode.proof.obligations.snapshot import SnapshotFingerprintCodec
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

from conftest import create_mock_result


_ORIGINAL_FINISH = production_boundary._profiled_finish


@pytest.fixture(autouse=True)
def _clean_pair_state():
    reset_pair_failure_scopes()
    yield
    reset_pair_failure_scopes()


def _trace_with_reason(reason):
    trace = DebugTrace(planned_phases=["P0_BASE"], known_phases=["P0_BASE"])
    trace.add_attempt(Attempt(
        attempt_id=0, retry_count=0, phase="P0_BASE", stage_path=["P0_BASE"],
        strategy="pairwise", result=None, transition_reason="UNKNOWN",
        unknown_reasons=[reason], solver_results={"all_results": []},
    ))
    return trace


def _pilot_pair(monkeypatch, build_result):
    seen = []

    def _spy(connector, session, result):
        seen.append((result.final_outcome if hasattr(result, "final_outcome") else None,
                     [r.reason_id for r in result.unknown_reasons]))
        return _ORIGINAL_FINISH(connector, session, result)

    monkeypatch.setattr(production_boundary, "_profiled_finish", _spy)

    def _plan(*_args, **_kwargs):
        _emit_one_production_signal()
        result = create_mock_result(is_equivalent=None, solver_status=SolverStatus.UNKNOWN)
        build_result(result)
        return result

    result = _run_pair(
        analyze=_analyze_from(*_analyses()), stage_plan=_plan, checker=_new_checker(_connector()),
    )
    return result, seen


# ---------------------------------------------------------------------------
# authority 前の診断の準備は fail-open（診断の欠陥で判定を壊さない）
# ---------------------------------------------------------------------------


def test_a_bug_in_the_cause_evidence_builder_does_not_break_the_pair(monkeypatch):
    def _broken(*_args, **_kwargs):
        raise KeyError("diagnostic bug")

    monkeypatch.setattr(cause_aggregate, "_event_views", _broken)
    reason = make_unknown_reason("unknown", stage="S")
    result, seen = _pilot_pair(monkeypatch, lambda r: (
        setattr(r, "unknown_reasons", [reason]), setattr(r, "debug_trace", _trace_with_reason(reason)),
    ))
    assert seen and result.final_outcome == "UNKNOWN"
    cause_aggregate.attach_cause_aggregate(result)
    aggregate = json.loads(build_final_result_envelope(result).text)["unknown_cause_aggregate"]
    assert "diagnostic bug" in aggregate["error"]


# ---------------------------------------------------------------------------
# authority 前に分かる B の大きさは、判定の前に確かめる
# ---------------------------------------------------------------------------


def test_recovery_actions_over_their_schema_bound_are_a_limitation_before_finish(monkeypatch):
    bounds = output_schema.authority_field_bounds()
    tight = dict(bounds)
    tight["unknown_recovery_actions"] = bounds["unknown_recovery_actions"].__class__(
        "unknown_recovery_actions", 2_000, "test", max_rows=4, rows_attr="unknown_recovery_actions",
    )
    monkeypatch.setattr(output_schema, "authority_field_bounds", lambda _policy=None: tight)

    def _many_actions(result):
        # recovery plan に obligation を持つ reason（action が出る）
        reasons = [
            make_unknown_reason("return_width_bridge_missing", stage=f"S{index}")
            for index in range(40)
        ]
        result.unknown_reasons = reasons
        result.__post_init__()

    result, seen = _pilot_pair(monkeypatch, _many_actions)
    # finish が受け取ったのは限界の UNKNOWN（出力の契約違反で ERROR にしない）
    assert seen and "expression_size_budget_exceeded" in seen[0][1]
    assert "return_width_bridge_missing" not in seen[0][1]
    assert result.final_outcome == "UNKNOWN"
    build_final_result_envelope(result)


# ---------------------------------------------------------------------------
# authority 後は live な trace / A の値を読み直さない
# ---------------------------------------------------------------------------


def test_diagnostics_and_text_after_authority_read_only_prepared_values(monkeypatch):
    reason = make_unknown_reason("unknown", stage="S")
    result, _seen = _pilot_pair(monkeypatch, lambda r: (
        setattr(r, "unknown_reasons", [reason]),
        setattr(r, "debug_trace", _trace_with_reason(reason)),
        setattr(r, "constrained_fragments", ["prepared-fragment"]),
    ))
    before = json.loads(build_final_result_envelope(result).text)["diagnostics"]["timings"]["attempts"]
    # 準備の後に live な値を中身だけ書き換える（差し替えではないので書く側では拒めない）
    result.debug_trace.attempts.append(result.debug_trace.attempts[0])
    result.constrained_fragments.append("LIVE-AFTER-AUTHORITY")

    class _Boom:
        def getName(self):  # noqa: N802 - Ghidra の API 名
            raise AssertionError("the text read a live Ghidra type after authority")

    if result.function1_signature is not None and result.function1_signature.parameters is not None:
        result.function1_signature.parameters.append({"name": "x", "data_type_obj": _Boom()})
    after = json.loads(build_final_result_envelope(result).text)["diagnostics"]["timings"]["attempts"]
    assert after == before
    text = result.to_string(verbose=True, show_phase_usage=True)
    assert "prepared-fragment" in text and "LIVE-AFTER-AUTHORITY" not in text
    assert "Phase Usage Summary" in text


# ---------------------------------------------------------------------------
# 有界化・行 schema の穴
# ---------------------------------------------------------------------------


class _KeyedOpaque:
    def __init__(self, size):
        self.size = size

    def stable_key(self):
        return tuple(range(self.size))


def test_small_non_json_or_live_legacy_evidence_becomes_bounded_not_an_error():
    reason = make_unknown_reason(
        "unknown", stage="S",
        object_target_key=frozenset({1, 2}),
        object_evidence={"live": _KeyedOpaque(3)},
    )
    result = create_mock_result(is_equivalent=None)
    result.unknown_reasons = [reason]
    result.unknown_recovery_actions = []
    finitize_legacy_reasons(result)
    finitized = result.unknown_reasons[0]
    assert type(finitized.object_target_key) is BoundedEvidence
    assert type(finitized.object_evidence) is BoundedEvidence
    prepared = OutputPreparer(BudgetPolicy.unlimited()).prepare(result)
    assert prepared.raw_limitation_evidence.value()[0]["stage"] == "S"


def test_a_text_column_bounds_values_that_are_not_strings():
    record = make_unknown_reason(
        "unknown", stage=["s" * 1000] * 100, pair_or_case=("c" * 5000, "d" * 5000),
        detail={"d": "x" * 100_000},
    )
    prepared = RESULT_JSON_POLICY.prepare(record)
    assert prepared.encoded_bytes <= row_max_bytes(UNKNOWN_REASON_ROW)


def test_the_canonical_typed_cause_key_is_never_summarized():
    result = _decided_result()
    assert result.unknown_reasons
    worst = {key: "f" * 128 for key in result.unknown_reasons[0].typed_cause_key}
    assert RESULT_JSON_POLICY.measure(worst) <= TYPED_CAUSE_KEY_INLINE_BYTES
    # 最悪の大きさの canonical な key（digest の列がすべて id の上限）でも要約しない
    widest = make_unknown_reason("unknown", typed_cause_key=worst)
    rendered = RESULT_JSON_POLICY.prepare(widest).value()["typed_cause_key"]
    assert "bounded_evidence" not in rendered and rendered == worst
    envelope = build_final_result_envelope(result)
    for row in envelope.payload["unknown_reasons"]:
        assert "bounded_evidence" not in row["typed_cause_key"]


def test_the_lane_key_is_set_only_when_the_diagnostic_carries_the_cause():
    cause = SimpleNamespace(cause_id=SimpleNamespace(canonical_target_key=("k", 1)))
    assert _production_target_key(cause, None) is None
    assert _production_target_key(cause, {"schema": "s", "error": "boom"}) is None
    assert _production_target_key(None, {"cause": {"canonical_target_key": ("k", 1)}}) is None
    assert _production_target_key(cause, {"cause": {"canonical_target_key": {"bounded": 1}}}) == ("k", 1)


# ---------------------------------------------------------------------------
# 出力 schema は authority の型から導く（写し書きしない）
# ---------------------------------------------------------------------------


def test_receipt_and_relation_rows_match_the_authority_payloads():
    from scripts.function_tracer_pcode.authority.decision import conditional, production_cutover

    decided = _decided_result()
    payload = production_cutover.decision_receipt_payload(decided.decision_receipt)
    assert set(payload) == {column.key for column in output_schema.DECISION_RECEIPT_ROW}
    relation = decided.canonical_c_active_base[0]
    assert set(relation) == {column.key for column in output_schema.C_ACTIVE_BASE_ROW}
    # conditional receipt: 公開表現の key（関数の return の dict）と行の列 + assumption_set
    source = ast.parse(inspect.getsource(conditional.conditional_decision_receipt_payload))
    (returned,) = [node.value for node in ast.walk(source) if isinstance(node, ast.Return)]
    keys = {key.value for key in returned.keys}
    assert keys == {column.key for column in output_schema.CONDITIONAL_RECEIPT_FIXED_ROW} | {"assumption_set"}


def test_string_bounds_cover_the_worst_escape_of_every_policy():
    for policy in (RESULT_JSON_POLICY, JsonEncodingPolicy(ensure_ascii=True)):
        # 1 文字の最悪の escape（ascii: 非 BMP = 12 byte、それ以外: 制御文字 = 6 byte）
        for worst_char in ("\x01", "\U0001F600"):
            assert policy.string_bytes(worst_char * 100) <= policy.max_string_bytes(100)
        column = Column("t", TEXT, 64)
        worst = "\U0001F600" * 64 if policy.ensure_ascii else "\x01" * 64
        prepared = policy.prepare({"t": column.source(worst)}).value()["t"]
        assert policy.string_bytes(prepared) <= column.max_value_bytes(policy)


def test_bounded_evidence_fields_cannot_exceed_the_declared_summary_size():
    with pytest.raises(ValueError):
        BoundedEvidence(identity='a"b', identity_kind="x", kind="y")
    with pytest.raises(ValueError):
        BoundedEvidence(identity="a\\b", identity_kind="x", kind="y")
    widest = BoundedEvidence(
        identity="~" * 96, identity_kind="~" * 64, kind="~" * 64,
        encoded_bytes_over=10 ** 19, distinct_nodes=10 ** 19,
    )
    assert RESULT_JSON_POLICY.measure(widest.summary()) <= EVIDENCE_SUMMARY_MAX_BYTES


# ---------------------------------------------------------------------------
# digest の等しさ（監査で見つけた境界）
# ---------------------------------------------------------------------------


class _Coordinate(enum.Enum):
    ORIGIN = (0, 0)


def test_digest_equality_holds_for_container_enum_values_and_colliding_sets():
    from scripts.function_tracer_pcode.authority.contracts import (
        canonical_value,
        streaming_canonical_str_digest,
    )

    assert canonical_value((_Coordinate.ORIGIN,)) == canonical_value(((0, 0),))
    assert canonical_merkle_digest((_Coordinate.ORIGIN,))[0] == canonical_merkle_digest(((0, 0),))[0]
    # hash が衝突する要素は、入れた順で集合の並びが変わる
    left, right = frozenset([1, 2 ** 61]), frozenset([2 ** 61, 1])
    assert list(left) != list(right)
    assert canonical_merkle_digest(left) == canonical_merkle_digest(right)
    for value in (left, {"s": right}, "lone \ud800 surrogate", (_Coordinate.ORIGIN, "\ud800")):
        expected = hashlib.sha256(
            str(canonical_value(value)).encode("utf-8", "surrogatepass")
        ).hexdigest()
        assert streaming_canonical_str_digest(value) == expected


# ---------------------------------------------------------------------------
# 作ってから数える経路（閉路の木・codec が写す opaque な葉）
# ---------------------------------------------------------------------------


def test_a_cyclic_expression_tree_is_counted_while_it_is_built():
    node = Expression.parameter("p", 0, 4)
    for _ in range(16):
        node = Expression.binary_op("INT_ADD", node, node)
    node.operands[0] = node  # 未凍結の式の中の閉路（DAG のまま見積もれない）
    tracemalloc.start()
    started = time.perf_counter()
    try:
        with pytest.raises(JsonBudgetExhausted):
            RESULT_JSON_POLICY.prepare({"e": node}, max_bytes=1000)
        peak = tracemalloc.get_traced_memory()[1]
    finally:
        tracemalloc.stop()
    assert time.perf_counter() - started < 1.0
    assert peak < 16 * 1024 * 1024


class _NestedRecord:
    def __init__(self, leaf):
        self.leaf = leaf

    def json_items(self):
        yield "k", nested({"inner": self.leaf})

    def to_dict(self):
        from scripts.function_tracer_pcode.core.json_encoding import materialize

        return materialize(self)


def test_an_opaque_leaf_is_counted_by_what_the_codec_will_copy():
    record = _NestedRecord(_KeyedOpaque(200_000))
    with pytest.raises(JsonBudgetExhausted):
        RESULT_JSON_POLICY.materialize(record, budget=JsonBudget(1000))
    with pytest.raises(JsonBudgetExhausted):
        SnapshotFingerprintCodec.freeze(record, budget=JsonBudget(1000))


def test_a_long_multibyte_string_is_counted_in_chunks_and_stops_early():
    text = "\U0001F600" * 5_000_000
    started = time.perf_counter()
    # 文字数では上限を超えないが byte では超える: chunk ごとに数えて途中で止まる
    assert RESULT_JSON_POLICY.string_bytes(text, max_bytes=6_000_000) == 6_000_001
    assert time.perf_counter() - started < 1.0
    sample = text[:70_000]
    assert RESULT_JSON_POLICY.string_bytes(sample, max_bytes=10 ** 9) == len(
        json.dumps(sample, ensure_ascii=False).encode()
    )


# ---------------------------------------------------------------------------
# CLI: envelope の契約違反は判定を残した ERROR（本物の except の経路）
# ---------------------------------------------------------------------------


def test_the_cli_envelope_step_turns_a_violation_into_the_error_result(monkeypatch, tmp_path):
    from scripts.function_tracer_pcode.cli.commands import equivalence

    emitted = []
    monkeypatch.setattr(
        equivalence, "build_final_result_envelope",
        lambda *_a, **_k: (_ for _ in ()).throw(
            OutputEnvelopeInvariantViolation("too big", max_bytes=1, requested_bytes=2)
        ),
    )
    monkeypatch.setattr(
        equivalence, "_emit_output_invariant_error_result",
        lambda *_a, **kwargs: (emitted.append(kwargs["violation"]), (_ for _ in ()).throw(SystemExit(2))),
    )
    with pytest.raises(SystemExit):
        equivalence._final_envelope_or_error_result(
            SimpleNamespace(), result=_decided_result(), seal=None,
            binary1_path=str(tmp_path / "a"), binary2_path=str(tmp_path / "b"),
            func_name1="f", func_name2="f", start_time=0.0,
        )
    assert len(emitted) == 1 and str(emitted[0]) == "too big"


class _JavaPrimitiveInt(int):
    """PyGhidra（JPype）の Java primitive（`JInt` / `JLong`）は `int` の subclass。"""


def test_a_fixed_scalar_record_keeps_int_subclasses_like_the_old_to_dict():
    # 実バイナリでは `tracer_storage` が `reg.getOffset()`（Java primitive）を構築後に
    # 代入する。固定形の scalar record は、旧 `to_dict()` と同じくその値をそのまま置き、
    # 出力（CANONICAL）では基底型へ直す。exact type で比べて落としてはいけない。
    from scripts.function_tracer_pcode.core.storage import StorageInfo

    storage = StorageInfo(is_register=True, space_name="register", offset=8, size=8,
                          register_name="x1")
    storage.register_offset = _JavaPrimitiveInt(8)
    legacy = storage.to_dict()
    assert legacy["register_offset"] == 8
    assert type(legacy["register_offset"]) is _JavaPrimitiveInt
    prepared = RESULT_JSON_POLICY.prepare(storage).value()
    assert type(prepared["register_offset"]) is int
    assert prepared == json.loads(json.dumps(legacy))


class _JavaPrimitiveStr(str):
    pass


def _subclassed_payload(n):
    return {
        "offsets": tuple(_JavaPrimitiveInt(i) for i in range(n)),
        "names": [_JavaPrimitiveStr(f"r{i}") for i in range(8)],
        _JavaPrimitiveStr("k"): (_JavaPrimitiveInt(7), 1.5, "x"),
        _JavaPrimitiveInt(3): None,
    }


def test_scalar_subclasses_stay_on_the_fast_path_with_the_general_path_result(monkeypatch):
    # 実バイナリの値には Java primitive（int の subclass）が至る所にある。高速経路が
    # それを一般の経路へ落とすと、replay（Python の int だけ）には出ない速度の退行に
    # なる。高速経路は基底型として数え、一般の経路と同じ値・byte を返す。
    from scripts.function_tracer_pcode.core import json_encoding as je

    scalar_calls = []
    original_scalar = je._Walk.scalar

    def counting_scalar(self, item):
        scalar_calls.append(item)
        return original_scalar(self, item)

    monkeypatch.setattr(je._Walk, "scalar", counting_scalar)
    payload = _subclassed_payload(10_000)
    legacy = RESULT_JSON_POLICY.materialize(payload)
    prepared = RESULT_JSON_POLICY.prepare(payload)
    assert len(scalar_calls) < 100  # 要素ごとに一般の経路の葉へ落ちていない

    base = json.loads(json.dumps(payload, default=str))
    assert json.loads(json.dumps(legacy)) == base
    assert type(legacy["offsets"][0]) is _JavaPrimitiveInt  # LEGACY は値をそのまま置く
    canonical = prepared.value()
    assert canonical == base
    assert type(canonical["offsets"][0]) is int and type(canonical["names"][0]) is str
    assert prepared.encoded_bytes == len(RESULT_JSON_POLICY.dumps(canonical).encode("utf-8"))


def test_a_tuple_with_scalar_subclasses_is_cached_without_poisoning_the_canonical_copy():
    # 実バイナリの tuple はほぼ必ず Java primitive を含むので、それも pair の間 cache する
    # （snapshot のたびに数え直さない）。ただし CANONICAL の写しは基底型へ直す。
    from scripts.function_tracer_pcode.core import json_encoding as je
    from scripts.function_tracer_pcode.core.budget_policy import budget_policy_scope

    shared = (tuple(_JavaPrimitiveInt(i) for i in range(64)), _JavaPrimitiveStr("r"))
    with budget_policy_scope(BudgetPolicy()):
        legacy = RESULT_JSON_POLICY.materialize({"a": shared})
        cached = je._PURE_TUPLE_SIZES.get(RESULT_JSON_POLICY, {}).get(id(shared))
        assert cached is not None and cached[0] is shared and cached[2] is True
        again = RESULT_JSON_POLICY.materialize({"b": shared})
        canonical = RESULT_JSON_POLICY.prepare({"c": shared}).value()
    assert type(legacy["a"][0][0]) is _JavaPrimitiveInt and type(again["b"][1]) is _JavaPrimitiveStr
    assert all(type(item) is int for item in canonical["c"][0])
    assert type(canonical["c"][1]) is str

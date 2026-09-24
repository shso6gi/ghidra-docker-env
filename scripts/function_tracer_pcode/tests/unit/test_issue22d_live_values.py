"""Issue #22 PR-22-D: bounded path は live な値の code（任意の producer）を作業量の外で呼ばない。

round 5 の cross-audit が実行して示した穴を、そのまま入力にして固定する（修正を外すと落ちる）:

* 作業量は上位の owner へ戻る（walk の中で始めた walk・呼ぶ側の作業量で辿る walk）。
* live な値の `__str__` / `__repr__` / `__hash__` / `to_dict()` / 上書きした容器の method を呼ばない
  （cause の集計・切り捨て事実の key・snapshot の codec・集計の key・失敗の文）。
* fingerprint は値を区別できるときだけ作る（型名しか分からない葉・一部だけ辿った列）。
* 出力の失敗の ERROR は、元の失敗を繰り返さず、launch と join する identity で durable になる。
"""

from __future__ import annotations

import json
import types
from collections.abc import Mapping as _AbcMapping
from dataclasses import replace
from types import SimpleNamespace

import pytest

from scripts.function_tracer_pcode.checker.output_preparation import OutputEnvelopeInvariantViolation
from scripts.function_tracer_pcode.checker.unknown_reason import (
    finitize_unknown_reason_record,
    make_unknown_reason,
)
from scripts.function_tracer_pcode.core.canonical_digest import canonical_fingerprint
from scripts.function_tracer_pcode.core.errors import reset_pair_failure_scopes
from scripts.function_tracer_pcode.core.json_encoding import (
    LEGACY,
    RESULT_JSON_POLICY,
    BoundedEvidence,
    JsonBudget,
    JsonBudgetExhausted,
    JsonValueRejected,
    Reducer,
    UNFINGERPRINTED_OPAQUE,
    each,
    evidence,
    metered,
    pairs_of,
    scan,
)
from scripts.function_tracer_pcode.tests.unit.test_issue22d_output_preparation import _decided_result


@pytest.fixture(autouse=True)
def _clean_scopes():
    reset_pair_failure_scopes()
    yield
    reset_pair_failure_scopes()


class _Heavy:
    """型名しか分からない live な object（`__str__` / `__repr__` / `__hash__` が重い）。

    `calls` は bounded path が呼んではいけない code の回数（`__str__` / `__repr__` / `__eq__` と、
    `hashes` とは別の `__hash__`）。test の準備（dict を作る・producer 自身の lookup）の hash は
    `hashes` にだけ数える。
    """

    calls = 0
    hashes = 0

    def __str__(self):
        _Heavy.calls += 1
        return "s" * 2_000_000

    __repr__ = __str__

    def __hash__(self):
        _Heavy.hashes += 1
        return 1

    def __eq__(self, other):
        _Heavy.calls += 1
        return self is other


@pytest.fixture(autouse=True)
def _reset_heavy():
    _Heavy.calls = 0
    _Heavy.hashes = 0
    yield


# ---------------------------------------------------------------------------
# 作業量は上位の owner へ戻る
# ---------------------------------------------------------------------------


class _Adds(Reducer):
    __slots__ = ("count",)

    def __init__(self):
        self.count = 0

    def add(self, element, *, work):
        work.charge(1)
        self.count += 1

    def result(self, *, work):
        return self.count


class _Scanned:
    """`json_items` が要素 2,000 の `scan` を返す record。"""

    def __init__(self, elements, reducer):
        self.elements = elements
        self.reducer = reducer

    def json_items(self):
        yield "count", scan(iter(self.elements), self.reducer)


def test_walks_on_the_caller_work_charge_their_effort_to_it():
    """`count_into(value, work)` を何度呼んでも、走査の作業量は `work` の上限で止まる（呼ぶたびに持ち直さない）。"""

    reducer = _Adds()
    parent = JsonBudget(10_000)
    with pytest.raises(JsonBudgetExhausted):
        for _ in range(200):
            RESULT_JSON_POLICY.count_into(_Scanned(range(2_000), reducer), parent, mode=LEGACY)
    assert reducer.count <= parent.max_bytes


def test_a_walk_started_inside_a_walk_is_charged_to_the_outer_work():
    """converter・`metered` の factory の中で始めた walk は、外の walk の作業量の子（新しい上限で逃れない）。"""

    inner_adds = _Adds()

    def factory(work):
        # 上限なしの内側の walk: 外の walk の作業量へ数えられる
        for _ in range(50):
            RESULT_JSON_POLICY.measure(_Scanned(range(2_000), inner_adds), mode=LEGACY)
        return "done"

    with pytest.raises(JsonBudgetExhausted):
        RESULT_JSON_POLICY.prepare(metered(factory), max_bytes=5_000)
    assert inner_adds.count <= 5_000


def test_a_walk_outside_any_walk_keeps_its_own_bound():
    """walk の外で始めた walk は親を持たない（出力の上限を他の出力と共有しない）。"""

    first = RESULT_JSON_POLICY.prepare(["x" * 1_000], max_bytes=2_000)
    second = RESULT_JSON_POLICY.prepare(["x" * 1_000], max_bytes=2_000)
    assert first.encoded_bytes == second.encoded_bytes


# ---------------------------------------------------------------------------
# callback の protocol
# ---------------------------------------------------------------------------


def test_pairs_of_refuses_an_unregistered_callback():
    calls = []

    def heavy(value):
        calls.append(value)
        return "x" * 5_000_000

    with pytest.raises(TypeError):
        pairs_of(iter([("a", 1)]), heavy)
    with pytest.raises(TypeError):
        pairs_of(iter([("a", 1)]), fn=heavy)
    with pytest.raises(TypeError):
        each([1], heavy)
    assert calls == []


def test_a_one_shot_pairs_stream_is_never_fingerprinted_from_its_suffix():
    """一部だけ辿った `pairs_of(generator)` の証拠は、残りの fingerprint を名乗らない。"""

    def rows(tag):
        return ((f"{tag}{index}", "y" * 60) for index in range(200))

    summary = RESULT_JSON_POLICY.prepare(evidence(pairs_of(rows("a"))), max_bytes=1 << 20).value()
    full = RESULT_JSON_POLICY.token_fingerprint(pairs_of(rows("a")), work=JsonBudget(None))
    empty = RESULT_JSON_POLICY.token_fingerprint(pairs_of(iter(())), work=JsonBudget(None))
    assert summary.get("fingerprint") in {None, full}
    assert summary.get("fingerprint") != empty


# ---------------------------------------------------------------------------
# live な値の code を呼ばない
# ---------------------------------------------------------------------------


class _UserMapping(_AbcMapping):
    calls = 0

    def __init__(self):
        self.data = {"k": 1}

    def __getitem__(self, key):
        _UserMapping.calls += 1
        return self.data[key]

    def __iter__(self):
        _UserMapping.calls += 1
        return iter(self.data)

    def __len__(self):
        _UserMapping.calls += 1
        return 1_000_000

    def items(self):
        _UserMapping.calls += 1
        return list(self.data.items())


def test_user_containers_are_never_iterated_by_the_digest_or_the_walker():
    _UserMapping.calls = 0
    wrapped = types.MappingProxyType(_UserMapping())
    with pytest.raises(TypeError):
        canonical_fingerprint(wrapped, work=JsonBudget(1 << 20))
    with pytest.raises(JsonValueRejected):
        RESULT_JSON_POLICY.prepare(_UserMapping(), max_bytes=1 << 20)
    with pytest.raises(JsonValueRejected):
        RESULT_JSON_POLICY.prepare(wrapped, max_bytes=1 << 20)
    summary = RESULT_JSON_POLICY.prepare(evidence(_UserMapping()), max_bytes=1 << 20).value()
    assert summary["kind"] == "_UserMapping"
    assert _UserMapping.calls == 0
    # 組み込みの mapping を包む proxy は辿る（authority の凍結した値）
    assert canonical_fingerprint(types.MappingProxyType({"k": 1}), work=JsonBudget(1 << 20))


def test_the_cause_aggregate_never_renders_a_live_trace_leaf():
    from scripts.function_tracer_pcode.checker.cause_aggregate import build_trace_cause_evidence
    from scripts.function_tracer_pcode.checker.debug_trace import Attempt, DebugTrace
    from scripts.function_tracer_pcode.core.budget_policy import serialization_scope

    reasons = [
        replace(make_unknown_reason("unknown", stage="P0_BASE", object_target_key=("k", _Heavy())), pair_or_case=(_Heavy(),))
        for index in range(20)
    ]
    _Heavy.calls = 0
    attempt = Attempt(
        attempt_id=1, retry_count=0, phase="P0_BASE", stage_path=[], strategy="pairwise",
        result=None, transition_reason="UNKNOWN", unknown_reasons=reasons,
    )
    result = SimpleNamespace(debug_trace=DebugTrace(attempts=[attempt]))
    with serialization_scope(site="probe", target_parts=("p",), terminal=False, max_bytes=200_000, enabled=True):
        built = build_trace_cause_evidence(result, binary_identities=("L", "R"))
    assert _Heavy.calls == 0
    assert "error" not in built


def test_root_cause_grouping_never_renders_live_evidence_or_units():
    """root cause に集まる record（typed cause を持つ）の証拠と単位の live な値も、描画も hash もしない。"""

    from scripts.function_tracer_pcode.checker.cause_aggregate import build_trace_cause_evidence
    from scripts.function_tracer_pcode.checker.debug_trace import DebugTrace
    from scripts.function_tracer_pcode.core.budget_policy import serialization_scope
    from scripts.function_tracer_pcode.tests.unit.test_issue128_cause_aggregate import (
        _attempt,
        _reason,
        _unary_cause,
    )

    # 構築（`make_unknown_reason`）を通らずに live な値を持つ record: 集計は組み込みの値だけで読む
    reasons = [
        replace(
            _reason("summary_effect_unmodeled", cause=_unary_cause(f"site{index}"), target=f"t{index}"),
            pair_or_case=(_Heavy(), _Heavy()), evidence_refs=(_Heavy(), "ref"),
        )
        for index in range(5)
    ]
    result = SimpleNamespace(debug_trace=DebugTrace(attempts=[_attempt(1, "pairwise", reasons)]))
    _Heavy.calls = _Heavy.hashes = 0
    with serialization_scope(site="probe", target_parts=("p",), terminal=False, max_bytes=1 << 22, enabled=True):
        built = build_trace_cause_evidence(result, binary_identities=("L", "R"))
    assert built.get("root_causes"), built
    assert _Heavy.calls == 0 and _Heavy.hashes == 0


def test_an_enum_that_overrides_value_is_not_asked_for_it():
    import enum

    asked = []

    class _Tricky(enum.Enum):
        A = "a"

        @property
        def value(self):  # noqa: D401 - 上書きした property（producer）
            asked.append(1)
            return "x" * 1_000_000

    fingerprint = canonical_fingerprint((_Tricky.A,), work=JsonBudget(1 << 20))
    assert fingerprint == canonical_fingerprint(("a",), work=JsonBudget(1 << 20))
    RESULT_JSON_POLICY.measure((_Tricky.A,), mode=LEGACY, max_bytes=1 << 20)
    assert asked == []


def test_a_truncation_scope_key_never_renders_its_live_key():
    from scripts.function_tracer_pcode.core.runtime_refs.unknowns import _canonical_budget_source

    source = metered(lambda work: _canonical_budget_source({(_Heavy(),): 1}, work=work))
    with pytest.raises(JsonValueRejected):
        RESULT_JSON_POLICY.prepare(source, max_bytes=500)
    assert _Heavy.calls == 0


def test_the_snapshot_codec_never_calls_a_bare_to_dict():
    from scripts.function_tracer_pcode.proof.obligations.snapshot import SnapshotFingerprintCodec

    built = []

    class _ToDictOnly:
        def to_dict(self):
            built.append(1)
            return {"items": list(range(300_000))}

    with pytest.raises(TypeError):
        SnapshotFingerprintCodec.freeze({"x": _ToDictOnly()}, budget=JsonBudget(100))
    with pytest.raises(TypeError):
        SnapshotFingerprintCodec.digest({"x": _ToDictOnly()})
    assert built == []


def test_aggregation_keys_are_hashed_only_as_plain_values():
    from scripts.function_tracer_pcode.checker.debug_trace import Attempt, DebugTrace

    record = replace(make_unknown_reason("unknown", stage="s"), pair_or_case=tuple(_Heavy() for _ in range(200_000)))
    attempt = Attempt(
        attempt_id=1, retry_count=0, phase="P0_BASE", stage_path=[], strategy="pairwise",
        result=None, transition_reason="UNKNOWN", unknown_reasons=[record],
    )
    counts = dict(DebugTrace(attempts=[attempt]).json_items())["unknown_reason_counts"]
    _Heavy.calls = _Heavy.hashes = 0
    try:
        RESULT_JSON_POLICY.prepare(counts, max_bytes=2_000)
    except JsonBudgetExhausted:
        pass
    assert _Heavy.calls == 0 and _Heavy.hashes == 0


def test_phase_usage_hashes_live_phase_labels_by_identity():
    from scripts.function_tracer_pcode.checker.debug_trace import Attempt, DebugTrace

    attempts = [
        Attempt(attempt_id=index, retry_count=0, phase=_Heavy(), stage_path=[], strategy="pairwise",
                result=None, transition_reason=_Heavy())
        for index in range(3)
    ]
    trace = DebugTrace(attempts=attempts)
    _Heavy.calls = _Heavy.hashes = 0
    try:
        RESULT_JSON_POLICY.prepare(trace.phase_usage_source(), max_bytes=1 << 20)
    except JsonValueRejected:
        pass
    assert _Heavy.calls == 0 and _Heavy.hashes == 0
    # 組み込みの phase 名の行は今までと同じ（known phases → attempt の初出の順）
    plain = DebugTrace(attempts=[
        Attempt(attempt_id=1, retry_count=0, phase="P0_BASE", stage_path=[], strategy="pairwise",
                result=None, transition_reason="UNKNOWN"),
    ])
    rows = RESULT_JSON_POLICY.prepare(plain.phase_usage_source(), max_bytes=1 << 20).value()
    assert rows == [dict(row) for row in plain.get_phase_usage()]


def test_failure_messages_are_built_without_rendering_the_failing_value():
    class _Failing:
        def json_items(self):
            table = {}
            yield "x", table[(_Heavy(),)]

    with pytest.raises(JsonValueRejected) as caught:
        RESULT_JSON_POLICY.prepare(_Failing(), max_bytes=100)
    assert _Heavy.calls == 0
    assert len(str(caught.value)) < 400


# ---------------------------------------------------------------------------
# fingerprint は値を区別できるときだけ
# ---------------------------------------------------------------------------


class _Case:
    def __init__(self, value):
        self.value = value


def test_distinct_live_cases_do_not_merge_after_finitization():
    from scripts.function_tracer_pcode.checker.cause_aggregate import select_primary_reason_records

    first = replace(make_unknown_reason("unknown", stage="s"), pair_or_case=(_Case(1), _Case(2)))
    second = replace(make_unknown_reason("unknown", stage="s"), pair_or_case=(_Case(3), _Case(4)))
    work = JsonBudget(1 << 20)
    finitized = [finitize_unknown_reason_record(item, work=work) for item in (first, second)]
    kept = finitized[0].pair_or_case
    if type(kept) is BoundedEvidence:
        assert kept.unfingerprinted == UNFINGERPRINTED_OPAQUE
    assert finitized[0].pair_or_case != finitized[1].pair_or_case
    assert len(select_primary_reason_records(finitized)) == len(select_primary_reason_records([first, second])) == 2


def test_the_columns_of_one_record_do_not_share_an_authority_fingerprint():
    from scripts.function_tracer_pcode.core.json_encoding import TEXT, Column, EVIDENCE, row_items

    row = (Column("left", EVIDENCE), Column("right", EVIDENCE))
    record = SimpleNamespace(left=("a",) + tuple(range(5_000)), right=("b",) + tuple(range(5_000)))
    prepared = RESULT_JSON_POLICY.prepare(
        metered(lambda _work: dict(row_items(row, record, identity="cause:c1"))), max_bytes=1 << 20,
    ).value()
    assert prepared["left"]["fingerprint"] != prepared["right"]["fingerprint"]
    assert TEXT  # 列の種類は同じ語彙


def test_an_overlong_identity_is_digested_not_truncated():
    long_a = "cause:" + "a" * 200 + "#left"
    long_b = "cause:" + "a" * 200 + "#right"
    work = JsonBudget(1 << 20)
    value = ("x",) + tuple(range(5_000))
    left = BoundedEvidence  # noqa: F841 - 型の名前だけ
    from scripts.function_tracer_pcode.core.json_encoding import bounded_evidence

    first = bounded_evidence(value, work=work, identity=long_a)
    second = bounded_evidence(value, work=work, identity=long_b)
    assert first.fingerprint != second.fingerprint
    assert first.fingerprint.startswith("sha256:")


# ---------------------------------------------------------------------------
# 出力の失敗の ERROR
# ---------------------------------------------------------------------------


def _emit(monkeypatch, result, violation=None):
    from scripts.function_tracer_pcode.authority.decision import canonical_result
    from scripts.function_tracer_pcode.cli.commands import equivalence

    written = []
    persisted = []
    monkeypatch.setattr(equivalence, "output_result", lambda content, *_a, **_k: written.append(content))
    monkeypatch.setattr(canonical_result, "persist_canonical_result_envelope", persisted.append)
    args = SimpleNamespace(verbose=False, debug=False, output=None, quiet=True)
    with pytest.raises(SystemExit):
        equivalence._emit_output_invariant_error_result(
            args, result=result,
            violation=violation or OutputEnvelopeInvariantViolation("too big", max_bytes=1, requested_bytes=2),
            binary1_path="/tmp/a", binary2_path="/tmp/b",
            func_name1="f", func_name2="f", start_time=0.0,
        )
    block = next(content for content in written if "EQUIVALENCE_RESULT_JSON_BEGIN" in content)
    return json.loads(block.split("\n")[1]), persisted


def test_a_receipt_that_cannot_be_written_still_yields_a_durable_error(monkeypatch):
    """取って代わられた receipt の payload が作れない（exact でない receipt）: digest だけの ERROR。"""

    result = _decided_result()
    result.conditional_decision_receipt = object()
    payload, persisted = _emit(monkeypatch, result)
    assert payload["final_outcome"] == "ERROR"
    superseded = payload["superseded_decision_receipt"]
    assert superseded["payload_unavailable"] == "TypeError"
    assert superseded["decision_receipt_digest"] == result.decision_receipt.receipt_digest
    assert len(persisted) == 1


def test_an_error_envelope_that_fails_falls_back_once(monkeypatch):
    """ERROR の出力自身が落ちたら、固定の文と digest だけでもう 1 度だけ出す（traceback にしない）。"""

    from scripts.function_tracer_pcode.cli.commands import equivalence

    original = equivalence.build_final_result_envelope
    calls = []

    def flaky(result, **kwargs):
        calls.append(1)
        if len(calls) == 1:
            raise ValueError("the first ERROR envelope failed")
        return original(result, **kwargs)

    monkeypatch.setattr(equivalence, "build_final_result_envelope", flaky)
    payload, _persisted = _emit(monkeypatch, _decided_result())
    assert len(calls) == 2
    assert "the ERROR envelope also failed" in payload["error_message"]
    assert payload["superseded_decision_receipt"]["payload_unavailable"] == "error_envelope_failed"


def test_the_error_envelope_joins_the_decided_pair_launch(monkeypatch):
    """出力の失敗の ERROR は、確定した pair の execution identity（launch と同じ）を持つ。"""

    result = _decided_result()
    _evidence, session = result._canonical_finalization_context
    payload, _persisted = _emit(monkeypatch, result)
    bundle = payload["canonical_result_finalization_bundle"]
    assert bundle["execution_identity"]["result_occurrence_id"] == session.identity.result_occurrence_id
    assert bundle["execution_payload"] == json.loads(json.dumps(session.execution_payload))


def test_the_text_path_turns_output_failures_into_the_same_error(monkeypatch):
    from scripts.function_tracer_pcode.authority.decision import canonical_result
    from scripts.function_tracer_pcode.cli.commands import equivalence

    result = _decided_result()

    def broken(**_kwargs):
        raise ValueError("canonical result lacks DecisionReceipt")

    result.to_string = broken
    written = []
    monkeypatch.setattr(equivalence, "output_result", lambda content, *_a, **_k: written.append(content))
    monkeypatch.setattr(canonical_result, "persist_canonical_result_envelope", lambda _payload: None)
    args = SimpleNamespace(verbose=False, debug=False, output=None, quiet=True)
    with pytest.raises(SystemExit):
        equivalence._text_or_error_result(
            args, result=result, payload=None, binary1_path="/tmp/a", binary2_path="/tmp/b",
            func_name1="f", func_name2="f", start_time=0.0,
        )
    assert any("OUTPUT_ENVELOPE_INVARIANT_VIOLATION" in content for content in written)


# ---------------------------------------------------------------------------
# 上限の導き方
# ---------------------------------------------------------------------------


def _string_of_bytes(size: int) -> str:
    return "a" * (size - 2)


def test_the_conditional_receipt_bound_is_exact_for_a_payload_at_every_maximum():
    """9 つの member がすべて上限の payload の byte は、schema の上限とちょうど等しい（区切りを数え落とさない）。"""

    from scripts.function_tracer_pcode.authority.decision import conditional
    from scripts.function_tracer_pcode.checker.output_schema import (
        CONDITIONAL_RECEIPT_FIXED_ROW,
        conditional_receipt_max_bytes,
    )

    policy = RESULT_JSON_POLICY
    payload = {
        column.key: _string_of_bytes(column.max_value_bytes(policy)) for column in CONDITIONAL_RECEIPT_FIXED_ROW
    }
    payload["assumption_set"] = [
        _string_of_bytes(conditional.ASSUMPTION_PREMISE_MAX_BYTES)
    ] * conditional.MAX_ASSUMPTION_PREMISES
    assert policy.measure(payload) == conditional_receipt_max_bytes(policy)


def test_the_conditional_receipt_payload_fields_are_the_owner_fields():
    from scripts.function_tracer_pcode.authority.decision import conditional

    import ast
    import inspect
    import textwrap

    tree = ast.parse(textwrap.dedent(inspect.getsource(conditional.conditional_decision_receipt_payload)))
    returned = next(node.value for node in ast.walk(tree) if isinstance(node, ast.Return))
    keys = [key.value for key in returned.keys]
    # payload の member は owner の固定の列 + 仮定の集合（schema の上限はこの 9 つを数える）
    assert set(keys) == set(conditional.CONDITIONAL_RECEIPT_FIXED_FIELDS) | {"assumption_set"}
    assert len(keys) == len(conditional.CONDITIONAL_RECEIPT_FIXED_FIELDS) + 1


@pytest.mark.parametrize("policy_name", ["RESULT_JSON_POLICY", "PERSISTED_ENVELOPE_JSON_POLICY"])
def test_the_marker_bound_covers_a_rejected_path_of_escaped_characters(policy_name):
    from scripts.function_tracer_pcode.checker import output_preparation
    from scripts.function_tracer_pcode.checker.output_schema import (
        MARKER_PATH_MAX_CHARS,
        truncation_marker_max_bytes,
    )
    from scripts.function_tracer_pcode.core import json_encoding

    policy = getattr(json_encoding, policy_name)
    rejected = JsonValueRejected("", path="\x01" * (MARKER_PATH_MAX_CHARS * 2))
    marker = output_preparation._truncation_marker(
        "diagnostics", list(range(10)), remaining_bytes=2 ** 63 - 1, rejected=rejected,
    )
    assert policy.measure(marker) <= truncation_marker_max_bytes(policy, "diagnostics")


def test_the_cause_aggregate_never_calls_a_bare_to_dict():
    from scripts.function_tracer_pcode.checker.cause_aggregate import _as_mapping

    built = []

    class _ToDictOnly:
        def to_dict(self):
            built.append(1)
            return {"x": 1}

    assert _as_mapping(_ToDictOnly()) == {}
    assert built == []
    assert _as_mapping({"a": 1}) == {"a": 1}


def test_a_truncation_value_renders_like_its_identity():
    """出力の切り捨て事実の値は identity（`_canonical_budget_value`）と同じ規則（`stable_key` だけ）。"""

    from scripts.function_tracer_pcode.core.runtime_refs.unknowns import (
        _canonical_budget_source,
        _canonical_budget_value,
    )

    class _ToKeyOnly:
        def to_key(self):
            return ("k",)

    class _StableKey:
        def stable_key(self):
            return ("s", 1)

    for value in (_ToKeyOnly(), _StableKey(), ("x", 1, {"a": [1, 2]})):
        prepared = RESULT_JSON_POLICY.prepare(
            metered(lambda work, value=value: _canonical_budget_source(value, work=work)), max_bytes=1 << 20,
        ).value()
        assert prepared == json.loads(json.dumps(_canonical_budget_value(value)))


def test_bounded_repr_uses_only_builtin_repr():
    from scripts.function_tracer_pcode.core.json_encoding import bounded_repr

    assert bounded_repr(_Heavy()) == "<_Heavy>"
    assert bounded_repr(12) == "12" and bounded_repr("ab") == "'ab'" and bounded_repr(None) == "None"
    assert len(bounded_repr("x" * 10_000)) < 300
    assert bounded_repr(1 << 5_000).startswith("<int ")
    assert _Heavy.calls == 0


def test_scalar_subclasses_are_their_base_values_without_their_own_methods():
    """JPype の `JInt` のような scalar の subclass は基底型の値（subclass の `__str__` / `__hash__` を呼ばない）。

    固定 subset の実バイナリでは identity の中に `JInt` が現れる: 型名の印にすると main と出力が変わる。
    """

    from scripts.function_tracer_pcode.checker.cause_aggregate import freeze_identity
    from scripts.function_tracer_pcode.core.json_encoding import builtin_str, hashable_key

    called = []

    class _JInt(int):
        def __str__(self):
            called.append("str")
            return "never"

        __repr__ = __str__

        def __hash__(self):
            called.append("hash")
            return 0

    value = _JInt(129780670288800)
    frozen = freeze_identity(("parameter", ("int", value)))
    assert frozen == ("parameter", ("int", 129780670288800))
    assert type(frozen[1][1]) is int
    assert builtin_str(("int", value)) == "('int', 129780670288800)"
    key = hashable_key(("int", value), JsonBudget(1 << 20))
    assert key == ("int", 129780670288800) and type(key[1]) is int
    assert called == []

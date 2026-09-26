# -*- coding: utf-8 -*-
"""Issue #110: authority event の契約と、canonical result の封印の作業量（AC-110-S1〜S4）。

- canonical unit の meter は `authority_digest` と同じ規則の大きさを **作らずに** 数え、上限で止まる。
- event の契約は publication gate（digest の前）で強制し、超過は判定の前の登録済みの理由の UNKNOWN。
- 封印・検証・永続化は有限の `SealWork` の中でだけ行い、各段は実行する前に数える。超えれば
  `BundleWorkExceeded` で、部分的な bundle / digest / replay は返らない。
- 上限の内側では bundle の byte 列は変わらない（数えるだけ）。
"""

from __future__ import annotations

import ast
import json
import random
import time
from dataclasses import dataclass
from enum import Enum
from pathlib import Path
from types import SimpleNamespace

import pytest

from scripts.function_tracer_pcode.authority.canonical_units import (
    LimitedUnits,
    canonical_units_within,
    measure_canonical_units,
)
from scripts.function_tracer_pcode.authority.contracts import Outcome, canonical_value
from scripts.function_tracer_pcode.authority.event_contract import (
    AUTHORITY_EVENT_CONTRACT,
    EVENT_CONTRACT_LIMITATION_SITE,
    AuthorityEventContract,
    AuthorityEventContractExceeded,
    EventContractLedger,
)
from scripts.function_tracer_pcode.authority.seal_work import (
    SEAL_COST_MODEL,
    BundleWorkExceeded,
    SealPlan,
    SealWorkBudget,
)

PACKAGE_ROOT = Path(__file__).resolve().parents[2]
NONCE_ENV = "UNKNOWN_TAXONOMY_V2_RESULT_ENTRY_OCCURRENCE_NONCE"


# ---------------------------------------------------------------------------
# canonical unit の meter
# ---------------------------------------------------------------------------


class _Color(Enum):
    RED = "red"
    BLUE = "blue"


@dataclass(frozen=True)
class _Row:
    name: str
    count: int
    tags: tuple


def _random_value(rng: random.Random, depth: int = 0):
    kind = rng.randrange(9 if depth < 4 else 5)
    if kind == 0:
        return None
    if kind == 1:
        return rng.choice([True, False])
    if kind == 2:
        return rng.randrange(-10**12, 10**12)
    if kind == 3:
        return rng.choice([0.5, -1.25, 3.0e10, 1e-7])
    if kind == 4:
        alphabet = 'ab"\\\n\t\x01é漢😀'
        return "".join(rng.choice(alphabet) for _ in range(rng.randrange(12)))
    if kind == 5:
        return tuple(_random_value(rng, depth + 1) for _ in range(rng.randrange(5)))
    if kind == 6:
        return {f"k{rng.randrange(30)}": _random_value(rng, depth + 1) for _ in range(rng.randrange(5))}
    if kind == 7:
        return _Row(f"n{rng.randrange(9)}", rng.randrange(99), (_random_value(rng, depth + 1),))
    return rng.choice(list(_Color))


def _canonical_bytes(value) -> int:
    return len(json.dumps(
        canonical_value(value), sort_keys=True, separators=(",", ":"), ensure_ascii=False,
    ).encode("utf-8", "surrogatepass"))


@pytest.mark.parametrize("seed", range(40))
def test_canonical_units_are_at_least_the_canonical_json_bytes(seed):
    """meter の単位は `authority_digest` が書く canonical JSON の byte 以上（集合が無ければ並べ替えの分だけ多い）。"""

    rng = random.Random(seed)
    value = _random_value(rng)
    units = measure_canonical_units(value, LimitedUnits(10**9))
    assert units >= _canonical_bytes(value)


def test_canonical_units_equal_the_bytes_for_flat_values():
    for value in (None, True, 12345, -0.5, "a\"b\\c\nd\x01é", (1, "x", None), [2, 3]):
        assert measure_canonical_units(value, LimitedUnits(10**6)) == _canonical_bytes(value)


def test_the_meter_stops_before_walking_past_its_limit():
    """上限で止まる（作ってから測らない）: 10^6 要素の列を上限 1,000 単位で測っても一瞬で止まる。"""

    huge = tuple(range(10**6))
    started = time.perf_counter()
    assert canonical_units_within(huge, 1_000) is None
    assert time.perf_counter() - started < 0.5
    long_text = "x" * 50_000_000
    started = time.perf_counter()
    assert canonical_units_within(long_text, 1_000) is None
    assert time.perf_counter() - started < 0.5


def test_the_meter_does_not_recurse():
    nested = ()
    for _ in range(50_000):
        nested = (nested,)
    assert canonical_units_within(nested, 10**7) is not None


# ---------------------------------------------------------------------------
# production の session（SAT-safety の blocker と EQ closure を持つ stream）
# ---------------------------------------------------------------------------


def _sat_blocker(index: int):
    from scripts.function_tracer_pcode.authority.lifecycle.production_signals import (
        SatSafetyBlockerProductionSignal,
    )

    return SatSafetyBlockerProductionSignal(
        action="OBSERVED",
        reason_id="counterexample_analysis_safety_unproven",
        canonical_target_key=("issue110-blocker", index),
        missing_semantic_fact=("counterexample_safety_gate_unproven", "model"),
        evidence_refs=(f"issue110-{index}",),
        producer_id="sat_unsafety_reason_producer",
    )


def _connector():
    from scripts.function_tracer_pcode.authority.domains.analysis_limitation import (
        AnalysisLimitationBlockerSignal,
        AnalysisLimitationPilotEncoder,
    )
    from scripts.function_tracer_pcode.authority.domains.sat_safety import SatSafetyPilotEncoder
    from scripts.function_tracer_pcode.authority.lifecycle.pilot import (
        ProductionDualWritePilotConnector,
    )
    from scripts.function_tracer_pcode.authority.lifecycle.production_signals import (
        CompositeProductionSignalEncoder,
        SatSafetyBlockerProductionSignal,
    )
    from scripts.function_tracer_pcode.authority.lifecycle.reducer import ShadowLifecycleReducer
    from scripts.function_tracer_pcode.authority.process.supervisor import (
        PROCESS_DURABLE_REASON_REGISTRY,
        PROCESS_DURABLE_RECOVERY_REGISTRY,
    )

    return ProductionDualWritePilotConnector(
        ShadowLifecycleReducer(
            reason_registry=PROCESS_DURABLE_REASON_REGISTRY,
            recovery_registry=PROCESS_DURABLE_RECOVERY_REGISTRY,
        ),
        domain_signal_encoder=CompositeProductionSignalEncoder({
            AnalysisLimitationBlockerSignal: AnalysisLimitationPilotEncoder(),
            SatSafetyBlockerProductionSignal: SatSafetyPilotEncoder(),
        }),
    )


def _legacy_result(**overrides):
    fields = dict(
        is_equivalent=None, error_message=None, failure_status=None, failure_message=None,
        unknown_reasons=[], unknown_recovery_actions=[], is_timeout=lambda: False,
    )
    fields.update(overrides)
    return SimpleNamespace(**fields)


def _finished_session(monkeypatch, *, blockers: int, case_id: str = "issue110", contract=None):
    """SAT-safety の blocker を `blockers` 件 emit した session を finish する（pair の台帳の scope の中）。"""

    from scripts.function_tracer_pcode.authority.contracts import authority_digest
    from scripts.function_tracer_pcode.authority.lifecycle.execution_authority import (
        PINNED_SOLVER_EXECUTION_ISSUER,
    )
    from scripts.function_tracer_pcode.authority.lifecycle.production_signals import (
        emit_sat_safety_signal,
        production_signal_scope,
    )
    from scripts.function_tracer_pcode.core.errors import pair_failure_scope

    monkeypatch.setenv(NONCE_ENV, f"{case_id}-occurrence")
    connector = _connector()
    session = connector.begin({"case": case_id})
    if contract is not None:
        session.event_contract = EventContractLedger(contract)
    emitted = []
    with pair_failure_scope(("issue110", case_id), session.identity.result_occurrence_id) as ledger:
        with production_signal_scope(session):
            for index in range(blockers):
                emitted.append(emit_sat_safety_signal(
                    _sat_blocker(index), producer_site_manifest_id="sat-safety-blocker-observed",
                ))
        pending = ledger.pending_failure()
    occurrence_payload = dict(session.execution_payload)
    occurrence_nonce = occurrence_payload.pop("result_entry_occurrence_nonce")
    session.result_entry_occurrence_receipt = PINNED_SOLVER_EXECUTION_ISSUER.issue_result_entry_occurrence(
        result_occurrence_id=session.identity.result_occurrence_id,
        execution_payload_digest=authority_digest(occurrence_payload),
        startup_receipt_digests=(),
        occurrence_nonce=occurrence_nonce,
    )
    return connector, session, emitted, pending


def _attribute_pending_limitation(session, pending):
    """pair の gate がする帰属（限界の cause を予約した枠で publish する）。"""

    from scripts.function_tracer_pcode.authority.domains.analysis_limitation import (
        observe_analysis_limitation,
    )
    from scripts.function_tracer_pcode.authority.lifecycle.production_signals import (
        production_signal_scope,
    )

    limitation = session.event_contract.exceeded
    assert limitation is not None and pending is not None
    with production_signal_scope(session):
        observe_analysis_limitation(
            reason_id=limitation.reason_id, limitation_site=limitation.site,
            target_key=limitation.target_key, missing_semantic_fact=limitation.missing_semantic_fact,
            evidence_refs=limitation.evidence_refs,
        )


# ---------------------------------------------------------------------------
# AC-110-S4: authority が作る cause / relation の数は判定の前に契約の中
# ---------------------------------------------------------------------------


def test_more_causes_than_the_contract_become_a_registered_unknown_before_the_decision(monkeypatch):
    """300 件の cause を作ろうとする pair: 契約の枠（予約を除く 252 件）で止まり、超過は pair の台帳の限界。

    限界の cause は予約した枠で publish でき、判定は登録済みの理由の UNKNOWN（出力時の ERROR ではない）。
    canonical reason の行・relation の行は出力の schema の上限（256 / 512）以下。
    """

    from scripts.function_tracer_pcode.authority.domains.analysis_limitation import (
        ANALYSIS_BUDGET_REASON_ID,
    )

    connector, session, emitted, pending = _finished_session(monkeypatch, blockers=300)
    ordinary = AUTHORITY_EVENT_CONTRACT.ordinary_cause_occurrences
    assert sum(emitted) == ordinary
    assert emitted[ordinary:] == [0] * (300 - ordinary)
    assert session.domain_signal_error_kinds == []
    assert session.event_contract.exceeded is not None
    assert session.event_contract.exceeded.bound == "cause_occurrences"
    _attribute_pending_limitation(session, pending)
    evidence = connector.finish(session, _legacy_result(), case_id="issue110-causes")
    pilot = evidence.pilot_result
    assert pilot.candidate.decision_receipt.outcome is Outcome.UNKNOWN
    rows = pilot.reduction.projection.c_active_base
    assert len(rows) <= AUTHORITY_EVENT_CONTRACT.max_cause_occurrences
    assert len(pilot.reduction.projection.q_open_base) <= AUTHORITY_EVENT_CONTRACT.max_relation_rows
    limitation_rows = [row for row in rows if row.reason_id == ANALYSIS_BUDGET_REASON_ID]
    assert len(limitation_rows) == 1


def test_a_small_relation_contract_stops_the_requirement_rows(monkeypatch):
    """relation の行（occurrence が束ねる requirement）の上限も publication gate で止まる。"""

    contract = AuthorityEventContract(max_cause_occurrences=64, max_relation_rows=12)
    connector, session, emitted, pending = _finished_session(
        monkeypatch, blockers=30, case_id="issue110-relations", contract=contract,
    )
    assert session.event_contract.exceeded is not None
    assert session.event_contract.exceeded.bound == "relation_rows"
    # 限界以外は予約を除いた枠の中、それに契約の超過の限界の cause（専用の枠）が 1 つ
    assert session.event_contract.contract_cause_published
    assert session.event_contract.relation_rows <= contract.ordinary_relation_rows + 1
    _attribute_pending_limitation(session, pending)
    evidence = connector.finish(session, _legacy_result(), case_id="issue110-relations")
    pilot = evidence.pilot_result
    assert pilot.candidate.decision_receipt.outcome is Outcome.UNKNOWN
    assert len(pilot.reduction.projection.q_open_base) <= contract.max_relation_rows


def test_events_and_payload_bytes_have_contract_bounds(monkeypatch):
    contract = AuthorityEventContract(max_cause_occurrences=64, max_events=10)
    _connector_, session, emitted, _pending = _finished_session(
        monkeypatch, blockers=20, case_id="issue110-events", contract=contract,
    )
    assert session.event_contract.exceeded.bound == "events"
    assert session.event_contract.events <= contract.ordinary_events + 1
    assert session.recorder.event_count == session.event_contract.events
    one = canonical_units_within(_sat_blocker(0), 10**9)
    contract = AuthorityEventContract(max_event_payload_units=one - 1)
    _connector_, session, emitted, _pending = _finished_session(
        monkeypatch, blockers=2, case_id="issue110-payload", contract=contract,
    )
    assert session.event_contract.exceeded.bound == "event_payload_units"
    # 拒んだ event は 1 つも無く、stream は契約の超過の限界の cause だけ
    assert emitted == [0, 0] and session.recorder.event_count == 1
    assert session.event_contract.contract_cause_published


def test_a_refused_transaction_leaves_the_stream_a_valid_prefix(monkeypatch):
    """拒んだ transaction は stream・producer の台帳・Phase 7 の buffer を変えない（部分的な event は無い）。"""

    contract = AuthorityEventContract(max_cause_occurrences=16)
    _connector_, session, emitted, _pending = _finished_session(
        monkeypatch, blockers=40, case_id="issue110-prefix", contract=contract,
    )
    # stream は拒む前の prefix と、超過の時点で publish した契約の超過の限界の cause
    assert session.recorder.event_count == session.event_contract.events == sum(emitted) + 1
    assert session.event_contract.contract_cause_published
    stream_view = session.recorder.prefix_view()
    stream_view.validate()
    assert session.domain_signal_error_kinds == []


def _defer(session, blocker):
    from dataclasses import replace

    from scripts.function_tracer_pcode.authority.lifecycle.production_signals import (
        emit_sat_safety_signal,
        production_signal_scope,
    )

    with production_signal_scope(session):
        return emit_sat_safety_signal(
            replace(blocker, defer_until_terminal=True),
            producer_site_manifest_id="sat-safety-blocker-observed",
        )


def test_a_deferred_occurrence_is_counted_when_it_is_promised(monkeypatch):
    """判定の前に publish すると約束した（遅延した）occurrence は約束の時点で数え、枠を超える約束は拒む。"""

    from scripts.function_tracer_pcode.core.errors import pair_failure_scope

    contract = AuthorityEventContract(max_cause_occurrences=16)
    _connector_, session, emitted, _pending = _finished_session(
        monkeypatch, blockers=5, case_id="issue110-deferred", contract=contract,
    )
    assert session.event_contract.exceeded is None
    with pair_failure_scope(("issue110", "deferred"), session.identity.result_occurrence_id) as ledger:
        for index in range(20):
            _defer(session, _sat_blocker(100 + index))
        assert ledger.pending_failure() is not None
    room = contract.ordinary_cause_occurrences - 5
    assert session.event_contract.deferred_unpublished == room
    assert len(session.domain_signal_state["sat_safety_deferred_observations"]) == room
    assert session.event_contract.exceeded.bound == "cause_occurrences"
    assert session.event_contract.contract_cause_published


def test_a_kept_promise_is_counted_once(monkeypatch):
    """約束した occurrence を後で publish しても 1 回だけ数える（約束と publish の 2 回数えない）。"""

    from scripts.function_tracer_pcode.authority.lifecycle.production_signals import (
        emit_sat_safety_signal,
        production_signal_scope,
    )

    contract = AuthorityEventContract(max_cause_occurrences=16)
    connector, session, emitted, _pending = _finished_session(
        monkeypatch, blockers=0, case_id="issue110-once", contract=contract,
    )
    for index in range(6):
        assert _defer(session, _sat_blocker(index)) == 0
    assert session.event_contract.deferred_unpublished == 6
    with production_signal_scope(session):
        published = [
            emit_sat_safety_signal(_sat_blocker(index), producer_site_manifest_id="sat-safety-blocker-observed")
            for index in range(contract.ordinary_cause_occurrences)
        ]
    # 約束した 6 件は publish で約束の勘定から外れる: 枠いっぱい（12 件）まで publish できる
    assert sum(published) == contract.ordinary_cause_occurrences
    assert session.event_contract.deferred_unpublished == 0
    assert session.event_contract.exceeded is None
    evidence = connector.finish(session, _legacy_result(), case_id="issue110-once")
    assert session.event_contract.exceeded is None
    assert session.event_contract.ordinary_occurrences == contract.ordinary_cause_occurrences
    assert evidence.pilot_result.candidate.decision_receipt.outcome is Outcome.UNKNOWN


def test_a_finish_time_refusal_publishes_the_contract_limitation_before_the_decision(monkeypatch):
    """gate の後（finish の中）で拒まれた event は落とし、判定の前に予約した枠で限界の cause を publish する。"""

    from scripts.function_tracer_pcode.authority.domains.analysis_limitation import (
        ANALYSIS_BUDGET_REASON_ID,
    )

    contract = AuthorityEventContract(max_cause_occurrences=64, max_events=16)
    connector, session, emitted, _pending = _finished_session(
        monkeypatch, blockers=3, case_id="issue110-finish", contract=contract,
    )
    for index in range(20):
        _defer(session, _sat_blocker(1000 + index))
    assert session.event_contract.exceeded is None
    # 遅延した観測は finish の中で publish され、event の数の枠（12 件）を超える（gate の後の超過）
    evidence = connector.finish(session, _legacy_result(), case_id="issue110-finish")
    pilot = evidence.pilot_result
    assert session.event_contract.exceeded.bound == "events"
    assert session.event_contract.limitation_recorded
    assert session.event_contract.deferred_unpublished == 0
    assert pilot.candidate.decision_receipt.outcome is Outcome.UNKNOWN
    assert ANALYSIS_BUDGET_REASON_ID in {row.reason_id for row in pilot.reduction.projection.c_active_base}
    assert session.recorder.event_count <= contract.max_events


def test_the_contract_limitation_cause_is_identified_by_its_site():
    from scripts.function_tracer_pcode.authority import event_contract

    exceeded = AuthorityEventContractExceeded("events", limit=1, observed=2)
    assert exceeded.site == EVENT_CONTRACT_LIMITATION_SITE
    assert exceeded.target_key == ("authority_event_contract", "events")
    assert event_contract._is_limitation_cause(SimpleNamespace(event_type=None)) is False


# ---------------------------------------------------------------------------
# AC-110-S1 / S2: 封印は有限の作業量の中で、実行する前に数える
# ---------------------------------------------------------------------------


def _sealed_inputs(monkeypatch, *, blockers: int = 6, case_id: str = "issue110-seal"):
    connector, session, _emitted, _pending = _finished_session(
        monkeypatch, blockers=blockers, case_id=case_id,
    )
    evidence = connector.finish(session, _legacy_result(), case_id=case_id)
    preimage = {"schema": "issue110-preimage", "note": "x" * 2_000, "rows": list(range(200))}
    return evidence, session, preimage


def _build(evidence, session, preimage, work):
    from scripts.function_tracer_pcode.authority.decision.canonical_result import (
        build_canonical_result_finalization_bundle,
    )

    return build_canonical_result_finalization_bundle(
        result_payload_preimage=preimage, evidence=evidence, session=session, work=work,
    )


EXPECTED_BUILD_STEPS = [
    "pilot_validate", "semantic_projection", "execution_payload_digest", "encode_stream",
    "encode_projection", "encode_receipts", "preimage_digest", "bundle_digest",
    "verify_bundle_digest", "verify_preimage_digest", "decode_stream", "decode_projection",
    "decode_receipts", "verify_replay", "verify_dual_write_replay", "verify_equality",
    "verify_execution_identity", "verify_decisive_provenance", "verify_semantic_projection",
]


def test_the_seal_charges_every_step_once_in_order_before_it_runs(monkeypatch):
    """封印は最初に大きさを測り、表の各段を 1 回ずつ、実行する前に数える（exact-once）。"""

    evidence, session, preimage = _sealed_inputs(monkeypatch)
    charged = []
    original = SealPlan.charge

    def _spy(self, step):
        original(self, step)
        charged.append((step, self.work.consumed))

    monkeypatch.setattr(SealPlan, "charge", _spy)
    work = SealWorkBudget.for_result()
    _build(evidence, session, preimage, work)
    assert [step for step, _ in charged] == EXPECTED_BUILD_STEPS
    consumed = [amount for _, amount in charged]
    assert consumed == sorted(consumed) and consumed[0] > 0


def test_the_seal_work_is_deterministic_and_the_exact_limit_suffices(monkeypatch):
    """同じ入力なら同じ量を数える。ちょうどの上限では作れ、1 単位少なければ部分的な結果なしに止まる。"""

    evidence, session, preimage = _sealed_inputs(monkeypatch)
    first = SealWorkBudget.for_result()
    bundle = _build(evidence, session, preimage, first)
    second = SealWorkBudget.for_result()
    assert _build(evidence, session, preimage, second) == bundle
    assert first.consumed == second.consumed
    exact = SealWorkBudget(first.consumed)
    assert _build(evidence, session, preimage, exact) == bundle
    short = SealWorkBudget(first.consumed - 1)
    with pytest.raises(BundleWorkExceeded) as stopped:
        _build(evidence, session, preimage, short)
    assert stopped.value.kind == "work"
    assert stopped.value.consumed > stopped.value.limit


@pytest.mark.parametrize("failing_step", ["encode_stream", "bundle_digest", "decode_stream", "verify_replay"])
def test_a_step_over_the_budget_never_runs(monkeypatch, failing_step):
    """段の途中（encoder・検証の途中）で上限に達すると、その段の仕事を 1 つも始めない。"""

    from scripts.function_tracer_pcode.authority.decision import canonical_result

    evidence, session, preimage = _sealed_inputs(monkeypatch)
    probe = []
    original = SealPlan.charge

    def _spy(self, step):
        before = self.work.consumed
        original(self, step)
        probe.append((step, before, self.work.consumed))

    monkeypatch.setattr(SealPlan, "charge", _spy)
    _build(evidence, session, preimage, SealWorkBudget.for_result())
    monkeypatch.setattr(SealPlan, "charge", original)
    before_step = next(before for step, before, _after in probe if step == failing_step)
    calls = {"encoded": 0, "loads": 0, "replay": 0}
    real_encoded = canonical_result._encoded

    def _counting_encoded(codec, value):
        calls["encoded"] += 1
        return real_encoded(codec, value)

    from scripts.function_tracer_pcode.authority.codecs import StrictV2JsonCodec
    from scripts.function_tracer_pcode.authority.lifecycle.reducer import ShadowLifecycleReducer

    real_loads = StrictV2JsonCodec.loads
    real_replay = ShadowLifecycleReducer.replay

    def _counting_loads(self, raw):
        calls["loads"] += 1
        return real_loads(self, raw)

    def _counting_replay(self, stream):
        calls["replay"] += 1
        return real_replay(self, stream)

    monkeypatch.setattr(canonical_result, "_encoded", _counting_encoded)
    monkeypatch.setattr(StrictV2JsonCodec, "loads", _counting_loads)
    monkeypatch.setattr(ShadowLifecycleReducer, "replay", _counting_replay)
    work = SealWorkBudget(before_step)
    with pytest.raises(BundleWorkExceeded) as stopped:
        _build(evidence, session, preimage, work)
    assert stopped.value.step == failing_step
    started = {"encode_stream": calls["encoded"], "decode_stream": calls["loads"],
               "verify_replay": calls["replay"]}
    if failing_step in started:
        assert started[failing_step] == 0, calls


def test_a_million_event_stream_stops_before_any_work(monkeypatch):
    """AC-110-S2: 10^6 event の stream は、何も作らずに契約の外として止まる（encode / digest / replay なし）。"""

    from scripts.function_tracer_pcode.authority.decision import canonical_result

    evidence, session, preimage = _sealed_inputs(monkeypatch, case_id="issue110-million")
    bundle = dict(_build(evidence, session, preimage, SealWorkBudget.for_result()))
    stream = dict(bundle["sealed_event_stream"])
    payload = dict(stream["payload"])
    payload["events"] = [payload["events"][0]] * 1_000_000
    stream["payload"] = payload
    bundle["sealed_event_stream"] = stream
    work = SealWorkBudget.for_result()
    started = time.perf_counter()
    with pytest.raises(BundleWorkExceeded) as stopped:
        canonical_result.validate_canonical_result_finalization_bundle(bundle, work=work)
    assert stopped.value.kind == "contract"
    assert time.perf_counter() - started < 1.0
    assert work.consumed == 0
    fake_stream = SimpleNamespace(events=tuple(
        SimpleNamespace(authority_payload={"x": 1}, diagnostic_payload=None) for _ in range(5_000)
    ))
    with pytest.raises(BundleWorkExceeded):
        SealPlan.price(SealWorkBudget.for_result(), stream=fake_stream, projection=None,
                       receipts=(), preimage=None, execution=None)


def test_a_stream_within_the_count_but_over_the_work_stops_while_measuring():
    events = tuple(
        SimpleNamespace(authority_payload={"x": "y" * 10_000}, diagnostic_payload=None) for _ in range(4_000)
    )
    work = SealWorkBudget(50_000)
    with pytest.raises(BundleWorkExceeded) as stopped:
        SealPlan.price(work, stream=SimpleNamespace(events=events), projection=None,
                       receipts=(), preimage=None, execution=None)
    assert stopped.value.kind == "work" and stopped.value.step == "price"
    assert work.consumed <= 50_000 + 20_000


def test_a_huge_event_payload_stops_while_it_is_measured():
    """1 event が大きすぎても、測っている途中で作業量の上限に達して止まる（全体を作らない）。"""

    events = (SimpleNamespace(authority_payload="z" * 50_000_000, diagnostic_payload=None),)
    work = SealWorkBudget(1_000_000)
    started = time.perf_counter()
    with pytest.raises(BundleWorkExceeded) as stopped:
        SealPlan.price(work, stream=SimpleNamespace(events=events),
                       projection=None, receipts=(), preimage=None, execution=None)
    assert stopped.value.kind == "work" and stopped.value.step == "price"
    assert time.perf_counter() - started < 0.5


def test_a_sealed_stream_over_the_contract_is_refused_while_it_is_measured():
    contract = AuthorityEventContract(
        max_stream_payload_units=1 << 10, max_events=8, max_limitation_event_units=64,
        max_terminal_event_units=64, sealed_event_frame_units=64,
    )
    events = tuple(SimpleNamespace(authority_payload="z" * 8_000, diagnostic_payload=None) for _ in range(8))
    with pytest.raises(BundleWorkExceeded) as stopped:
        SealPlan.price(SealWorkBudget.for_result(), stream=SimpleNamespace(events=events),
                       projection=None, receipts=(), preimage=None, execution=None, contract=contract)
    assert stopped.value.kind == "contract"


def test_large_replay_material_and_digest_input_stop_before_the_digest(monkeypatch):
    """大きな preimage（digest の入力）は、digest を始める前に作業量の中で測って止まる。"""

    from scripts.function_tracer_pcode.authority.decision import canonical_result

    evidence, session, _preimage = _sealed_inputs(monkeypatch)
    digests = []
    real_digest = canonical_result.authority_digest
    monkeypatch.setattr(canonical_result, "authority_digest",
                        lambda value: digests.append(1) or real_digest(value))
    huge = {"payload": ["p" * 1000] * 20_000}
    with pytest.raises(BundleWorkExceeded):
        _build(evidence, session, huge, SealWorkBudget(2_000_000))
    assert digests == []


def test_the_validation_of_a_persisted_bundle_is_metered(monkeypatch):
    from scripts.function_tracer_pcode.authority.decision.canonical_result import (
        validate_canonical_result_finalization_bundle,
    )

    evidence, session, preimage = _sealed_inputs(monkeypatch)
    bundle = _build(evidence, session, preimage, SealWorkBudget.for_result())
    work = SealWorkBudget.for_result()
    validate_canonical_result_finalization_bundle(bundle, work=work, result_payload_preimage=preimage)
    assert work.consumed > 0
    with pytest.raises(BundleWorkExceeded):
        validate_canonical_result_finalization_bundle(
            bundle, work=SealWorkBudget(work.consumed // 2), result_payload_preimage=preimage,
        )


def test_the_seal_limit_covers_the_contract_and_is_finite():
    limit = SealWorkBudget.for_result().limit
    assert 0 < limit < 1 << 40
    with pytest.raises(ValueError):
        SealWorkBudget(-1)
    with pytest.raises(TypeError):
        SealPlan.price(object(), stream=SimpleNamespace(events=()), projection=None,
                       receipts=(), preimage=None, execution=None)


# ---------------------------------------------------------------------------
# 静的な guard: 封印の関数は作業量を必ず受け取り、表の段と code の段が一致する
# ---------------------------------------------------------------------------

_METERED_FUNCTIONS = {
    "build_canonical_result_finalization_bundle",
    "validate_canonical_result_finalization_bundle",
    "build_supervisor_canonical_result_finalization_bundle",
    "persist_canonical_result_envelope",
}


def _canonical_result_tree():
    return ast.parse((PACKAGE_ROOT / "authority/decision/canonical_result.py").read_text(encoding="utf-8"))


def test_every_seal_step_in_the_code_is_in_the_cost_model_and_back():
    """code が数える段（`plan.charge("…")`）の集合 = 表の段の集合（表だけ・code だけの段は無い）。"""

    charged = set()
    for node in ast.walk(_canonical_result_tree()):
        if (
            isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute)
            and node.func.attr == "charge" and node.args
            and isinstance(node.args[0], ast.Constant)
        ):
            charged.add(node.args[0].value)
    persist_and_supervisor = {"supervisor_stream_validate", "supervisor_replay"}
    assert charged == set(SEAL_COST_MODEL), sorted(charged ^ set(SEAL_COST_MODEL))
    assert persist_and_supervisor <= charged


def test_seal_functions_take_a_required_keyword_only_work():
    functions = {
        node.name: node for node in _canonical_result_tree().body
        if isinstance(node, ast.FunctionDef) and node.name in _METERED_FUNCTIONS
    }
    assert set(functions) == _METERED_FUNCTIONS
    for name, node in functions.items():
        kwonly = {arg.arg: default for arg, default in zip(node.args.kwonlyargs, node.args.kw_defaults)}
        assert "work" in kwonly and kwonly["work"] is None, name


def test_no_production_call_seals_without_work():
    offenders = []
    for path in PACKAGE_ROOT.rglob("*.py"):
        if "tests" in path.relative_to(PACKAGE_ROOT).parts:
            continue
        tree = ast.parse(path.read_text(encoding="utf-8"))
        for node in ast.walk(tree):
            if not isinstance(node, ast.Call):
                continue
            func = node.func
            name = func.id if isinstance(func, ast.Name) else getattr(func, "attr", None)
            if name in _METERED_FUNCTIONS and not any(k.arg == "work" for k in node.keywords):
                offenders.append(f"{path.relative_to(PACKAGE_ROOT)}:{node.lineno}")
    assert offenders == []


def test_the_contract_numbers_have_one_owner():
    """event の契約の数値は `authority/event_contract` だけに書く（他の module に同じ上限を書かない）。"""

    import re

    fields = (
        "max_cause_occurrences", "max_relation_rows", "max_events", "max_event_payload_units",
        "max_stream_payload_units", "max_projection_units", "max_receipt_units",
        "max_execution_payload_units", "sealed_form_factor", "sealed_event_frame_units",
    )
    definition = re.compile(r"\b(" + "|".join(fields) + r")\s*(:\s*int\s*)?=\s*\d")
    offenders = []
    for path in PACKAGE_ROOT.rglob("*.py"):
        if "tests" in path.relative_to(PACKAGE_ROOT).parts or path.name == "event_contract.py":
            continue
        for line_number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
            if definition.search(line):
                offenders.append(f"{path.relative_to(PACKAGE_ROOT)}:{line_number}")
    assert offenders == []


# ---------------------------------------------------------------------------
# mutation で見つけた穴を塞ぐ test
# ---------------------------------------------------------------------------

_EXPECTED_STEPS_BY_FUNCTION = {
    "build_canonical_result_finalization_bundle": EXPECTED_BUILD_STEPS[:8],
    "build_supervisor_canonical_result_finalization_bundle": [
        "supervisor_stream_validate", "supervisor_replay", "semantic_projection", "encode_stream",
        "encode_projection", "encode_receipts", "preimage_digest", "bundle_digest",
    ],
    "_validate_bundle_with_plan": EXPECTED_BUILD_STEPS[8:14] + [
        "verify_dual_write_replay", "verify_timeout_selection", "verify_equality",
        "verify_execution_identity", "verify_decisive_provenance", "verify_semantic_projection",
    ],
    "persist_canonical_result_envelope": [
        "persist_project", "persist_surface", "persist_seal", "persist_write",
    ],
}


def test_each_seal_function_charges_its_steps_in_order():
    """関数ごとに、数える段の列（code の順）が決まった列と一致する（段を 1 つ外すと落ちる）。"""

    functions = {
        node.name: node for node in _canonical_result_tree().body if isinstance(node, ast.FunctionDef)
    }
    for name, expected in _EXPECTED_STEPS_BY_FUNCTION.items():
        steps = []
        for node in ast.walk(functions[name]):
            if (
                isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute)
                and node.func.attr == "charge" and node.args and isinstance(node.args[0], ast.Constant)
            ):
                steps.append((node.lineno, node.args[0].value))
        assert [step for _line, step in sorted(steps)] == expected, name


def test_pricing_charges_each_event_before_measuring_it():
    # 封印した形の event（header・digest・payload の dict）を 1 つずつ、辿る前に数える: 約 50 event 分の
    # 作業量なら 50 event 目あたりで止まる（残りの event にも reducer の見積もりにも進まない）
    event = {
        "header": {"stream_id": "s" * 40, "sequence_number": 1, "event_type": "CAUSE_OBSERVED",
                   "predecessor_authority_digest": "0" * 64, "authority_payload_digest": "1" * 64},
        "authority_digest": "2" * 64, "authority_payload": {"x": "y" * 400}, "diagnostic_payload": None,
    }
    one = canonical_units_within(event, 10**6)
    stream = {"payload": {"events": [event] * 1_000}}
    work = SealWorkBudget(50 * one)
    with pytest.raises(BundleWorkExceeded) as stopped:
        SealPlan.price(work, stream=stream, projection=None,
                       receipts=(), preimage=None, execution=None)
    assert stopped.value.step == "price"
    assert work.consumed <= 52 * one


@dataclass(frozen=True)
class _Header:
    event_type: Enum


@dataclass(frozen=True)
class _Event:
    header: _Header
    authority_payload: int = 1
    diagnostic_payload: None = None


def _typed_events(kinds):
    from scripts.function_tracer_pcode.authority.lifecycle.stream import EventType

    return tuple(_Event(_Header(EventType(kind))) for kind in kinds)


def test_pricing_charges_the_reduction_by_events_and_the_stream_causes():
    """replay の見積もりは event の数 × stream の cause event の数（最後の `c_active_base` にも projection の
    有無にも依らない: discharge 済みの occurrence も replay は辿る）。封印した形の dict でも同じ。"""

    from scripts.function_tracer_pcode.authority.lifecycle.stream import EventType

    kinds = [EventType.CAUSE_OBSERVED.value] * 40 + [EventType.SOLVER_UNKNOWN.value] * 10
    events = _typed_events(kinds)
    for projection in (None, {"payload": {"c_active_base": []}}):
        plan = SealPlan.price(SealWorkBudget.for_result(), stream=SimpleNamespace(events=events),
                              projection=projection, receipts=(), preimage=None, execution=None)
        assert plan.components.reduction == 50 * 40
    encoded = {"payload": {"events": [{"header": {"event_type": kind}} for kind in kinds]}}
    plan = SealPlan.price(SealWorkBudget.for_result(), stream=encoded, projection=None,
                          receipts=(), preimage=None, execution=None)
    assert plan.components.reduction == 50 * 40
    without_causes = SealPlan.price(
        SealWorkBudget.for_result(), stream=SimpleNamespace(events=_typed_events(kinds[40:])),
        projection=None, receipts=(), preimage=None, execution=None,
    )
    assert without_causes.components.reduction == 10
    # 見積もった replay の仕事は price の中で数える（同じ大きさの stream で cause の数だけが違う）
    same_size = [EventType.SOLVER_UNKNOWN.value] * 50
    assert len(EventType.CAUSE_OBSERVED.value) == len(EventType.SOLVER_UNKNOWN.value)
    with_causes_work, without_causes_work = SealWorkBudget.for_result(), SealWorkBudget.for_result()
    SealPlan.price(with_causes_work, stream=SimpleNamespace(events=events), projection=None,
                   receipts=(), preimage=None, execution=None)
    SealPlan.price(without_causes_work, stream=SimpleNamespace(events=_typed_events(same_size)),
                   projection=None, receipts=(), preimage=None, execution=None)
    assert with_causes_work.consumed - without_causes_work.consumed == 50 * 40 - 50


def test_a_stream_with_more_causes_than_the_contract_is_refused_while_it_is_measured():
    from scripts.function_tracer_pcode.authority.lifecycle.stream import EventType

    contract = AuthorityEventContract(max_cause_occurrences=8)
    events = _typed_events([EventType.CAUSE_OBSERVED.value] * 9)
    with pytest.raises(BundleWorkExceeded) as refused:
        SealPlan.price(SealWorkBudget.for_result(), stream=SimpleNamespace(events=events),
                       projection=None, receipts=(), preimage=None, execution=None, contract=contract)
    assert refused.value.kind == "contract"


def test_measure_more_enforces_the_projection_and_receipt_bounds():
    """replay の後に足す projection / receipt も契約の上限と比べる（encode の前に止まる）。"""

    contract = AuthorityEventContract(max_projection_units=64, max_receipt_units=64)
    fresh = lambda: SealPlan.price(  # noqa: E731
        SealWorkBudget.for_result(), stream=SimpleNamespace(events=()), projection=None,
        receipts=(), preimage=None, execution=None, contract=contract,
    )
    fresh().measure_more(projection={"rows": "x" * 20}, receipts=("y" * 20,))
    with pytest.raises(BundleWorkExceeded) as projection:
        fresh().measure_more(projection={"rows": "x" * 100})
    assert projection.value.kind == "contract"
    with pytest.raises(BundleWorkExceeded) as receipts:
        fresh().measure_more(receipts=("y" * 40, "z" * 40))
    assert receipts.value.kind == "contract"


def test_a_step_cannot_be_charged_twice():
    plan = SealPlan.price(SealWorkBudget.for_result(), stream=SimpleNamespace(events=()), projection=None,
                          receipts=(), preimage=None, execution=None)
    plan.charge("preimage_digest")
    with pytest.raises(ValueError):
        plan.charge("preimage_digest")
    with pytest.raises(KeyError):
        plan.charge("unregistered_step")


@pytest.mark.parametrize("seed", range(20))
def test_the_meter_charges_at_least_what_it_reports(seed):
    rng = random.Random(1000 + seed)
    value = _random_value(rng)
    sink = LimitedUnits(10**9)
    units = measure_canonical_units(value, sink)
    assert sink.consumed >= units


def test_a_refused_oversized_event_keeps_later_events_out(monkeypatch):
    """1 つの event が大きすぎて拒まれたら、後の小さい event も拒む（stream は超過の前の prefix のまま）。"""

    from scripts.function_tracer_pcode.authority.lifecycle.production_signals import (
        SatSafetyBlockerProductionSignal,
        emit_sat_safety_signal,
        production_signal_scope,
    )
    from scripts.function_tracer_pcode.core.errors import pair_failure_scope

    monkeypatch.setenv(NONCE_ENV, "issue110-sticky-occurrence")
    connector = _connector()
    session = connector.begin({"case": "issue110-sticky"})
    small = canonical_units_within(_sat_blocker(0), 10**9)
    session.event_contract = EventContractLedger(AuthorityEventContract(max_event_payload_units=small * 40))
    big = SatSafetyBlockerProductionSignal(
        action="OBSERVED", reason_id="counterexample_analysis_safety_unproven",
        canonical_target_key=("issue110-big", "k" * (small * 60)),
        missing_semantic_fact=("counterexample_safety_gate_unproven", "model"),
        evidence_refs=("issue110-big",), producer_id="sat_unsafety_reason_producer",
    )
    with pair_failure_scope(("issue110", "sticky"), session.identity.result_occurrence_id):
        with production_signal_scope(session):
            first = emit_sat_safety_signal(_sat_blocker(1), producer_site_manifest_id="sat-safety-blocker-observed")
            refused = emit_sat_safety_signal(big, producer_site_manifest_id="sat-safety-blocker-observed")
            later = emit_sat_safety_signal(_sat_blocker(2), producer_site_manifest_id="sat-safety-blocker-observed")
    assert (first, refused, later) == (1, 0, 0)
    assert session.recorder.event_count == 2  # 超過の前の 1 つと契約の超過の限界の cause
    assert session.event_contract.exceeded.bound == "event_payload_units"


def test_a_refused_finish_time_eq_closure_publishes_the_limitation(monkeypatch):
    """finish の中（pending EQ authority の publish）で拒まれても、判定の前に限界の cause を publish する。"""

    from scripts.function_tracer_pcode.authority.contracts import authority_digest
    from scripts.function_tracer_pcode.authority.domains.analysis_limitation import (
        ANALYSIS_BUDGET_REASON_ID,
    )
    from scripts.function_tracer_pcode.authority.lifecycle.execution_authority import (
        PINNED_SOLVER_EXECUTION_ISSUER,
    )
    from scripts.function_tracer_pcode.authority.lifecycle.production_signals import (
        emit_sat_safety_signal,
        issue_pending_eq_closure_authority,
        production_signal_scope,
    )
    from scripts.function_tracer_pcode.checker.checker import EquivalenceChecker
    from scripts.function_tracer_pcode.core.errors import pair_failure_scope
    from scripts.function_tracer_pcode.tests.unit.test_monolithic_region_split import _analysis

    monkeypatch.setenv(NONCE_ENV, "issue110-eq-occurrence")
    connector = _connector()
    session = connector.begin({"case": "issue110-eq"})
    with pair_failure_scope(("issue110", "eq"), session.identity.result_occurrence_id):
        with production_signal_scope(session):
            assert emit_sat_safety_signal(
                _sat_blocker(0), producer_site_manifest_id="sat-safety-blocker-observed",
            ) == 1
            trusted = EquivalenceChecker(
                strategy="monolithic", timeout=5, monolithic_timeout=5, canonical_decision_cutover=False,
            ).check(_analysis("left", 7), _analysis("right", 7))
            frame = trusted._prepared_dispatch_frame
            issue_pending_eq_closure_authority(session, frame.receipt, frame)
    # 分析の後の event 数ちょうどで、finish の event（EQ closure）は ordinary な枠に入らない
    recorded = session.recorder.event_count
    ledger = EventContractLedger(AuthorityEventContract(max_events=recorded + 4))
    ledger.events = session.event_contract.events
    ledger.ordinary_occurrences = session.event_contract.ordinary_occurrences
    ledger.relation_rows = session.event_contract.relation_rows
    ledger.payload_units = session.event_contract.payload_units
    session.event_contract = ledger
    payload = dict(session.execution_payload)
    nonce = payload.pop("result_entry_occurrence_nonce")
    session.result_entry_occurrence_receipt = PINNED_SOLVER_EXECUTION_ISSUER.issue_result_entry_occurrence(
        result_occurrence_id=session.identity.result_occurrence_id,
        execution_payload_digest=authority_digest(payload), startup_receipt_digests=(), occurrence_nonce=nonce,
    )
    evidence = connector.finish(session, _legacy_result(), case_id="issue110-eq")
    pilot = evidence.pilot_result
    assert session.event_contract.exceeded is not None
    assert session.event_contract.limitation_recorded
    assert pilot.candidate.decision_receipt.outcome is Outcome.UNKNOWN
    assert ANALYSIS_BUDGET_REASON_ID in {row.reason_id for row in pilot.reduction.projection.c_active_base}



# ---------------------------------------------------------------------------
# 横断監査（fresh reviewer）で見つけた穴を塞ぐ test
# ---------------------------------------------------------------------------


def test_a_seal_failure_is_a_value_error_and_the_field_check_comes_first():
    """`BundleWorkExceeded` は `ValueError`（永続化した bundle の読み手は無効として扱う）。形の違う bundle は
    数える前に main と同じ `ValueError("fields differ")`。"""

    from scripts.function_tracer_pcode.authority.decision.canonical_result import (
        validate_canonical_result_finalization_bundle,
    )

    assert issubclass(BundleWorkExceeded, ValueError)
    work = SealWorkBudget.for_result()
    malformed = {"sealed_event_stream": {"payload": {"events": [{}] * 5_000}}}
    with pytest.raises(ValueError, match="fields differ") as stopped:
        validate_canonical_result_finalization_bundle(malformed, work=work)
    assert type(stopped.value) is ValueError
    assert work.consumed == 0


@dataclass(frozen=True)
class _SelfAuthority:
    label: str = "self"

    def to_authority_dict(self):
        return self


class _NotADataclass:
    def to_authority_dict(self):  # pragma: no cover - must never be called
        raise AssertionError("an arbitrary projection was called")


def test_the_meter_stops_on_values_that_only_hop():
    """自分を返す射影のように hop だけが続く値も、上限の中で止まる（無限に回らない）。"""

    started = time.perf_counter()
    assert canonical_units_within(_SelfAuthority(), 100_000) is None
    assert time.perf_counter() - started < 1.0


def test_the_meter_calls_only_dataclass_projections():
    """射影を持てるのは dataclass の値だけ（任意の callable・Mock の射影は呼ばずに拒む）。"""

    from unittest.mock import MagicMock

    for value in (_NotADataclass(), MagicMock()):
        with pytest.raises(TypeError, match="must be a dataclass value"):
            canonical_units_within(value, 10**6)


@dataclass(frozen=True)
class _Projected:
    public: str
    _token: object = None

    def to_authority_dict(self):
        return {"public": self.public}


def test_a_projection_is_charged_by_its_structure_before_it_is_called():
    """射影は、その値の公開 field の構造を数えてから呼ぶ（上限の外の値では呼ばない）。"""

    calls = []

    @dataclass(frozen=True)
    class _Counted(_Projected):
        def to_authority_dict(self):
            calls.append(self)
            return super().to_authority_dict()

    big = _Counted("x" * 100_000, object())
    assert canonical_units_within(big, 50_000) is None
    assert calls == []  # 構造だけで上限を超え、射影は呼ばれない
    small = _Counted("y" * 10, object())
    units = canonical_units_within(small, 10_000)
    assert calls == [small]
    # 単位は構造（公開 field だけ。token は数えない）と射影の和で、canonical JSON の byte 以上
    assert units >= _canonical_bytes(small) + len("y" * 10)


@pytest.mark.parametrize("seed", range(30))
def test_the_meter_never_reports_more_than_its_limit(seed):
    rng = random.Random(5000 + seed)
    values = [(-rng.randrange(1, 10**6),) * rng.randrange(1, 400), _random_value(rng), -15, (-1,) * 1000]
    for value in values:
        sink = LimitedUnits(10**9)
        exact = measure_canonical_units(value, sink)
        needed = sink.consumed
        for limit in (0, 1, exact // 2, max(0, exact - 1), exact, needed - 1, needed):
            measured = canonical_units_within(value, max(0, limit))
            assert measured is None or measured <= max(0, limit)
        # 数えた量（報告する単位以上）ちょうどの上限なら測り終える
        assert canonical_units_within(value, needed) == exact


def test_an_earlier_limitation_is_still_attributed_after_the_contract_overflows(monkeypatch):
    """契約を超える前に別の限界（gate の winner）が台帳にあっても、その限界の cause は予約した枠で publish
    でき、pair は登録済みの理由の UNKNOWN（`limitation_unattributed` の ERROR にならない）。"""

    from scripts.function_tracer_pcode.authority.domains.analysis_limitation import (
        ANALYSIS_BUDGET_REASON_ID,
        observe_analysis_limitation,
    )
    from scripts.function_tracer_pcode.authority.lifecycle.production_signals import (
        production_signal_scope,
    )

    contract = AuthorityEventContract(max_cause_occurrences=16)
    connector, session, _emitted, _pending = _finished_session(
        monkeypatch, blockers=40, case_id="issue110-earlier", contract=contract,
    )
    assert session.event_contract.exceeded is not None
    before = session.event_contract.limitation_occurrences
    with production_signal_scope(session):
        observe_analysis_limitation(
            reason_id=ANALYSIS_BUDGET_REASON_ID, limitation_site="checker.checker.EquivalenceChecker.check",
            target_key=("left", "right"), evidence_refs=("issue110-earlier",),
        )
    assert session.event_contract.limitation_occurrences == before + 1
    evidence = connector.finish(session, _legacy_result(), case_id="issue110-earlier")
    assert evidence.pilot_result.candidate.decision_receipt.outcome is Outcome.UNKNOWN


def test_a_stale_admission_is_counted_again_before_publication():
    ledger = EventContractLedger()
    first = ledger.admit(())
    ledger.commit(first)
    stale = ledger.admit(())
    ledger.events += 1
    assert ledger.is_current(stale) is False
    with pytest.raises(ValueError):
        ledger.commit(stale)


def test_recorded_streams_and_envelopes_outside_the_contract_are_refused_before_reading():
    from scripts.function_tracer_pcode.authority.event_contract import require_events_within_contract
    from scripts.function_tracer_pcode.authority.process.canonical_envelope import validate_canonical_envelope
    from scripts.function_tracer_pcode.authority.seal_work import persisted_envelope_byte_limit

    # 封印・検証する stream は worker の stream + supervisor の終端の event まで
    require_events_within_contract(AUTHORITY_EVENT_CONTRACT.max_events + 1)
    require_events_within_contract(AUTHORITY_EVENT_CONTRACT.max_sealed_events)
    with pytest.raises(ValueError):
        require_events_within_contract(AUTHORITY_EVENT_CONTRACT.max_sealed_events + 1)

    class _Huge(bytes):
        def __len__(self):
            return persisted_envelope_byte_limit() + 1

        def decode(self, *args, **kwargs):  # pragma: no cover - must not be read
            raise AssertionError("an oversized envelope was read")

    with pytest.raises(ValueError, match="outside the authority event contract"):
        validate_canonical_envelope(_Huge(b"{}"), launch=None, validate_bundle=None)


def test_the_contract_holds_with_the_phase7_runtime(monkeypatch):
    """production と同じ Phase 7 runtime を持つ session でも、契約の超過は buffer を残さずに止まる。"""

    from scripts.function_tracer_pcode.authority.domains.analysis_limitation import (
        AnalysisLimitationBlockerSignal,
        AnalysisLimitationPilotEncoder,
    )
    from scripts.function_tracer_pcode.authority.domains.sat_safety import SatSafetyPilotEncoder
    from scripts.function_tracer_pcode.authority.lifecycle.pilot import (
        ProductionDualWritePilotConnector,
    )
    from scripts.function_tracer_pcode.authority.lifecycle.production_signals import (
        CompositeProductionSignalEncoder,
        SatSafetyBlockerProductionSignal,
        emit_sat_safety_signal,
        production_signal_scope,
    )
    from scripts.function_tracer_pcode.authority.lifecycle.reducer import ShadowLifecycleReducer
    from scripts.function_tracer_pcode.authority.process.supervisor import (
        PROCESS_DURABLE_REASON_REGISTRY,
        PROCESS_DURABLE_RECOVERY_REGISTRY,
    )
    from scripts.function_tracer_pcode.authority.sites.runtime import runtime_from_audited_manifest
    from scripts.function_tracer_pcode.core.errors import pair_failure_scope

    manifest = json.loads((PACKAGE_ROOT.parents[1] / (
        "artifacts/unknown_taxonomy_v2/phase7/producer-sites.json"
    )).read_text(encoding="utf-8"))
    monkeypatch.setenv(NONCE_ENV, "issue110-phase7-occurrence")
    connector = ProductionDualWritePilotConnector(
        ShadowLifecycleReducer(
            reason_registry=PROCESS_DURABLE_REASON_REGISTRY,
            recovery_registry=PROCESS_DURABLE_RECOVERY_REGISTRY,
        ),
        domain_signal_encoder=CompositeProductionSignalEncoder({
            AnalysisLimitationBlockerSignal: AnalysisLimitationPilotEncoder(),
            SatSafetyBlockerProductionSignal: SatSafetyPilotEncoder(),
        }),
        phase7_runtime_factory=lambda identity: runtime_from_audited_manifest(manifest, identity),
    )
    session = connector.begin({"case": "issue110-phase7"})
    session.event_contract = EventContractLedger(AuthorityEventContract(max_cause_occurrences=16))
    buffered = []
    real_buffer = session.phase7_runtime.buffer_signal_intents

    def _counting_buffer(site_id, signal, intents):
        buffered.append(signal)
        return real_buffer(site_id, signal, intents)

    monkeypatch.setattr(session.phase7_runtime, "buffer_signal_intents", _counting_buffer)
    with pair_failure_scope(("issue110", "phase7"), session.identity.result_occurrence_id):
        with production_signal_scope(session):
            emitted = [
                emit_sat_safety_signal(_sat_blocker(index), producer_site_manifest_id="sat-safety-blocker-observed")
                for index in range(30)
            ]
    assert sum(emitted) == 12 and session.domain_signal_error_kinds == []
    assert session.recorder.event_count == 13  # 12 件と契約の超過の限界の cause
    # 拒んだ signal は Phase 7 の buffer に 1 度も入らない（admission は buffer より前）。入るのは
    # publish した 12 件と契約の超過の限界の cause
    assert len(buffered) == 13


def test_the_stream_frame_and_the_rest_of_the_bundle_are_priced(monkeypatch):
    """event 以外（stream の envelope・bundle の残りの field）も、digest・decode の前に測る。"""

    from scripts.function_tracer_pcode.authority.decision.canonical_result import (
        validate_canonical_result_finalization_bundle,
    )

    stream = {"object_type": "SealedEventStream", "payload": {"envelope": {"note": "e" * 400_000}, "events": []}}
    with pytest.raises(BundleWorkExceeded) as stopped:
        SealPlan.price(SealWorkBudget(100_000), stream=stream, projection=None,
                       receipts=(), preimage=None, execution=None)
    assert stopped.value.step == "price"
    evidence, session, preimage = _sealed_inputs(monkeypatch, case_id="issue110-rest")
    bundle = dict(_build(evidence, session, preimage, SealWorkBudget.for_result()))
    measured = SealWorkBudget.for_result()
    validate_canonical_result_finalization_bundle(dict(bundle), work=measured, result_payload_preimage=preimage)
    bundle["execution_payload_digest"] = "d" * 5_000_000
    with pytest.raises(BundleWorkExceeded) as stopped:
        validate_canonical_result_finalization_bundle(
            bundle, work=SealWorkBudget(measured.consumed), result_payload_preimage=preimage,
        )
    assert stopped.value.step == "price"


def test_supervisor_segments_check_the_event_count_before_validating():
    tree = ast.parse((PACKAGE_ROOT / "authority/process/supervisor.py").read_text(encoding="utf-8"))
    guarded = 0
    for node in ast.walk(tree):
        if isinstance(node, (ast.FunctionDef,)):
            calls = [
                inner for inner in ast.walk(node)
                if isinstance(inner, ast.Call) and isinstance(inner.func, ast.Attribute)
                and inner.func.attr == "validate"
                and isinstance(inner.func.value, ast.Attribute) and inner.func.value.attr == "composite_stream"
            ]
            if not calls:
                continue
            checks = [
                inner for inner in ast.walk(node)
                if isinstance(inner, ast.Call) and getattr(inner.func, "id", None) == "require_events_within_contract"
            ]
            assert checks and min(c.lineno for c in checks) < min(c.lineno for c in calls), node.name
            guarded += 1
    assert guarded == 3


def test_limitation_causes_use_the_reserve_up_to_the_contract_only(monkeypatch):
    """予約した枠の限界の cause も、cause の上限そのものを超えては publish できない。"""

    from scripts.function_tracer_pcode.authority.domains.analysis_limitation import (
        ANALYSIS_BUDGET_REASON_ID,
        observe_analysis_limitation,
    )
    from scripts.function_tracer_pcode.authority.lifecycle.production_signals import (
        production_signal_scope,
    )
    from scripts.function_tracer_pcode.core.errors import pair_failure_scope

    monkeypatch.setenv(NONCE_ENV, "issue110-reserve-occurrence")
    connector = _connector()
    session = connector.begin({"case": "issue110-reserve"})
    session.event_contract = EventContractLedger(AuthorityEventContract(max_cause_occurrences=8))
    with pair_failure_scope(("issue110", "reserve"), session.identity.result_occurrence_id):
        with production_signal_scope(session):
            for index in range(12):
                observe_analysis_limitation(
                    reason_id=ANALYSIS_BUDGET_REASON_ID, limitation_site=f"issue110.site.{index}",
                    target_key=("issue110", index), evidence_refs=(f"issue110-{index}",),
                )
    assert session.event_contract.limitation_occurrences == 8
    assert session.recorder.event_count == 8
    assert session.event_contract.exceeded.bound == "cause_occurrences"


def test_the_stream_total_bound_is_enforced_while_measuring(monkeypatch):
    """stream 全体の上限は、1 event の上限より小さい残りまでしか測らずに止まる。"""

    one = canonical_units_within(_sat_blocker(0), 10**9)
    contract = AuthorityEventContract(
        max_stream_payload_units=one * 3 + 4 * 64 * 1024, max_cause_occurrences=64,
    )
    _connector_, session, emitted, _pending = _finished_session(
        monkeypatch, blockers=10, case_id="issue110-stream", contract=contract,
    )
    assert session.event_contract.exceeded.bound == "stream_payload_units"
    assert session.event_contract.payload_units <= (
        contract.ordinary_stream_payload_units + contract.max_limitation_event_units
    )
    assert sum(emitted) <= 4


# ---------------------------------------------------------------------------
# 契約で切られた stream（truncated regime）: 超過の後の producer の失敗・finish の段・solver の履歴
# ---------------------------------------------------------------------------


def _truncated_session(monkeypatch, case_id: str):
    """契約（cause 16 件）を超えて stream が切られた session（pair の台帳に限界がある）。"""

    contract = AuthorityEventContract(max_cause_occurrences=16)
    connector, session, emitted, pending = _finished_session(
        monkeypatch, blockers=40, case_id=case_id, contract=contract,
    )
    assert session.stream_truncated and pending is not None
    return connector, session, pending


def _shadow_emit(session, index):
    """production の producer（decompilation broker など）の形: emit の失敗を shadow error として記録する。"""

    from scripts.function_tracer_pcode.authority.lifecycle.production_signals import (
        production_signal_scope,
        record_production_pilot_shadow_error,
    )
    from scripts.function_tracer_pcode.authority.lifecycle.stream import (
        CauseObservedEventAuthority,
        EventIntent,
        EventType,
    )

    with production_signal_scope(session):
        try:
            authority = session.domain_signal_encoder.authority_for_signal(session, _sat_blocker(index))
            emitted = session.emit(EventIntent(EventType.CAUSE_OBSERVED, CauseObservedEventAuthority(authority)))
            if emitted != 1:
                raise ValueError("producer event was not recorded")
        except Exception as exc:  # noqa: BLE001 - the production producer's catch
            record_production_pilot_shadow_error(exc)


def test_a_producer_failure_after_the_truncation_is_a_consequence_not_an_error(monkeypatch):
    """超過の後に producer が emit の失敗（や、拒まれた event を前提にした不整合）を shadow error として記録
    しても、pair は契約の限界の UNKNOWN（ERROR にならない）。失敗は診断として残る。"""

    connector, session, pending = _truncated_session(monkeypatch, "issue110-consequence")
    _shadow_emit(session, 5000)
    assert session.domain_signal_error_kinds == []
    assert session.truncation_consequences["AuthorityEventContractExceeded"]["count"] == 1
    assert session.truncation_consequences["AuthorityEventContractExceeded"]["first_detail"]
    _attribute_pending_limitation(session, pending)
    evidence = connector.finish(session, _legacy_result(), case_id="issue110-consequence")
    assert evidence.pilot_result.candidate.decision_receipt.outcome is Outcome.UNKNOWN


def test_a_producer_failure_before_the_truncation_stays_an_error(monkeypatch):
    connector, session, _emitted, _pending = _finished_session(
        monkeypatch, blockers=2, case_id="issue110-real-error",
        contract=AuthorityEventContract(max_cause_occurrences=16),
    )
    from scripts.function_tracer_pcode.authority.lifecycle.production_signals import (
        production_signal_scope,
        record_production_pilot_shadow_error,
    )

    with production_signal_scope(session):
        record_production_pilot_shadow_error(ValueError("a real encoding failure"))
    assert not session.stream_truncated
    assert session.domain_signal_error_kinds == ["ValueError"]
    with pytest.raises(ValueError, match="encoding is incomplete"):
        connector.finish(session, _legacy_result(), case_id="issue110-real-error")


def test_a_rollback_failure_stays_an_error_on_the_overflowing_transaction(monkeypatch):
    """契約で拒んだ transaction の rollback が失敗したら、prefix が producer の状態を表さない: ERROR のまま。"""

    contract = AuthorityEventContract(max_cause_occurrences=16)
    _connector_, session, _emitted, _pending = _finished_session(
        monkeypatch, blockers=contract.ordinary_cause_occurrences, case_id="issue110-rollback",
        contract=contract,
    )
    assert not session.stream_truncated

    def _broken_rollback(_session, _signal):
        raise RuntimeError("rollback broke")

    monkeypatch.setattr(session.domain_signal_encoder, "rollback_emitted_signal", _broken_rollback,
                        raising=False)
    assert session.emit_domain_signal(_sat_blocker(6000)) == 0
    assert session.stream_truncated
    assert session.domain_signal_error_kinds == ["AuthorityEventContractExceeded"]
    assert "rollback broke" in session.domain_signal_error_details[0]


def test_a_signal_after_the_truncation_is_refused_before_it_is_encoded(monkeypatch):
    """切られた stream への（限界以外の）domain signal は encode する前に O(1) で拒む。"""

    _connector_, session, _pending = _truncated_session(monkeypatch, "issue110-before-encoding")
    encoded = []
    real_encoder = session.domain_signal_encoder

    class _Spy:
        def __getattr__(self, name):
            return getattr(real_encoder, name)

        def __call__(self, owner, signal):
            encoded.append(signal)
            return real_encoder(owner, signal)

    session.domain_signal_encoder = _Spy()
    assert session.emit_domain_signal(_sat_blocker(6100)) == 0
    assert encoded == [] and session.domain_signal_error_kinds == []


def test_a_finish_stage_stops_at_its_first_refused_event(monkeypatch):
    """stream を完成させる finish の段は最初に拒まれた event で止まる（拒まれた状態を前提に先へ進まない）。"""

    from scripts.function_tracer_pcode.authority.lifecycle.stream import (
        CauseObservedEventAuthority,
        EventIntent,
        EventType,
    )

    contract = AuthorityEventContract(max_cause_occurrences=16)
    connector, session, _emitted, _pending = _finished_session(
        monkeypatch, blockers=10, case_id="issue110-stage", contract=contract,
    )
    progress = []

    def _history(owner):
        for index in range(5):
            authority = owner.domain_signal_encoder.authority_for_signal(owner, _sat_blocker(7000 + index))
            owner.emit(EventIntent(EventType.CAUSE_OBSERVED, CauseObservedEventAuthority(authority)))
            progress.append(index)

    monkeypatch.setattr(session.domain_signal_encoder, "finalize_open_execution_history", _history,
                        raising=False)
    evidence = connector.finish(session, _legacy_result(), case_id="issue110-stage")
    room = contract.ordinary_cause_occurrences - 10
    assert progress == list(range(room))
    assert session.stream_truncated
    assert evidence.pilot_result.candidate.decision_receipt.outcome is Outcome.UNKNOWN


def test_a_truncated_stream_abandons_its_solver_history(monkeypatch):
    """切られた stream の solver の台帳は stream に束ねずに閉じる: evidence bundle も timeout の束縛も作らない。"""

    from scripts.function_tracer_pcode.authority.domains.call_effect import (
        CALL_EFFECT_PRODUCTION_STAGE_REGISTRY,
    )
    from scripts.function_tracer_pcode.authority.lifecycle.execution_authority import (
        PINNED_SOLVER_EXECUTION_ISSUER,
    )

    connector, session, pending = _truncated_session(monkeypatch, "issue110-abandon")
    result_id = session.identity.result_occurrence_id
    PINNED_SOLVER_EXECUTION_ISSUER._ledger_for(CALL_EFFECT_PRODUCTION_STAGE_REGISTRY, result_id)
    assert PINNED_SOLVER_EXECUTION_ISSUER.has_open_result_ledger(CALL_EFFECT_PRODUCTION_STAGE_REGISTRY, result_id)
    resolved = []
    monkeypatch.setattr(session.domain_signal_encoder, "finalize_terminal_timeout_bindings",
                        lambda *args: resolved.append(args) or (), raising=False)
    _attribute_pending_limitation(session, pending)
    evidence = connector.finish(session, _legacy_result(), case_id="issue110-abandon")
    assert not PINNED_SOLVER_EXECUTION_ISSUER.has_open_result_ledger(
        CALL_EFFECT_PRODUCTION_STAGE_REGISTRY, result_id
    )
    assert resolved == [] and evidence.execution_authority_evidence_bundles == ()
    assert session.domain_signal_state["terminal_timeout_domain_candidate_bindings"] == ()
    assert evidence.pilot_result.candidate.decision_receipt.outcome is Outcome.UNKNOWN
    assert PINNED_SOLVER_EXECUTION_ISSUER.abandon_result_ledgers(result_id) == 0
    with pytest.raises(ValueError, match="only a truncated stream"):
        _connector_, fresh, _emitted, _pending = _finished_session(
            monkeypatch, blockers=1, case_id="issue110-not-truncated",
        )
        fresh.abandon_execution_history()


def test_the_contract_cause_itself_must_be_active_before_the_decision(monkeypatch):
    """別の限界の cause があっても、切られた stream は契約の限界の cause そのものを active に持つ。"""

    from scripts.function_tracer_pcode.authority.domains.analysis_limitation import (
        ANALYSIS_BUDGET_REASON_ID,
        observe_analysis_limitation,
    )
    from scripts.function_tracer_pcode.authority.lifecycle.production_signals import (
        production_signal_scope,
    )

    connector, session, _pending = _truncated_session(monkeypatch, "issue110-own-cause")
    with production_signal_scope(session):
        observe_analysis_limitation(
            reason_id=ANALYSIS_BUDGET_REASON_ID, limitation_site="issue110.other",
            target_key=("issue110", "other"), evidence_refs=("issue110-other",),
        )
    assert session.event_contract.limitation_recorded
    session.ensure_event_contract_limitation()
    active = session.preview_lifecycle_projection().c_active_base
    # 別の限界と契約の限界の 2 つ（別の限界があるだけで契約の cause を省かない）
    assert len([row for row in active if row.reason_id == ANALYSIS_BUDGET_REASON_ID]) == 2
    # 観測した occurrence が active でなければ（discharge 済みなど）判定の前に失敗する
    monkeypatch.setattr(
        "scripts.function_tracer_pcode.authority.domains.analysis_limitation.observe_analysis_limitation",
        lambda **_kw: "not-an-active-occurrence",
    )
    with pytest.raises(ValueError, match="not active"):
        session.ensure_event_contract_limitation()


def test_a_committed_replay_is_not_admitted(monkeypatch):
    """publish しない（commit 済みの）replay は契約に数えない（余分な限界を記録しない）。"""

    contract = AuthorityEventContract(max_cause_occurrences=16)
    _connector_, session, emitted, _pending = _finished_session(
        monkeypatch, blockers=contract.ordinary_cause_occurrences, case_id="issue110-replay",
        contract=contract,
    )
    assert session.event_contract.exceeded is None
    monkeypatch.setattr(session.domain_signal_encoder, "supports_signal_replay",
                        lambda *_a: True, raising=False)
    monkeypatch.setattr(session.domain_signal_encoder, "is_committed_signal_replay",
                        lambda *_a: True, raising=False)
    assert session.emit_domain_signal(_sat_blocker(8000)) == 0
    assert session.event_contract.exceeded is None
    assert session.domain_signal_error_kinds == []


def test_the_envelope_read_never_reads_past_the_contract(monkeypatch, tmp_path):
    """envelope file は上限 + 1 byte より先を読まない。上限の内側の digest は file 全体の sha256（従来と同じ）。"""

    import hashlib

    from scripts.function_tracer_pcode.authority import seal_work
    from scripts.function_tracer_pcode.authority.process.canonical_envelope import (
        EnvelopeOutsideContract,
        read_canonical_envelope,
    )

    monkeypatch.setattr(seal_work, "persisted_envelope_byte_limit", lambda **_kw: 100)
    inside = tmp_path / "inside.json"
    inside.write_bytes(b"x" * 100)
    read = read_canonical_envelope(inside)
    assert read.raw == b"x" * 100 and read.sha256 == hashlib.sha256(b"x" * 100).hexdigest()
    outside = tmp_path / "outside.json"
    outside.write_bytes(b"y" * 10_000_000)
    reads = []
    real_open = open

    class _CountingFile:
        def __init__(self, handle):
            self._handle = handle

        def __enter__(self):
            return self

        def __exit__(self, *exc):
            self._handle.close()

        def read(self, size=-1):
            data = self._handle.read(size)
            reads.append(len(data))
            return data

    monkeypatch.setattr("builtins.open", lambda path, mode="r", *a, **k: _CountingFile(real_open(path, mode, *a, **k)))
    read = read_canonical_envelope(outside)
    assert sum(reads) == 101 and read.raw is None
    assert read.sha256 == hashlib.sha256(b"y" * 101).hexdigest()
    with pytest.raises(EnvelopeOutsideContract):
        read.require_within_contract()


def test_a_completed_promise_releases_its_room(monkeypatch):
    """完了で退いた約束は契約の枠を返す（約束のまま数え続けない）。"""

    from scripts.function_tracer_pcode.authority.lifecycle.production_signals import (
        emit_sat_safety_completion_if_observed,
        emit_sat_safety_signal,
        production_signal_scope,
    )

    contract = AuthorityEventContract(max_cause_occurrences=16)
    _connector_, session, _emitted, _pending = _finished_session(
        monkeypatch, blockers=0, case_id="issue110-release", contract=contract,
    )
    for index in range(6):
        _defer(session, _sat_blocker(index))
    assert session.event_contract.deferred_unpublished == 6
    # 完了の proof artifact は SAT-safety の test が持つ: ここでは完了が約束した occurrence を名指すことだけ作る
    encoder = session.domain_signal_encoder
    real_authority = encoder.authority_for_signal
    monkeypatch.setattr(encoder, "authority_for_signal", lambda owner, signal: real_authority(
        owner, signal.observed if isinstance(signal, SimpleNamespace) else signal,
    ), raising=False)
    with production_signal_scope(session):
        for index in range(6):
            emit_sat_safety_completion_if_observed(
                SimpleNamespace(action="COMPLETED", observed=_sat_blocker(index)),
                producer_site_manifest_id="sat-safety-blocker-completed",
            )
    assert session.event_contract.deferred_unpublished == 0
    with production_signal_scope(session):
        published = [
            emit_sat_safety_signal(_sat_blocker(100 + index), producer_site_manifest_id="sat-safety-blocker-observed")
            for index in range(contract.ordinary_cause_occurrences)
        ]
    assert sum(published) == contract.ordinary_cause_occurrences
    assert session.event_contract.exceeded is None


def test_publishing_a_promise_at_the_edge_counts_it_once(monkeypatch):
    """枠が約束で埋まっていても、約束した occurrence 自身の publish は同じ transaction で 1 回だけ数える。"""

    from scripts.function_tracer_pcode.authority.lifecycle.production_signals import (
        emit_sat_safety_signal,
        production_signal_scope,
    )

    contract = AuthorityEventContract(max_cause_occurrences=16)
    _connector_, session, _emitted, _pending = _finished_session(
        monkeypatch, blockers=0, case_id="issue110-edge", contract=contract,
    )
    room = contract.ordinary_cause_occurrences
    for index in range(room // 2):
        _defer(session, _sat_blocker(index))
    with production_signal_scope(session):
        others = [
            emit_sat_safety_signal(_sat_blocker(100 + index), producer_site_manifest_id="sat-safety-blocker-observed")
            for index in range(room - room // 2)
        ]
        assert sum(others) == room - room // 2
        # 枠はちょうど埋まっている（publish 済み + 約束 = 枠）: 約束した occurrence の publish は通る
        assert emit_sat_safety_signal(_sat_blocker(0), producer_site_manifest_id="sat-safety-blocker-observed") == 1
    assert session.event_contract.exceeded is None
    assert session.event_contract.deferred_unpublished == room // 2 - 1


def test_the_cause_total_includes_the_limitation_causes(monkeypatch):
    """限界の cause が予約より多く publish された後は、限界以外の cause は全体の上限までしか publish できない。"""

    from scripts.function_tracer_pcode.authority.domains.analysis_limitation import (
        ANALYSIS_BUDGET_REASON_ID,
        observe_analysis_limitation,
    )
    from scripts.function_tracer_pcode.authority.lifecycle.production_signals import (
        emit_sat_safety_signal,
        production_signal_scope,
    )
    from scripts.function_tracer_pcode.core.errors import pair_failure_scope

    monkeypatch.setenv(NONCE_ENV, "issue110-total-occurrence")
    contract = AuthorityEventContract(max_cause_occurrences=16)
    connector = _connector()
    session = connector.begin({"case": "issue110-total"})
    session.event_contract = EventContractLedger(contract)
    with pair_failure_scope(("issue110", "total"), session.identity.result_occurrence_id):
        with production_signal_scope(session):
            for index in range(8):
                observe_analysis_limitation(
                    reason_id=ANALYSIS_BUDGET_REASON_ID, limitation_site=f"issue110.total.{index}",
                    target_key=("issue110-total", index), evidence_refs=(f"issue110-total-{index}",),
                )
            published = [
                emit_sat_safety_signal(_sat_blocker(index), producer_site_manifest_id="sat-safety-blocker-observed")
                for index in range(contract.ordinary_cause_occurrences)
            ]
    # 限界以外は、全体の上限から契約の超過の専用の枠と先に publish した限界を除いた分まで
    assert sum(published) == contract.max_cause_occurrences - 1 - 8
    assert session.event_contract.exceeded.bound == "cause_occurrences"
    # 超過の限界の cause は専用の枠で必ず publish できる（全体はちょうど上限）
    assert session.event_contract.contract_cause_published
    assert session.event_contract.limitation_occurrences == 8 + 1
    assert (session.event_contract.ordinary_occurrences
            + session.event_contract.limitation_occurrences) == contract.max_cause_occurrences


def test_the_first_overflow_is_the_one_kept_and_recorded():
    """最初の超過が stream を切った点: 後の超過（予約の枠の超過など）で上書きしない。"""

    ledger = EventContractLedger(AuthorityEventContract(max_cause_occurrences=16))
    for bound in ("events", "cause_occurrences"):
        with pytest.raises(AuthorityEventContractExceeded):
            ledger._exceed(bound, 1, 2)
    assert ledger.exceeded.bound == "events"


def test_every_envelope_read_goes_through_the_bounded_reader():
    """`RESULT_ENVELOPE` の path を持つ変数は `read_canonical_envelope` だけが読む（file 全体を読む呼び出しに渡さない）。"""

    whole_file_reads = {"read_bytes", "read_text", "open"}
    offenders = []
    checked = 0
    for path in sorted((PACKAGE_ROOT / "authority").rglob("*.py")):
        tree = ast.parse(path.read_text(encoding="utf-8"))
        for node in ast.walk(tree):
            if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                continue
            envelope_paths = {
                target.id
                for sub in ast.walk(node) if isinstance(sub, ast.Assign)
                for target in sub.targets if isinstance(target, ast.Name)
                if any(isinstance(item, ast.Attribute) and item.attr == "RESULT_ENVELOPE"
                       for item in ast.walk(sub.value))
            }
            for sub in ast.walk(node):
                if not isinstance(sub, ast.Call):
                    continue
                func = sub.func
                receiver = func.value.id if isinstance(func, ast.Attribute) and isinstance(func.value, ast.Name) else None
                name = func.attr if isinstance(func, ast.Attribute) else getattr(func, "id", None)
                arguments = {arg.id for arg in sub.args if isinstance(arg, ast.Name)}
                if name in whole_file_reads and (receiver in envelope_paths or arguments & envelope_paths):
                    offenders.append(f"{path.relative_to(PACKAGE_ROOT)}:{node.name}:{sub.lineno} {name}")
                if name == "read_canonical_envelope" and arguments & envelope_paths:
                    checked += 1
    assert offenders == [], offenders
    assert checked == 3  # 終端の snapshot・checkpoint の診断・child 終了の観測


def test_a_truncated_stream_is_not_completed_at_finish(monkeypatch):
    """gate の前に切られた stream では、finish の stream を完成させる段（solver の履歴など）を走らせない。

    段は拒まれた event を前提にしうる（ABI/width の completion が「live な C_active の行が無い」で
    失敗したのが実測）: 走らせれば ERROR になる。"""

    connector, session, pending = _truncated_session(monkeypatch, "issue110-not-completed")
    ran = []

    def _inconsistent_history(owner):
        ran.append(owner)
        raise ValueError("completion artifact does not bind one live C_active row")

    monkeypatch.setattr(session.domain_signal_encoder, "finalize_open_execution_history",
                        _inconsistent_history, raising=False)
    _attribute_pending_limitation(session, pending)
    evidence = connector.finish(session, _legacy_result(), case_id="issue110-not-completed")
    assert ran == []
    assert evidence.pilot_result.candidate.decision_receipt.outcome is Outcome.UNKNOWN


def test_a_pending_eq_of_a_truncated_stream_does_not_block_the_seal(monkeypatch):
    """切られた stream の pending EQ は決まらない（限界の cause が EQ を止める）: seal を止める ERROR にしない。"""

    connector, session, pending = _truncated_session(monkeypatch, "issue110-pending-eq")
    session.domain_signal_state["pending_eq_authorities"] = {"issue110-nonce": {"state": "PENDING"}}
    monkeypatch.setattr(
        "scripts.function_tracer_pcode.authority.lifecycle.production_signals.finalize_pending_eq_authorities",
        lambda *_a: pytest.fail("a truncated stream does not finalize pending EQ"),
    )
    _attribute_pending_limitation(session, pending)
    evidence = connector.finish(session, _legacy_result(), case_id="issue110-pending-eq")
    assert evidence.pilot_result.candidate.decision_receipt.outcome is Outcome.UNKNOWN


# ---------------------------------------------------------------------------
# 3 回目の review（fresh reviewer）で見つけた穴を塞ぐ test
# ---------------------------------------------------------------------------


def test_other_limitations_cannot_take_the_contract_causes_slot(monkeypatch):
    """他の限界の cause が予約を使い切っても、契約の超過の限界の cause は専用の枠で publish でき、
    pair は登録済みの理由の UNKNOWN（`finish` の ERROR にならない）。"""

    from scripts.function_tracer_pcode.authority.domains.analysis_limitation import (
        ANALYSIS_BUDGET_REASON_ID,
        observe_analysis_limitation,
    )
    from scripts.function_tracer_pcode.authority.lifecycle.production_signals import (
        emit_sat_safety_signal,
        production_signal_scope,
    )
    from scripts.function_tracer_pcode.core.errors import pair_failure_scope

    contract = AuthorityEventContract(max_cause_occurrences=16)
    connector, session, _emitted, _pending = _finished_session(
        monkeypatch, blockers=contract.ordinary_cause_occurrences, case_id="issue110-slot",
        contract=contract,
    )
    with pair_failure_scope(("issue110", "slot"), session.identity.result_occurrence_id):
        with production_signal_scope(session):
            for index in range(contract.limitation_reserve_occurrences):
                observe_analysis_limitation(
                    reason_id=ANALYSIS_BUDGET_REASON_ID, limitation_site=f"issue110.slot.{index}",
                    target_key=("issue110-slot", index), evidence_refs=(f"issue110-slot-{index}",),
                )
            assert emit_sat_safety_signal(
                _sat_blocker(9000), producer_site_manifest_id="sat-safety-blocker-observed",
            ) == 0
    # 共有の予約は 1 枠少なく（最後の限界で超過）、専用の枠は契約の超過の限界の cause が使った
    assert session.event_contract.limitation_occurrences == contract.limitation_reserve_occurrences
    assert session.event_contract.contract_cause_published
    evidence = connector.finish(session, _legacy_result(), case_id="issue110-slot")
    pilot = evidence.pilot_result
    assert pilot.candidate.decision_receipt.outcome is Outcome.UNKNOWN
    assert len(pilot.reduction.projection.c_active_base) == contract.max_cause_occurrences


def test_an_unpublishable_limitation_is_attributed_to_the_truncation(monkeypatch):
    """切られた stream で限界そのものを publish できないとき、pair の gate の帰属は契約の超過の限界の
    cause（active）へ向く（`limitation_unattributed` の ERROR にしない）。切られていなければ今までどおり。"""

    from scripts.function_tracer_pcode.authority.decision import limitation_attribution as la
    from scripts.function_tracer_pcode.authority.domains.analysis_limitation import (
        ANALYSIS_BUDGET_REASON_ID,
    )
    from scripts.function_tracer_pcode.core.errors import AnalysisLimitation

    connector, session, _pending = _truncated_session(monkeypatch, "issue110-attribution")
    winner = AnalysisLimitation(
        ANALYSIS_BUDGET_REASON_ID, "an earlier budget", site="issue110.winner",
        target_key=("issue110-winner",), evidence_refs=("issue110-winner",),
    )
    # 共有の予約を使い切った状態を作る（勝者の限界の cause は拒まれる）
    session.event_contract.limitation_occurrences = session.event_contract.contract.max_cause_occurrences
    attribution = la.attribute_analysis_limitation(session, winner)
    assert attribution.disposition == la.ATTRIBUTED_TRUNCATED_STREAM
    assert attribution.is_attributed and attribution.decision_effect == "blocks_decision"
    active = {row.occurrence_id for row in session.preview_lifecycle_projection().c_active_base}
    assert attribution.occurrence_id in active

    _connector2, fresh, _emitted, _pending2 = _finished_session(
        monkeypatch, blockers=1, case_id="issue110-attribution-bounds",
    )
    monkeypatch.setattr(la, "observe_analysis_limitation", lambda **_kw: None)
    assert la.attribute_analysis_limitation(fresh, winner).disposition == la.UNATTRIBUTED


def test_a_supervisor_composite_of_a_full_worker_stream_can_be_sealed():
    """worker の stream が上限ちょうどでも、supervisor の終端の event を足した composite は封印できる。"""

    from scripts.function_tracer_pcode.authority.lifecycle.stream import EventType

    contract = AuthorityEventContract(max_events=8)
    composite = _typed_events([EventType.SOLVER_UNKNOWN.value] * contract.max_events
                              + [EventType.PROCESS_TIMEOUT.value])
    assert len(composite) == contract.max_sealed_events
    SealPlan.price(SealWorkBudget.for_supervisor(contract), stream=SimpleNamespace(events=composite),
                   projection=None, receipts=(), preimage=None, execution=None, contract=contract)
    with pytest.raises(BundleWorkExceeded):
        SealPlan.price(SealWorkBudget.for_supervisor(contract),
                       stream=SimpleNamespace(events=composite + composite[-1:]),
                       projection=None, receipts=(), preimage=None, execution=None, contract=contract)
    assert SealWorkBudget.for_supervisor(contract).preimage_limit == contract.max_supervisor_preimage_units


def test_a_preimage_over_its_bound_stops_while_it_is_measured(monkeypatch):
    """preimage は封印の上限まで数えながら測り、超えた時点で止まる（大きい文字列を escape して書かない）。"""

    from scripts.function_tracer_pcode.authority import canonical_units

    encoded = []
    real_encode = canonical_units._ENCODE_STRING
    monkeypatch.setattr(canonical_units, "_ENCODE_STRING",
                        lambda text: encoded.append(len(text)) or real_encode(text))
    work = SealWorkBudget.for_seal(preimage_units=1_000)
    with pytest.raises(BundleWorkExceeded) as refused:
        SealPlan.price(work, stream=SimpleNamespace(events=()), projection=None, receipts=(),
                       preimage={"note": "p" * 10_000_000}, execution=None)
    assert refused.value.kind == "contract"
    assert max(encoded, default=0) < 1_000


def test_the_writer_never_writes_an_envelope_its_reader_rejects(monkeypatch, tmp_path):
    from scripts.function_tracer_pcode.authority.decision import canonical_result

    evidence, session, preimage = _sealed_inputs(monkeypatch, case_id="issue110-writer")
    bundle = _build(evidence, session, preimage, SealWorkBudget.for_result())
    monkeypatch.setenv("UNKNOWN_TAXONOMY_V2_SUPERVISOR_ROOT", str(tmp_path))
    monkeypatch.setenv("UNKNOWN_TAXONOMY_V2_EXECUTION_NONCE", "issue110-writer")
    payload = {**preimage, "canonical_result_finalization_bundle": bundle}
    path = canonical_result.persist_canonical_result_envelope(payload, work=SealWorkBudget.for_result())
    written = path.stat().st_size
    path.unlink()
    monkeypatch.setattr(canonical_result, "persisted_envelope_byte_limit", lambda: written - 1)
    with pytest.raises(BundleWorkExceeded) as refused:
        canonical_result.persist_canonical_result_envelope(payload, work=SealWorkBudget.for_result())
    assert refused.value.kind == "contract" and refused.value.step == "persist_write"
    assert not path.exists() and list(path.parent.iterdir()) == []


def test_the_seal_checks_exactly_the_parts_the_reader_measures(monkeypatch):
    """封印は digest の前に、読む側が測る encode した形を同じ上限で確かめる（大きさが読む側と一致）。"""

    from scripts.function_tracer_pcode.authority.decision import canonical_result

    evidence, session, preimage = _sealed_inputs(monkeypatch, case_id="issue110-parts")
    checked = []
    real = SealPlan.check_sealed_form

    def _spy(plan, **parts):
        checked.append(parts)
        return real(plan, **parts)

    monkeypatch.setattr(SealPlan, "check_sealed_form", _spy)
    bundle = _build(evidence, session, preimage, SealWorkBudget.for_result())
    assert len(checked) == 1
    read = canonical_result._bundle_parts(bundle)
    for name in ("stream", "projection", "receipts", "execution"):
        assert canonical_units_within(checked[0][name], 10**9) == canonical_units_within(read[name], 10**9)


def test_a_replay_without_its_audited_site_stays_an_error(monkeypatch):
    """commit 済みの replay の近道は、Phase 7 の監査済みの場所の確認より後（場所の無い signal は ERROR）。"""

    from scripts.function_tracer_pcode.authority.sites.runtime import runtime_from_audited_manifest

    manifest = json.loads((PACKAGE_ROOT.parents[1] / (
        "artifacts/unknown_taxonomy_v2/phase7/producer-sites.json"
    )).read_text(encoding="utf-8"))
    monkeypatch.setenv(NONCE_ENV, "issue110-replay-site-occurrence")
    connector = _connector()
    session = connector.begin({"case": "issue110-replay-site"})
    session.phase7_runtime = runtime_from_audited_manifest(manifest, session.identity)
    monkeypatch.setattr(session.domain_signal_encoder, "supports_signal_replay", lambda *_a: True,
                        raising=False)
    monkeypatch.setattr(session.domain_signal_encoder, "is_committed_signal_replay", lambda *_a: True,
                        raising=False)
    assert session.emit_domain_signal(_sat_blocker(9100)) == 0
    assert session.domain_signal_error_kinds == ["ValueError"]
    assert "audited pre-emission site" in session.domain_signal_error_details[0]


def test_a_failed_publication_leaves_the_contract_uncounted(monkeypatch):
    """publish の直前の callback が失敗したら、契約の勘定は数える前に戻る（数えたのに publish しない、が無い）。"""

    from scripts.function_tracer_pcode.authority.lifecycle.stream import (
        CauseObservedEventAuthority,
        EventIntent,
        EventType,
    )

    _connector_, session, _emitted, _pending = _finished_session(
        monkeypatch, blockers=2, case_id="issue110-undo",
    )
    before = session.event_contract._state()
    events_before = session.recorder.event_count
    authority = session.domain_signal_encoder.authority_for_signal(session, _sat_blocker(9200))
    intent = EventIntent(EventType.CAUSE_OBSERVED, CauseObservedEventAuthority(authority))

    def _failing_commit():
        raise RuntimeError("producer commit failed")

    with pytest.raises(RuntimeError, match="producer commit failed"):
        session.emit_many((intent,), _failing_commit)
    assert session.event_contract._state() == before
    assert session.recorder.event_count == events_before
    assert authority.occurrence.occurrence_id not in session.event_contract._published_ids
    assert session.emit(intent) == events_before + 1


def _eq_session(monkeypatch, case_id: str, contract=None):
    """EQ の closure（pending EQ authority）だけを持つ session（blocker は無い）。"""

    from scripts.function_tracer_pcode.authority.contracts import authority_digest
    from scripts.function_tracer_pcode.authority.lifecycle.execution_authority import (
        PINNED_SOLVER_EXECUTION_ISSUER,
    )
    from scripts.function_tracer_pcode.authority.lifecycle.production_signals import (
        issue_pending_eq_closure_authority,
        production_signal_scope,
    )
    from scripts.function_tracer_pcode.checker.checker import EquivalenceChecker
    from scripts.function_tracer_pcode.core.errors import pair_failure_scope
    from scripts.function_tracer_pcode.tests.unit.test_monolithic_region_split import _analysis

    monkeypatch.setenv(NONCE_ENV, f"{case_id}-occurrence")
    connector = _connector()
    session = connector.begin({"case": case_id})
    if contract is not None:
        session.event_contract = EventContractLedger(contract)
    with pair_failure_scope(("issue110", case_id), session.identity.result_occurrence_id):
        with production_signal_scope(session):
            trusted = EquivalenceChecker(
                strategy="monolithic", timeout=5, monolithic_timeout=5, canonical_decision_cutover=False,
            ).check(_analysis("left", 7), _analysis("right", 7))
            frame = trusted._prepared_dispatch_frame
            issue_pending_eq_closure_authority(session, frame.receipt, frame)
    payload = dict(session.execution_payload)
    nonce = payload.pop("result_entry_occurrence_nonce")
    session.result_entry_occurrence_receipt = PINNED_SOLVER_EXECUTION_ISSUER.issue_result_entry_occurrence(
        result_occurrence_id=session.identity.result_occurrence_id,
        execution_payload_digest=authority_digest(payload), startup_receipt_digests=(), occurrence_nonce=nonce,
    )
    return connector, session


def test_an_eq_pair_truncated_before_its_closure_is_unknown(monkeypatch):
    """契約が無ければ EQUIVALENT の pair（legacy も EQ）も、切られた stream では UNKNOWN（EQ を通さない）。"""

    connector, session = _eq_session(monkeypatch, "issue110-eq-control")
    control = connector.finish(session, _legacy_result(is_equivalent=True), case_id="issue110-eq-control")
    assert control.pilot_result.candidate.decision_receipt.outcome is Outcome.EQUIVALENT
    closure_units = session.event_contract.payload_units  # finish が publish する EQ closure の大きさ
    assert closure_units > 1
    reserve = AUTHORITY_EVENT_CONTRACT.limitation_reserve_occurrences * (
        AUTHORITY_EVENT_CONTRACT.max_limitation_event_units
    )
    connector, session = _eq_session(
        monkeypatch, "issue110-eq-truncated",
        contract=AuthorityEventContract(max_stream_payload_units=reserve + closure_units - 1),
    )
    evidence = connector.finish(session, _legacy_result(is_equivalent=True), case_id="issue110-eq-truncated")
    assert session.stream_truncated
    assert evidence.pilot_result.candidate.decision_receipt.outcome is Outcome.UNKNOWN


def test_the_contract_numbers_have_no_second_home():
    """契約の数値（と派生の上限）は `authority/event_contract` の外に literal で書かない。

    契約を使う module（`event_contract` / `seal_work` を import する module）には契約のどの値も、他の
    authority の module には契約に固有の大きい値（64 Ki 以上）も書かない。
    """

    from dataclasses import fields as dataclass_fields

    contract = AUTHORITY_EVENT_CONTRACT
    values = {getattr(contract, field.name) for field in dataclass_fields(contract)}
    values |= {
        contract.max_sealed_events, contract.max_sealed_stream_units,
        contract.ordinary_cause_occurrences, contract.ordinary_relation_rows,
        contract.ordinary_events, contract.ordinary_stream_payload_units,
    }
    consumers = ("authority.event_contract", "authority.seal_work")
    offenders = []
    for path in sorted((PACKAGE_ROOT / "authority").rglob("*.py")):
        if path.name == "event_contract.py":
            continue
        tree = ast.parse(path.read_text(encoding="utf-8"))
        imported = {
            node.module for node in ast.walk(tree)
            if isinstance(node, ast.ImportFrom) and node.module
        }
        consumer = any(name.endswith(consumers) for name in imported)
        floor = 256 if consumer else 64 << 10
        for node in ast.walk(tree):
            value = None
            if isinstance(node, ast.BinOp) and isinstance(node.op, ast.LShift) and all(
                isinstance(side, ast.Constant) for side in (node.left, node.right)
            ):
                value = node.left.value << node.right.value
            elif isinstance(node, ast.Constant) and type(node.value) is int:
                value = node.value
            if value is not None and value >= floor and value in values:
                offenders.append(f"{path.relative_to(PACKAGE_ROOT)}:{node.lineno} {value}")
    assert offenders == [], offenders


def test_a_limitation_event_is_measured_against_the_limitation_bound(monkeypatch):
    """限界の cause の event は予約した大きさ（`max_limitation_event_units`）までしか publish できない。"""

    from scripts.function_tracer_pcode.authority.domains.analysis_limitation import (
        ANALYSIS_BUDGET_REASON_ID,
        observe_analysis_limitation,
    )
    from scripts.function_tracer_pcode.authority.lifecycle.production_signals import (
        production_signal_scope,
    )

    contract = AuthorityEventContract(max_limitation_event_units=8 << 10)
    _connector_, session, _emitted, _pending = _finished_session(
        monkeypatch, blockers=1, case_id="issue110-limitation-size", contract=contract,
    )
    with production_signal_scope(session):
        observe_analysis_limitation(
            reason_id=ANALYSIS_BUDGET_REASON_ID, limitation_site="issue110.size",
            target_key=("issue110-size", "t" * (16 << 10)), evidence_refs=("issue110-size",),
        )
    assert session.event_contract.exceeded.bound == "event_payload_units"
    assert session.event_contract.exceeded.limit == contract.max_limitation_event_units


def test_a_truncated_stream_takes_no_new_promise_without_building_its_authority(monkeypatch):
    _connector_, session, _pending = _truncated_session(monkeypatch, "issue110-no-promise")
    built = []
    real_authority = session.domain_signal_encoder.authority_for_signal
    monkeypatch.setattr(session.domain_signal_encoder, "authority_for_signal",
                        lambda owner, signal: built.append(signal) or real_authority(owner, signal),
                        raising=False)
    assert _defer(session, _sat_blocker(9300)) == 0
    assert built == [] and session.event_contract.deferred_unpublished == 0


def test_a_promise_counts_against_the_total_with_the_limitation_causes(monkeypatch):
    """約束も全体の上限（限界の cause と契約の超過の専用の枠を含む）で数える。"""

    from scripts.function_tracer_pcode.authority.domains.analysis_limitation import (
        ANALYSIS_BUDGET_REASON_ID,
        observe_analysis_limitation,
    )
    from scripts.function_tracer_pcode.authority.lifecycle.production_signals import (
        production_signal_scope,
    )

    contract = AuthorityEventContract(max_cause_occurrences=16)
    _connector_, session, _emitted, _pending = _finished_session(
        monkeypatch, blockers=0, case_id="issue110-promise-total", contract=contract,
    )
    limitations = 5  # 共有の予約（3）より多い: 全体の上限が予約を除く枠より先に効く
    with production_signal_scope(session):
        for index in range(limitations):
            observe_analysis_limitation(
                reason_id=ANALYSIS_BUDGET_REASON_ID, limitation_site=f"issue110.pt.{index}",
                target_key=("issue110-pt", index), evidence_refs=(f"issue110-pt-{index}",),
            )
    assert session.event_contract.limitation_occurrences == limitations
    for index in range(20):
        _defer(session, _sat_blocker(9400 + index))
    # 全体 16 から専用の枠 1 と限界 5 を除いた 10（予約を除く枠 12 より小さい）
    expected = contract.max_cause_occurrences - 1 - limitations
    assert expected < contract.ordinary_cause_occurrences
    assert session.event_contract.deferred_unpublished == expected


def test_a_direct_emit_overflow_publishes_the_contract_cause_at_once(monkeypatch):
    from scripts.function_tracer_pcode.authority.lifecycle.production_signals import (
        production_signal_scope,
    )
    from scripts.function_tracer_pcode.authority.lifecycle.stream import (
        CauseObservedEventAuthority,
        EventIntent,
        EventType,
    )
    from scripts.function_tracer_pcode.core.errors import pair_failure_scope

    contract = AuthorityEventContract(max_cause_occurrences=16)
    _connector_, session, _emitted, _pending = _finished_session(
        monkeypatch, blockers=contract.ordinary_cause_occurrences, case_id="issue110-direct",
        contract=contract,
    )
    authority = session.domain_signal_encoder.authority_for_signal(session, _sat_blocker(9500))
    with pair_failure_scope(("issue110", "direct"), session.identity.result_occurrence_id):
        with production_signal_scope(session):
            with pytest.raises(AuthorityEventContractExceeded):
                session.emit(EventIntent(EventType.CAUSE_OBSERVED, CauseObservedEventAuthority(authority)))
    assert session.event_contract.contract_cause_published


def test_a_refused_contract_cause_does_not_recurse_and_fails_closed(monkeypatch):
    """契約の超過の限界の cause そのものが拒まれても（契約の設定の誤り）、再帰せず、判定の前に止まる。"""

    contract = AuthorityEventContract(max_cause_occurrences=16, max_limitation_event_units=1)
    connector, session, _emitted, _pending = _finished_session(
        monkeypatch, blockers=30, case_id="issue110-no-recursion", contract=contract,
    )
    assert session.stream_truncated and not session.event_contract.contract_cause_published
    with pytest.raises(ValueError, match="not active"):
        session.ensure_event_contract_limitation()


def test_every_bundle_builder_checks_the_sealed_form_before_its_digest():
    """bundle を作る関数はどれも、`bundle_digest` を数える直前に encode した形を確かめる。"""

    tree = _canonical_result_tree()
    builders = 0
    for node in ast.walk(tree):
        if not isinstance(node, ast.FunctionDef):
            continue
        order = []
        for sub in ast.walk(node):
            if isinstance(sub, ast.Call):
                name = sub.func.attr if isinstance(sub.func, ast.Attribute) else getattr(sub.func, "id", None)
                if name == "_check_sealed_form":
                    order.append(("check", sub.lineno))
                if name == "charge" and sub.args and isinstance(sub.args[0], ast.Constant) \
                        and sub.args[0].value == "bundle_digest":
                    order.append(("digest", sub.lineno))
        if any(kind == "digest" for kind, _ in order):
            builders += 1
            kinds = [kind for kind, _ in sorted(order, key=lambda item: item[1])]
            assert kinds == ["check", "digest"], (node.name, kinds)
    assert builders == 2


@pytest.mark.parametrize("part", ["projection", "receipts", "execution"])
def test_each_sealed_part_stops_at_its_contract_bound(part):
    """projection・receipt・execution payload は、それぞれの上限まで数えながら測って止まる。"""

    contract = AuthorityEventContract(
        max_projection_units=1 << 10, max_receipt_units=1 << 10, max_execution_payload_units=1 << 10,
    )
    big = {"rows": "r" * 5_000}
    parts = dict(projection=None, receipts=(), execution=None)
    parts[part] = (big,) if part == "receipts" else big
    with pytest.raises(BundleWorkExceeded) as refused:
        SealPlan.price(SealWorkBudget.for_result(), stream=SimpleNamespace(events=()), preimage=None,
                       contract=contract, **parts)
    assert refused.value.kind == "contract"


def test_a_direct_emit_after_an_overflow_is_refused_even_within_bounds(monkeypatch):
    """超過は sticky: 1 つの大きい event で超えた後は、上限の内側の小さい直接の emit も拒む。"""

    from scripts.function_tracer_pcode.authority.lifecycle.production_signals import (
        SatSafetyBlockerProductionSignal,
        production_signal_scope,
    )
    from scripts.function_tracer_pcode.authority.lifecycle.stream import (
        CauseObservedEventAuthority,
        EventIntent,
        EventType,
    )
    from scripts.function_tracer_pcode.core.errors import pair_failure_scope

    monkeypatch.setenv(NONCE_ENV, "issue110-direct-sticky-occurrence")
    connector = _connector()
    session = connector.begin({"case": "issue110-direct-sticky"})
    small = canonical_units_within(_sat_blocker(0), 10**9)
    session.event_contract = EventContractLedger(AuthorityEventContract(max_event_payload_units=small * 40))
    big = SatSafetyBlockerProductionSignal(
        action="OBSERVED", reason_id="counterexample_analysis_safety_unproven",
        canonical_target_key=("issue110-direct-big", "k" * (small * 60)),
        missing_semantic_fact=("counterexample_safety_gate_unproven", "model"),
        evidence_refs=("issue110-direct-big",), producer_id="sat_unsafety_reason_producer",
    )

    def _intent(signal):
        authority = session.domain_signal_encoder.authority_for_signal(session, signal)
        return EventIntent(EventType.CAUSE_OBSERVED, CauseObservedEventAuthority(authority))

    with pair_failure_scope(("issue110", "direct-sticky"), session.identity.result_occurrence_id):
        with production_signal_scope(session):
            with pytest.raises(AuthorityEventContractExceeded):
                session.emit(_intent(big))
            count = session.recorder.event_count
            with pytest.raises(AuthorityEventContractExceeded):
                session.emit(_intent(_sat_blocker(1)))
    assert session.recorder.event_count == count


def test_finish_fails_closed_when_the_contract_cause_was_never_published(monkeypatch):
    """超過の時点の publish が失敗していても、判定の前の確認が止める（切られた stream を判定しない）。"""

    connector, session = _eq_session(monkeypatch, "issue110-unpublished")
    reserve = AUTHORITY_EVENT_CONTRACT.limitation_reserve_occurrences * (
        AUTHORITY_EVENT_CONTRACT.max_limitation_event_units
    )
    session.event_contract = EventContractLedger(AuthorityEventContract(max_stream_payload_units=reserve + 1))
    # 契約の超過の限界の cause を publish できない（例: 設定の誤り）状態を作る
    monkeypatch.setattr(type(session), "publish_event_contract_limitation", lambda self: None)
    with pytest.raises(ValueError, match="not active"):
        connector.finish(session, _legacy_result(is_equivalent=True), case_id="issue110-unpublished")
    assert session.stream_truncated

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
    assert session.event_contract.relation_rows <= contract.ordinary_relation_rows
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
    assert session.event_contract.events <= contract.ordinary_events
    assert session.recorder.event_count == session.event_contract.events
    contract = AuthorityEventContract(max_event_payload_units=256)
    _connector_, session, emitted, _pending = _finished_session(
        monkeypatch, blockers=2, case_id="issue110-payload", contract=contract,
    )
    assert session.event_contract.exceeded.bound == "event_payload_units"
    assert emitted == [0, 0] and session.recorder.event_count == 0


def test_a_refused_transaction_leaves_the_stream_a_valid_prefix(monkeypatch):
    """拒んだ transaction は stream・producer の台帳・Phase 7 の buffer を変えない（部分的な event は無い）。"""

    contract = AuthorityEventContract(max_cause_occurrences=16)
    _connector_, session, emitted, _pending = _finished_session(
        monkeypatch, blockers=40, case_id="issue110-prefix", contract=contract,
    )
    assert session.recorder.event_count == session.event_contract.events == sum(emitted)
    stream_view = session.recorder.prefix_view()
    stream_view.validate()
    assert session.domain_signal_error_kinds == []


def test_the_pair_gate_checkpoint_counts_deferred_occurrences(monkeypatch):
    """判定の前に publish される予定の（遅延した）occurrence も、gate の前の checkpoint が数える。"""

    contract = AuthorityEventContract(max_cause_occurrences=16)
    _connector_, session, emitted, _pending = _finished_session(
        monkeypatch, blockers=5, case_id="issue110-deferred", contract=contract,
    )
    assert session.event_contract.exceeded is None
    session.domain_signal_state["sat_safety_deferred_observations"] = {
        f"deferred-{index}": object() for index in range(20)
    }
    with pytest.raises(AuthorityEventContractExceeded):
        session.event_contract_checkpoint()
    assert session.event_contract.exceeded.bound == "cause_occurrences"


def test_a_finish_time_refusal_publishes_the_contract_limitation_before_the_decision(monkeypatch):
    """gate の後（finish の中）で拒まれた event は落とし、判定の前に予約した枠で限界の cause を publish する。"""

    from scripts.function_tracer_pcode.authority.domains.analysis_limitation import (
        ANALYSIS_BUDGET_REASON_ID,
    )

    contract = AuthorityEventContract(max_cause_occurrences=16)
    connector, session, emitted, _pending = _finished_session(
        monkeypatch, blockers=3, case_id="issue110-finish", contract=contract,
    )
    assert session.event_contract.exceeded is None
    # finish の中で publish される遅延した観測が枠を超える（gate の後の超過）
    deferred = {f"finish-{index}": (_sat_blocker(1000 + index), "sat-safety-blocker-observed")
                for index in range(30)}
    session.domain_signal_state["sat_safety_deferred_observations"] = deferred
    session.event_contract.ordinary_occurrences = 0  # checkpoint を通した後の状態を作る
    evidence = connector.finish(session, _legacy_result(), case_id="issue110-finish")
    pilot = evidence.pilot_result
    assert session.event_contract.exceeded is not None
    assert session.event_contract.limitation_recorded
    assert pilot.candidate.decision_receipt.outcome is Outcome.UNKNOWN
    assert ANALYSIS_BUDGET_REASON_ID in {row.reason_id for row in pilot.reduction.projection.c_active_base}
    assert len(pilot.reduction.projection.c_active_base) <= contract.max_cause_occurrences


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
    contract = AuthorityEventContract(max_stream_payload_units=1 << 10, max_events=8)
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
class _Projection:
    c_active_base: tuple


def test_pricing_charges_the_reduction_by_events_and_active_occurrences():
    events = tuple(SimpleNamespace(authority_payload=1, diagnostic_payload=None) for _ in range(50))
    small = SealWorkBudget.for_result()
    SealPlan.price(small, stream=SimpleNamespace(events=events), projection=_Projection(()),
                   receipts=(), preimage=None, execution=None)
    rows = _Projection(tuple(range(40)))
    large = SealWorkBudget.for_result()
    plan = SealPlan.price(large, stream=SimpleNamespace(events=events), projection=rows,
                          receipts=(), preimage=None, execution=None)
    assert plan.components.reduction == 50 * 40
    assert large.consumed - small.consumed >= 50 * 40 - 50


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
    assert session.recorder.event_count == 1
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


class _SelfAuthority:
    def to_authority_dict(self):
        return self


def test_the_meter_stops_on_values_that_only_hop():
    """自分を返す `to_authority_dict`・Mock のように hop だけが続く値も、上限の中で止まる（無限に回らない）。"""

    from unittest.mock import MagicMock

    # Mock は呼ぶたびに自分の呼び出しの記録が伸びる（Mock 自身の仕事）ので小さい上限で確かめる
    for value, limit in ((_SelfAuthority(), 100_000), (MagicMock(), 200)):
        started = time.perf_counter()
        assert canonical_units_within(value, limit) is None
        assert time.perf_counter() - started < 1.0


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

    require_events_within_contract(AUTHORITY_EVENT_CONTRACT.max_events)
    with pytest.raises(ValueError):
        require_events_within_contract(AUTHORITY_EVENT_CONTRACT.max_events + 1)

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
    assert session.recorder.event_count == 12
    # 拒んだ signal は Phase 7 の buffer に 1 度も入らない（admission は buffer より前）
    assert len(buffered) == 12


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

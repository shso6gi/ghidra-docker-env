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

    monkeypatch.setattr(canonical_result, "_encoded", _counting_encoded)
    work = SealWorkBudget(before_step)
    with pytest.raises(BundleWorkExceeded) as stopped:
        _build(evidence, session, preimage, work)
    assert stopped.value.step == failing_step
    if failing_step == "encode_stream":
        assert calls["encoded"] == 0


def test_a_million_event_stream_stops_before_any_work(monkeypatch):
    """AC-110-S2: 10^6 event の stream は、何も作らずに契約の外として止まる（encode / digest / replay なし）。"""

    from scripts.function_tracer_pcode.authority.decision import canonical_result

    event = {"authority_payload": {"x": 1}, "diagnostic_payload": None, "header": {}}
    bundle = {"sealed_event_stream": {"payload": {"events": [event] * 1_000_000}}}
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


def test_a_huge_event_payload_is_outside_the_contract():
    events = (SimpleNamespace(authority_payload="z" * (AUTHORITY_EVENT_CONTRACT.max_event_payload_units + 10),
                              diagnostic_payload=None),)
    with pytest.raises(BundleWorkExceeded) as stopped:
        SealPlan.price(SealWorkBudget.for_result(), stream=SimpleNamespace(events=events),
                       projection=None, receipts=(), preimage=None, execution=None)
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

    offenders = []
    for path in (PACKAGE_ROOT / "authority").rglob("*.py"):
        if path.name in {"event_contract.py", "seal_work.py", "canonical_units.py"}:
            continue
        text = path.read_text(encoding="utf-8")
        if "max_cause_occurrences" in text or "max_relation_rows" in text:
            if "AUTHORITY_EVENT_CONTRACT" not in text:
                offenders.append(str(path.relative_to(PACKAGE_ROOT)))
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
    events = tuple(SimpleNamespace(authority_payload=None, diagnostic_payload=None) for _ in range(1_000))
    # header（1 event 1,024 単位）を辿る前に数える: 50 event 分の作業量なら 50 event 目あたりで止まる
    work = SealWorkBudget(50 * 1024)
    with pytest.raises(BundleWorkExceeded) as stopped:
        SealPlan.price(work, stream=SimpleNamespace(events=events), projection=None,
                       receipts=(), preimage=None, execution=None)
    assert stopped.value.step == "price"
    assert work.consumed <= 52 * 1024


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
    probe = SealWorkBudget.for_result()
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
    assert probe.consumed == 0


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

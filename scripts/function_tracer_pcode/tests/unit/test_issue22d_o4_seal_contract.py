# -*- coding: utf-8 -*-
"""Issue #22 PR-22-D O-4 の測り直し: 最終 envelope の封印は Issue #110 の契約の中だけで作る。

- 封印（`AuthoritySeal.seal(preimage, work=...)`）は envelope ごとの有限の作業量の中で行い、各段を実行する
  前に数える（作業量を受け取らない依存は 0）。
- 上限を超える入力（10^6 event の stream）は作業量の中で止まり、確定した判定を持つ durable な ERROR に
  なる（意味の UNKNOWN にしない: authority 確定後の出力の契約違反）。
- 257 件以上の cause・過大な relation は、判定の **前** に登録済みの理由の UNKNOWN（出力で ERROR に
  しない）で、authority の行は黙って切り詰めない。
- 上限の内側の封印は authority の builder がそのまま作るものと同じ。
"""

from __future__ import annotations

import json
import time
from types import SimpleNamespace

import pytest

from scripts.function_tracer_pcode.authority.event_contract import (
    AUTHORITY_EVENT_CONTRACT,
    AuthorityEventContract,
    EventContractLedger,
)
from scripts.function_tracer_pcode.authority.seal_work import (
    BundleWorkExceeded,
    SealWorkBudget,
    persisted_envelope_byte_limit,
)
from scripts.function_tracer_pcode.checker import output_schema
from scripts.function_tracer_pcode.checker.output_preparation import (
    BUNDLE_KEY,
    SEALS_PER_ENVELOPE,
    AuthoritySeal,
    build_final_result_envelope,
    envelope_seal_work,
)
from scripts.function_tracer_pcode.core.errors import reset_pair_failure_scopes
from scripts.function_tracer_pcode.core.json_encoding import RESULT_JSON_POLICY
from scripts.function_tracer_pcode.smt import SolverStatus
from scripts.function_tracer_pcode.tests.unit.test_issue106_pair_limitation_propagation import (
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

BUDGET_REASON = "analysis_budget_exceeded"


@pytest.fixture(autouse=True)
def _clean_scopes():
    reset_pair_failure_scopes()
    yield
    reset_pair_failure_scopes()


def _blocker(index: int):
    from scripts.function_tracer_pcode.authority.lifecycle.production_signals import (
        SatSafetyBlockerProductionSignal,
    )

    return SatSafetyBlockerProductionSignal(
        action="OBSERVED",
        reason_id="counterexample_analysis_safety_unproven",
        canonical_target_key=("issue22d-o4", index),
        missing_semantic_fact=("counterexample_safety_gate_unproven", "model"),
        evidence_refs=(f"issue22d-o4-{index}",),
        producer_id="sat_unsafety_reason_producer",
    )


def _result_with_blockers(count: int):
    """production の pair の制御フローで、stage plan が `count` 件の blocker を emit した結果。"""

    from scripts.function_tracer_pcode.authority.lifecycle.production_signals import (
        emit_sat_safety_signal,
    )

    def _plan(*_args, **_kwargs):
        for index in range(count):
            emit_sat_safety_signal(_blocker(index), producer_site_manifest_id="sat-safety-blocker-observed")
        return create_mock_result(is_equivalent=None, solver_status=SolverStatus.UNKNOWN)

    return _run_pair(analyze=_analyze_from(*_analyses()), stage_plan=_plan, checker=_new_checker(_connector()))


def _real_seal(result):
    evidence, session = result._canonical_finalization_context
    return AuthoritySeal(evidence=evidence, session=session)


class _Proxy:
    """実物の値を読みつつ、指定した属性だけを差し替える（test の入力を作るだけ）。"""

    def __init__(self, real, **overrides):
        self._real = real
        self._overrides = overrides

    def __getattr__(self, name):
        if name in self._overrides:
            return self._overrides[name]
        return getattr(self._real, name)


# ---------------------------------------------------------------------------
# 上限の owner と作業量
# ---------------------------------------------------------------------------


def test_the_output_schema_rows_are_the_authority_event_contract():
    """出力の schema の行数の上限は authority の event の契約の値そのもの（2 か所に書かない）。"""

    assert output_schema.MAX_UNKNOWN_REASON_ROWS == AUTHORITY_EVENT_CONTRACT.max_cause_occurrences
    assert output_schema.MAX_RELATION_ROWS == AUTHORITY_EVENT_CONTRACT.max_relation_rows
    assert output_schema.MAX_RECOVERY_ACTION_ROWS == output_schema.MAX_UNKNOWN_REASON_ROWS


def test_the_envelope_seal_work_is_finite_and_covers_its_passes():
    """envelope 1 つの作業量は、封印 `SEALS_PER_ENVELOPE` 回と永続化 1 回（契約だけから決まる有限の値）。"""

    work = envelope_seal_work()
    assert type(work) is SealWorkBudget
    assert work.limit == SealWorkBudget.for_result(passes=SEALS_PER_ENVELOPE + 1).limit
    assert 0 < work.limit < 1 << 44
    assert work.preimage_limit == AUTHORITY_EVENT_CONTRACT.max_result_preimage_units
    assert envelope_seal_work() is not work  # envelope ごとに 1 つ（共有しない）


def test_a_sealed_envelope_needs_its_work_and_the_exact_seal_type():
    result = _decided_result()
    with pytest.raises(TypeError, match="seal work"):
        build_final_result_envelope(result, seal=_real_seal(result))

    class _Other:
        def seal(self, preimage, *, work):  # pragma: no cover - never called
            raise AssertionError("an arbitrary seal was called")

    with pytest.raises(TypeError, match="only by an AuthoritySeal"):
        build_final_result_envelope(result, seal=_Other(), work=envelope_seal_work())


def test_the_real_seal_runs_within_its_envelope_work_and_matches_the_authority_builder(monkeypatch, tmp_path):
    """上限の内側: 封印は作業量の中で作られ、authority の builder が同じ preimage から作るものと同じ。"""

    from scripts.function_tracer_pcode.authority.decision import canonical_result

    result = _decided_result()
    work = envelope_seal_work()
    envelope = build_final_result_envelope(result, seal=_real_seal(result), work=work)
    assert 0 < work.consumed <= work.limit
    bundle = envelope.payload[BUNDLE_KEY]
    preimage = {key: value for key, value in envelope.payload.items() if key != BUNDLE_KEY}
    evidence, session = result._canonical_finalization_context
    direct = canonical_result.build_canonical_result_finalization_bundle(
        result_payload_preimage=preimage, evidence=evidence, session=session,
        work=SealWorkBudget.for_result(),
    )
    assert RESULT_JSON_POLICY.encode_bounded(bundle, max_bytes=None) == (
        RESULT_JSON_POLICY.encode_bounded(direct, max_bytes=None)
    )
    canonical_result.validate_canonical_result_finalization_bundle(
        bundle, result_payload_preimage=preimage, work=SealWorkBudget.for_result(),
    )
    # 最終 envelope の byte は出力の契約の中、永続化した envelope は読む側の上限の中
    assert envelope.total_bytes <= envelope.plan.max_bytes
    monkeypatch.setenv("UNKNOWN_TAXONOMY_V2_SUPERVISOR_ROOT", str(tmp_path))
    monkeypatch.setenv("UNKNOWN_TAXONOMY_V2_EXECUTION_NONCE", "issue22d-o4")
    path = canonical_result.persist_canonical_result_envelope(envelope.payload, work=work)
    assert path.stat().st_size <= persisted_envelope_byte_limit()
    assert work.consumed <= work.limit


def test_a_seal_out_of_work_returns_no_partial_bundle():
    result = _decided_result()
    with pytest.raises(BundleWorkExceeded) as stopped:
        build_final_result_envelope(result, seal=_real_seal(result), work=SealWorkBudget(1_000))
    assert stopped.value.kind == "work"


# ---------------------------------------------------------------------------
# 上限の外: 作業量の中で止まり、durable な ERROR（意味の UNKNOWN にしない）
# ---------------------------------------------------------------------------


def test_a_million_event_seal_stops_within_its_work_and_is_a_durable_error(monkeypatch, tmp_path):
    from scripts.function_tracer_pcode.authority.decision import canonical_result
    from scripts.function_tracer_pcode.cli.commands import equivalence

    decided = _decided_result()
    evidence, session = decided._canonical_finalization_context
    stream = evidence.pilot_result.sealed_event_stream
    huge = SimpleNamespace(events=(stream.events[0],) * 1_000_000, envelope=stream.envelope)
    seal = AuthoritySeal(
        evidence=_Proxy(evidence, pilot_result=_Proxy(evidence.pilot_result, sealed_event_stream=huge)),
        session=session,
    )
    work = envelope_seal_work()
    started = time.perf_counter()
    with pytest.raises(BundleWorkExceeded) as stopped:
        build_final_result_envelope(decided, seal=seal, work=work)
    assert stopped.value.kind == "contract"
    assert time.perf_counter() - started < 5.0
    assert work.consumed <= work.limit

    written = []
    monkeypatch.setattr(equivalence, "output_result", lambda content, *_a, **_k: written.append(content))
    monkeypatch.setattr(canonical_result, "persist_canonical_result_envelope", lambda _payload, **_kw: None)
    monkeypatch.setattr(equivalence, "journal_stage_end", lambda *_a, **_k: None)
    args = SimpleNamespace(verbose=False, debug=False, output=None, quiet=True)
    with pytest.raises(SystemExit):
        equivalence._final_envelope_or_error_result(
            args, result=decided, seal=seal, work=envelope_seal_work(),
            binary1_path=str(tmp_path / "a"), binary2_path=str(tmp_path / "b"),
            func_name1="f", func_name2="f", start_time=0.0, emission_started=0.0,
        )
    block = next(content for content in written if "EQUIVALENCE_RESULT_JSON_BEGIN" in content)
    payload = json.loads(block.split("\n")[1])
    # authority 確定後の出力の契約違反: 確定した判定を持つ ERROR（UNKNOWN にしない）
    assert payload["final_outcome"] == "ERROR"
    assert payload["superseded_decision_receipt"]["decision_receipt"]["outcome"] == decided.final_outcome
    assert BUNDLE_KEY in payload  # ERROR の envelope は自分の封印を持つ（部分的な元の封印ではない）


# ---------------------------------------------------------------------------
# 契約の外の authority（257 件以上の cause・過大な relation）: 判定の前の UNKNOWN
# ---------------------------------------------------------------------------


def _unknown_reason_ids(payload):
    return {row["reason_id"] for row in payload["unknown_reasons"]}


def test_more_causes_than_the_contract_reach_the_output_as_a_registered_unknown():
    """300 件の cause の pair: 判定の前に契約の限界の UNKNOWN になり、出力は ERROR ではない。

    authority の行（reason・relation）は契約の上限の中で、出力はそれを **全部** 持つ（黙って切らない）。
    """

    result = _result_with_blockers(300)
    work = envelope_seal_work()
    envelope = build_final_result_envelope(result, seal=_real_seal(result), work=work)
    payload = envelope.payload
    assert payload["final_outcome"] == "UNKNOWN"
    assert BUDGET_REASON in _unknown_reason_ids(payload)
    assert len(payload["unknown_reasons"]) <= output_schema.MAX_UNKNOWN_REASON_ROWS
    assert len(payload["c_active_base"]) <= output_schema.MAX_RELATION_ROWS
    assert len(payload["c_active_base"]) == len(result.canonical_c_active_base)
    assert len(payload["unknown_reasons"]) == len(result.unknown_reasons)
    assert not ({"unknown_reasons", "c_active_base", "q_open_base", "decision_receipt"}
                & set(envelope.truncated_metadata))
    assert work.consumed <= work.limit


def test_a_relation_overflow_reaches_the_output_as_a_registered_unknown(monkeypatch):
    contract = AuthorityEventContract(max_cause_occurrences=64, max_relation_rows=12)
    monkeypatch.setattr(EventContractLedger.__init__, "__defaults__", (contract,))
    result = _result_with_blockers(30)
    envelope = build_final_result_envelope(result, seal=_real_seal(result), work=envelope_seal_work())
    payload = envelope.payload
    assert payload["final_outcome"] == "UNKNOWN"
    assert BUDGET_REASON in _unknown_reason_ids(payload)
    assert len(payload["q_open_base"]) <= contract.max_relation_rows
    assert len(payload["q_open_base"]) == len(result.canonical_q_open_base)


def test_a_huge_limitation_description_is_bounded_before_attribution_digests_it(monkeypatch):
    """帰属する限界の記述（target key・帰属キー）が契約の外なら、帰属は何かを作る前（digest の前）に
    契約の超過の限界の cause へ向く（10^6 要素の key を digest・写しにしない）。"""

    from scripts.function_tracer_pcode.authority.decision import limitation_attribution as la
    from scripts.function_tracer_pcode.authority.domains import analysis_limitation
    from scripts.function_tracer_pcode.authority.domains.analysis_limitation import (
        ANALYSIS_BUDGET_REASON_ID,
    )
    from scripts.function_tracer_pcode.core.errors import (
        AnalysisLimitation,
        CauseAttributionKey,
        pair_failure_scope,
    )

    monkeypatch.setenv("UNKNOWN_TAXONOMY_V2_RESULT_ENTRY_OCCURRENCE_NONCE", "issue22d-o4-huge-occurrence")
    session = _connector().begin({"case": "issue22d-o4-huge"})
    huge = tuple(range(10 ** 6))
    digested = []
    real_digest = analysis_limitation.authority_digest

    def _digest(value):
        digested.append(value)
        return real_digest(value)

    monkeypatch.setattr(analysis_limitation, "authority_digest", _digest)
    for limitation in (
        AnalysisLimitation(
            ANALYSIS_BUDGET_REASON_ID, "a huge target", site="issue22d.o4.huge",
            target_key=huge, evidence_refs=("issue22d-o4-huge",),
        ),
        AnalysisLimitation(
            ANALYSIS_BUDGET_REASON_ID, "a huge attribution key", site="issue22d.o4.huge-key",
            target_key=("issue22d-o4-huge-key",), evidence_refs=("issue22d-o4-huge-key",),
            attribution=CauseAttributionKey(
                reason_id=ANALYSIS_BUDGET_REASON_ID, identity_scope="RELATIONAL", target_kind="limitation",
                canonical_target_key=huge, missing_semantic_fact=("issue22d",),
                semantic_proposition=("issue22d",), proof_requirement_ids=(),
            ),
        ),
    ):
        with pair_failure_scope(("issue22d", "o4-huge"), session.identity.result_occurrence_id):
            started = time.perf_counter()
            attribution = la.attribute_analysis_limitation(session, limitation)
            assert time.perf_counter() - started < 1.0
        assert attribution.disposition in (la.ATTRIBUTED_TRUNCATED_STREAM, la.UNATTRIBUTED)
        assert session.event_contract.contract_cause_published
        assert not any(value is huge or huge in _flat(value) for value in digested)


def _flat(value, depth=0):
    """digest に渡った値の中の tuple（浅く。10^6 要素の tuple そのものが入っていないかを見る）。"""

    if depth > 4 or not isinstance(value, (tuple, list, dict)):
        return ()
    items = value.values() if isinstance(value, dict) else value
    found = []
    for item in items:
        if isinstance(item, tuple) and len(item) > 1000:
            found.append(item)
        found.extend(_flat(item, depth + 1))
    return found


def test_output_preparation_never_runs_past_the_contract_even_with_the_budget_off():
    """調査用に直列化の予算を外しても（`off`）・契約より大きくしても、出力の準備の byte の上限は
    authority の契約（結果の preimage）の中。上限の内側の予算はそのまま。"""

    from scripts.function_tracer_pcode.checker.output_preparation import OutputPreparer
    from scripts.function_tracer_pcode.config.settings import expression_budget_policy
    from scripts.function_tracer_pcode.core.budget_policy import BudgetPolicy

    ceiling = AUTHORITY_EVENT_CONTRACT.max_result_preimage_units
    off = expression_budget_policy({"FT_SERIALIZATION_BYTES_BUDGET": "off"})
    assert off.serialization_bytes is None
    for policy in (off, BudgetPolicy.unlimited(), BudgetPolicy(serialization_bytes=ceiling * 2)):
        prepared = OutputPreparer(policy).policy
        assert prepared.serialization_bytes == ceiling
        assert prepared.prepared_payload_limit() is not None
    default = expression_budget_policy({})
    assert OutputPreparer(default).policy is default
    # 上限で置き換えるときは headroom も有効な値（設定の組み合わせで policy を作れない値にしない）。
    # 準備した payload と判定に使わない準備物（headroom を共有）の和は上限の中
    huge_headroom = expression_budget_policy({
        "FT_SERIALIZATION_BYTES_BUDGET": "off", "FT_ENVELOPE_HEADROOM_BYTES": str(300 << 20),
    })
    clamped = OutputPreparer(huge_headroom).policy
    assert clamped.envelope_headroom_bytes <= ceiling // 2
    assert clamped.prepared_payload_limit() + clamped.envelope_headroom_bytes == ceiling
    no_headroom = OutputPreparer(expression_budget_policy({
        "FT_SERIALIZATION_BYTES_BUDGET": "off", "FT_ENVELOPE_HEADROOM_BYTES": "off",
    })).policy
    assert no_headroom.envelope_headroom_bytes == output_schema.required_headroom_bytes()


def test_the_diagnostics_copy_is_bounded_and_leaves_a_count_marker():
    """診断の mapping の key の写しは live_values の上限まで。外は件数の marker（判定に使わない）。"""

    from scripts.function_tracer_pcode.checker import output_preparation
    from scripts.function_tracer_pcode.core import live_values
    from scripts.function_tracer_pcode.core.budget_policy import BudgetPolicy

    result = create_mock_result(is_equivalent=True)
    result.diagnostics = {f"k{index}": index for index in range(10 ** 6)}
    prepared = SimpleNamespace(plan=SimpleNamespace(to_diagnostic=lambda: {}))
    started = time.perf_counter()
    output_preparation._attach_budget_diagnostics(result, prepared, BudgetPolicy.unlimited())
    assert time.perf_counter() - started < 1.0
    limit = live_values.SCAN_LIMIT
    assert result.diagnostics["diagnostics_overflow"] == {"truncated": True, "keys": 10 ** 6, "kept": limit}
    # 先頭の上限の組は残す（`failures` など既存の診断を捨てない）
    assert len(result.diagnostics) == limit + 2 and result.diagnostics["k0"] == 0
    small = create_mock_result(is_equivalent=True)
    small.diagnostics = {f"k{index}": index for index in range(live_values.SCAN_LIMIT)}
    output_preparation._attach_budget_diagnostics(small, prepared, BudgetPolicy.unlimited())
    assert len(small.diagnostics) == live_values.SCAN_LIMIT + 1


def test_a_limitation_with_more_evidence_than_the_read_bound_is_still_an_attributed_unknown():
    """authority の契約に収まる限界（参照 5,000 件）は、診断の写しが先頭だけでも pair を止めない:
    登録済みの理由の UNKNOWN に帰属し、写さなかった件数を診断に残す。"""

    from scripts.function_tracer_pcode.core import live_values
    from scripts.function_tracer_pcode.core.errors import DeadlineExceeded, raise_limitation

    refs = tuple(f"e{index}" for index in range(5_000))

    def _plan(*_args, **_kwargs):
        raise_limitation(DeadlineExceeded(
            "many evidence refs", site="issue22d.o4.many-refs", target_key=("issue22d-many-refs",),
            evidence_refs=refs,
        ))

    result = _run_pair(analyze=_analyze_from(*_analyses()), stage_plan=_plan, checker=_new_checker(_connector()))
    assert result.final_outcome == "UNKNOWN"
    assert BUDGET_REASON in {reason.reason_id for reason in result.unknown_reasons}
    text = json.dumps(result.diagnostics, default=str)
    assert f'"evidence_refs_omitted": {len(refs) - live_values.SCAN_LIMIT}' in text

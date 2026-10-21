# -*- coding: utf-8 -*-
"""commit 済みの witness への final gate の veto を authority へ届ける（U-14 / #271、plan N-4）。

strategy は比較の中で安全な counterexample を commit する（authority の記録）。その後の final
call/effect preflight gate の veto は、修正前は legacy の結果を None にして legacy 専用の診断を
付けるだけだった。authority では commit した witness が decisive のまま残り、EQ だけを止める
cause（例: ``return_coverage_gap``）が別にあると pilot の closure が抑制され、最終 NOT_EQ に
なっていた。

守る契約（``checker/preflight_gate.py`` の veto の分岐と
``proof_gates/sat_safety.py::emit_post_commit_veto_blocker``）:

* commit の記録（``committed_safe_counterexample``）があり、gate が veto したら、
  ``post_commit_veto:<blocker>`` の SAT-safety blocker を commit した witness に束縛して出す。
  型は解析の不安全で、登録済みの ``counterexample_analysis_safety_unproven`` に写り、replay でも
  witness の完了でも解消しない。
* legacy の結果の値は読まない（commit は authority の記録から、veto は gate の blocker から）。
* veto の無い commit、commit の無い veto、EQ への veto は今どおり。

veto と EQ だけを止める cause は final gate を包んで注入する（production の gate 自体はそのまま
走らせ、cleanup の完了を偽にするか、manifest の構築を失敗させる）。
"""

from __future__ import annotations

from contextlib import contextmanager

import pytest

from scripts.function_tracer_pcode.authority.lifecycle.production_signals import (
    committed_safe_counterexample,
)
from scripts.function_tracer_pcode.checker.preflight_gate import PreflightGateMixin
from scripts.function_tracer_pcode.proof.sat_safety_resolution import (
    COUNTEREXAMPLE_ANALYSIS_SAFETY_UNPROVEN,
    SatSafetyResolution,
    classify_sat_safety_blocker,
    replay_may_resolve_sat_safety_reason,
)
from scripts.function_tracer_pcode.proof.strategies.proof_gates.sat_safety import (
    POST_COMMIT_VETO_REF_PREFIX,
)
from scripts.function_tracer_pcode.core import Expression
from scripts.function_tracer_pcode.tests.unit._production_check_harness import (
    call_effect_manifest_failure,
    run_production_check,
)
from scripts.function_tracer_pcode.tests.unit.test_unpaired_input_sat_gate import (
    _CONFIGS,
    _FIRST_STAGE,
    _configured,
    _param,
    _side,
)


def _not_eq_pair():
    """``n`` と ``n + 1``（relation が覆う parameter だけの SAT。両 strategy が安全な counterexample を commit する）。"""

    return _side("f", _param()), _side("g", Expression.binary_op("INT_ADD", _param(), Expression.constant(1, 4)))


def _eq_pair():
    return _side("f", _param()), _side("g", _param())


def _emit_eq_only_blocker():
    """EQ だけを止める cause（``return_coverage_gap``、``blocks_equivalence``）を出す。"""

    from scripts.function_tracer_pcode.authority.domains.return_coverage import ReturnCoverageBlockerSignal
    from scripts.function_tracer_pcode.authority.lifecycle.production_signals import emit_return_coverage_signal

    emit_return_coverage_signal(ReturnCoverageBlockerSignal(
        declared_reason_id="return_coverage_gap", function_identity=("u14", "f"),
        coverage_check="return_coverage_gate_verdict", comparison_identity=("u14", "S_PAIRWISE", "0"),
        evidence_refs=("u14_injected_eq_only_blocker",),
    ), producer_site_manifest_id="return-coverage-final-terminal")


@contextmanager
def _final_gate(*, veto, eq_only):
    """final gate を包む。最初の呼び出しで veto（cleanup の未完了）と EQ だけを止める cause を注入する。

    yield するのは gate の呼び出しの記録（呼び出し時点で commit があったか、注入したか）。
    """

    calls = []
    original = PreflightGateMixin._apply_preflight_final_gate

    def wrapped(self, strategy_result, frame, *, cleanup_complete):
        first = not calls
        calls.append({"committed": committed_safe_counterexample() is not None, "injected": first})
        if first and eq_only:
            _emit_eq_only_blocker()
        if first and veto:
            cleanup_complete = False
        return original(self, strategy_result, frame, cleanup_complete=cleanup_complete)

    PreflightGateMixin._apply_preflight_final_gate = wrapped
    try:
        yield calls
    finally:
        PreflightGateMixin._apply_preflight_final_gate = original


def _strings(value):
    if isinstance(value, dict):
        for item in value.values():
            yield from _strings(item)
    elif isinstance(value, (list, tuple)):
        for item in value:
            yield from _strings(item)
    elif isinstance(value, str):
        yield value


def _post_commit_refs(result):
    return sorted({text for text in _strings(result) if text.startswith(POST_COMMIT_VETO_REF_PREFIX)})


def _active(result):
    return sorted({str(row.get("reason_id")) for row in result.get("c_active_base") or ()})


def _run(case_id, config, pair, *, veto=False, eq_only=False, manifest_failure=False):
    strategy, query_mode = _CONFIGS[config]
    left, right = pair()
    with _configured(strategy, query_mode) as region_runs, _final_gate(veto=veto, eq_only=eq_only) as calls:
        if manifest_failure:
            with call_effect_manifest_failure(lambda _a, _b: True) as injected:
                result = run_production_check(f"u14-{config}-{case_id}", left, right)
            assert injected, "the manifest failure was not injected"
        else:
            result = run_production_check(f"u14-{config}-{case_id}", left, right)
    assert result["stage_path"][0] == _FIRST_STAGE[strategy], result["stage_path"]
    if query_mode == "split":
        assert region_runs and all(run is not None for run in region_runs), region_runs
    elif query_mode == "legacy":
        assert region_runs == []
    return result, calls


@pytest.mark.parametrize("config", sorted(_CONFIGS))
def test_veto_of_a_committed_witness_is_not_a_disequivalence(config):
    """commit + veto + EQ だけを止める cause。修正前は両 strategy で最終 NOT_EQ（#271）。"""

    result, calls = _run("cleanup_eqblk", config, _not_eq_pair, veto=True, eq_only=True)
    assert calls[0]["committed"], calls
    assert result["final_outcome"] == "UNKNOWN", (result["final_outcome"], _active(result))
    assert COUNTEREXAMPLE_ANALYSIS_SAFETY_UNPROVEN in _active(result)
    assert _post_commit_refs(result) == [POST_COMMIT_VETO_REF_PREFIX + "dispatch_cleanup_incomplete"]


@pytest.mark.parametrize("config", sorted(_CONFIGS))
def test_veto_alone_of_a_committed_witness_names_the_witness_blocker(config):
    """EQ だけを止める cause が無い veto も、closure に頼らず commit した witness の blocker で止まる。"""

    result, calls = _run("cleanup", config, _not_eq_pair, veto=True)
    assert calls[0]["committed"], calls
    assert result["final_outcome"] == "UNKNOWN", (result["final_outcome"], _active(result))
    assert COUNTEREXAMPLE_ANALYSIS_SAFETY_UNPROVEN in _active(result)
    assert _post_commit_refs(result) == [POST_COMMIT_VETO_REF_PREFIX + "dispatch_cleanup_incomplete"]


def test_manifest_failure_veto_of_a_committed_witness_is_not_a_disequivalence():
    """veto の原因が manifest の構築失敗（projection の未完了）でも同じ。"""

    result, calls = _run("manifest_eqblk", "pairwise", _not_eq_pair, eq_only=True, manifest_failure=True)
    assert calls[0]["committed"], calls
    assert result["final_outcome"] == "UNKNOWN", (result["final_outcome"], _active(result))
    assert COUNTEREXAMPLE_ANALYSIS_SAFETY_UNPROVEN in _active(result)
    refs = _post_commit_refs(result)
    assert refs and all(ref.startswith(POST_COMMIT_VETO_REF_PREFIX) for ref in refs), refs


@pytest.mark.parametrize("config", sorted(_CONFIGS))
def test_committed_witness_without_veto_stays_not_eq(config):
    """対照: veto の無い commit は NOT_EQ のまま（EQ だけを止める cause があっても）。"""

    for case_id, eq_only in (("none", False), ("eqblk_only", True)):
        result, calls = _run(case_id, config, _not_eq_pair, eq_only=eq_only)
        assert calls[0]["committed"], calls
        assert result["final_outcome"] == "NOT_EQ", (case_id, _active(result))
        assert _post_commit_refs(result) == []


def test_veto_without_a_commit_is_unchanged():
    """対照: commit の無い veto（EQ への veto）は今どおり。witness の blocker は出さず、veto の後も
    次の phase が走る（再解析の結果の EQ がそのまま最終になる）。"""

    result, calls = _run("eq_veto", "pairwise", _eq_pair, veto=True)
    assert not any(call["committed"] for call in calls), calls
    assert len(calls) >= 2, calls
    assert result["final_outcome"] == "EQUIVALENT", _active(result)
    assert _post_commit_refs(result) == []


def test_eq_pair_without_veto_stays_equivalent():
    result, calls = _run("eq", "pairwise", _eq_pair)
    assert not calls[0]["committed"], calls
    assert result["final_outcome"] == "EQUIVALENT", _active(result)


def test_post_commit_veto_blocker_is_analysis_unsafety_that_nothing_completes():
    """``post_commit_veto:*`` は解析の不安全: replay でも witness の完了でも解消しない。"""

    refs = (POST_COMMIT_VETO_REF_PREFIX + "dispatch_cleanup_incomplete",)
    blocker = classify_sat_safety_blocker(COUNTEREXAMPLE_ANALYSIS_SAFETY_UNPROVEN, refs)
    assert blocker.resolution is SatSafetyResolution.ANALYSIS_UNSAFETY
    assert not blocker.replay_resolvable
    assert not blocker.completable
    assert not replay_may_resolve_sat_safety_reason(COUNTEREXAMPLE_ANALYSIS_SAFETY_UNPROVEN, refs)


def test_committed_reader_is_fail_closed_on_an_inexact_record():
    """commit の記録が型どおりでなければ「無い」とは扱わない（fail-closed）。"""

    from types import SimpleNamespace

    from scripts.function_tracer_pcode.authority.lifecycle.production_signals import (
        SAFE_COUNTEREXAMPLE_COMMITTED_KEY,
    )

    assert committed_safe_counterexample(SimpleNamespace(domain_signal_state={})) is None
    with pytest.raises(TypeError):
        committed_safe_counterexample(SimpleNamespace(
            domain_signal_state={SAFE_COUNTEREXAMPLE_COMMITTED_KEY: "digest-only"},
        ))

# -*- coding: utf-8 -*-
"""Issue #47: callee 解析 cache（``call_analysis_cache``）の hit/miss 診断。

``_analysis_scope_key()` の semantic key も cache の再利用方針も変えず、miss の原因
（unbound entry 不在 / ``bound_signature`` 差 / ``storage_bound_signature`` 差 / 分類不能）
だけを観測できることを固定する。parameter snapshot cache とは別概念。
"""

from unittest.mock import Mock, patch

from scripts.function_tracer_pcode.analysis.returns.analyzer import ReturnAnalyzer
from scripts.function_tracer_pcode.analysis.returns.analyze_function import (
    _record_callee_analysis_cache_lookup,
)
from scripts.function_tracer_pcode.analysis.returns.lifecycle import (
    analysis_cache_target_identity,
    analysis_scope_key_components,
    classify_analysis_scope_cache_miss,
)
from scripts.function_tracer_pcode.analysis.runtime_state import repeated_miss_targets
from scripts.function_tracer_pcode.core.call_target import CallTargetRef


TARGET = ("function", 11, 0x401000)
OTHER_TARGET = ("function", 11, 0x402000)


def _key(target=TARGET, bound=(), storage=()):
    return ("analysis_scope", target, bound, storage)


BOUND_A = ((0, "sig-a"),)
BOUND_B = ((0, "sig-b"),)
STORAGE_A = ((("register", "x0"), "sig-a"),)
STORAGE_B = ((("register", "x0"), "sig-b"),)


def test_scope_key_components_reject_non_scope_keys():
    assert analysis_scope_key_components(_key()) == (TARGET, (), ())
    assert analysis_scope_key_components(("0x401000",)) is None
    assert analysis_scope_key_components(None) is None


def test_first_analysis_of_a_target_is_not_a_bound_miss():
    reason, unbound_absent, same_target = classify_analysis_scope_cache_miss(
        _key(bound=BOUND_A), [_key(target=OTHER_TARGET)]
    )
    assert reason == "target_first_analysis"
    assert unbound_absent is True
    assert same_target == 0


def test_bound_signature_difference_is_identified():
    reason, unbound_absent, same_target = classify_analysis_scope_cache_miss(
        _key(bound=BOUND_B, storage=STORAGE_A),
        [_key(bound=BOUND_A, storage=STORAGE_A)],
    )
    assert reason == "bound_signature_differs"
    assert unbound_absent is True
    assert same_target == 1


def test_storage_bound_signature_difference_is_identified():
    reason, unbound_absent, _ = classify_analysis_scope_cache_miss(
        _key(bound=BOUND_A, storage=STORAGE_B),
        [_key(bound=BOUND_A, storage=STORAGE_A)],
    )
    assert reason == "storage_bound_signature_differs"
    assert unbound_absent is True


def test_both_signatures_differing_is_reported_separately():
    reason, _, _ = classify_analysis_scope_cache_miss(
        _key(bound=BOUND_B, storage=STORAGE_B),
        [_key(bound=BOUND_A, storage=STORAGE_A)],
    )
    assert reason == "bound_and_storage_bound_signature_differ"


def test_a_different_target_is_never_classified_as_a_bound_miss():
    reason, unbound_absent, same_target = classify_analysis_scope_cache_miss(
        _key(target=OTHER_TARGET, bound=BOUND_A),
        [_key(target=TARGET, bound=BOUND_A), _key(target=TARGET, bound=BOUND_B)],
    )
    assert reason == "target_first_analysis"
    assert same_target == 0
    assert unbound_absent is True


def test_unbound_entry_presence_is_reported_for_bound_requests():
    _, unbound_absent, _ = classify_analysis_scope_cache_miss(
        _key(bound=BOUND_A), [_key(), _key(bound=BOUND_B)]
    )
    assert unbound_absent is False
    # 無束縛の要求は「unbound entry 不在」の対象にしない。
    _, unbound_absent_for_unbound_request, _ = classify_analysis_scope_cache_miss(
        _key(), [_key(bound=BOUND_A)]
    )
    assert unbound_absent_for_unbound_request is False


def test_a_non_scope_key_request_is_unclassified():
    reason, unbound_absent, same_target = classify_analysis_scope_cache_miss(
        ("0x401000",), [_key()]
    )
    assert reason == "unclassified"
    assert unbound_absent is False
    assert same_target == 0


def test_target_identity_is_a_stable_string_without_object_identity():
    ref = CallTargetRef.from_name("log")
    assert analysis_cache_target_identity(ref) == "function:log"
    assert analysis_cache_target_identity(None) == "unknown:UNKNOWN_FUNC"

    class _Broken:
        kind = "function"

        def display_name(self):
            raise RuntimeError("boom")

    assert analysis_cache_target_identity(_Broken()) == "unknown:UNKNOWN_FUNC"


def _analyzer():
    return ReturnAnalyzer(program=Mock(), debug=False)


def _ref(name="callee", entry=0x401000, external=False):
    return CallTargetRef(
        kind="function", function_name=name, program_id=11, entry_offset=entry,
        is_external=external, is_thunk=False,
    )


def test_lookup_records_hits_and_bound_misses_per_target():
    analyzer = _analyzer()
    ref = _ref()
    analyzer._call_analysis_cache[_key(bound=BOUND_A)] = "analysis"

    # 同一 scope の再利用は hit。
    _record_callee_analysis_cache_lookup(analyzer, ref, _key(bound=BOUND_A), "analysis")
    # 同一 target・bound だけ違う要求は bound_signature_differs の miss。
    _record_callee_analysis_cache_lookup(analyzer, ref, _key(bound=BOUND_B), None)
    analyzer._call_analysis_cache[_key(bound=BOUND_B)] = "analysis"
    _record_callee_analysis_cache_lookup(
        analyzer, ref, _key(bound=((0, "sig-c"),)), None
    )

    payload = analyzer.callee_analysis_cache_diagnostics()
    assert payload["hits"] == 1
    assert payload["misses"] == 2
    assert payload["miss_reasons"] == {"bound_signature_differs": 2}
    assert payload["bound_misses_without_unbound_entry"] == 2
    assert payload["repeated_miss_targets"] == {
        "bound_signature_differs": ["function:callee@0x401000"]
    }
    row = payload["targets"][0]
    assert row["target"] == "function:callee@0x401000"
    assert row["hits"] == 1 and row["misses"] == 2
    assert row["miss_reasons"] == {"bound_signature_differs": 2}
    assert row["is_external"] is False
    assert payload["entries"] == 2


def test_lookup_records_a_cold_target_without_marking_a_bound_miss():
    analyzer = _analyzer()
    _record_callee_analysis_cache_lookup(analyzer, _ref(), _key(), None)
    payload = analyzer.callee_analysis_cache_diagnostics()
    assert payload["miss_reasons"] == {"target_first_analysis": 1}
    assert payload["bound_misses_without_unbound_entry"] == 0
    assert payload["repeated_miss_targets"] == {}


def test_diagnostics_failure_never_propagates_to_the_analysis():
    analyzer = _analyzer()
    broken = Mock()
    broken.record_hit.side_effect = RuntimeError("boom")
    broken.record_miss.side_effect = RuntimeError("boom")
    analyzer._callee_analysis_cache_stats = broken
    # 記録側が壊れても解析経路へ例外を出さない。
    _record_callee_analysis_cache_lookup(analyzer, _ref(), _key(), "analysis")
    _record_callee_analysis_cache_lookup(analyzer, _ref(), _key(), None)

    # 読み出し側が壊れても診断だけが error を返す。
    failing = Mock()
    failing.snapshot.side_effect = RuntimeError("boom")
    analyzer._callee_analysis_cache_stats = failing
    assert "error" in analyzer.callee_analysis_cache_diagnostics()


def test_analyze_function_records_the_cache_hit_it_returns():
    """実際の lookup 経路（``analyze_function``）が診断を残すことを固定する。"""
    analyzer = _analyzer()
    function = Mock()
    ref = _ref()
    scope_key = _key()
    with patch.object(analyzer, "_analysis_scope_key", return_value=scope_key):
        with patch(
            "scripts.function_tracer_pcode.core.call_target.CallTargetRef.from_function",
            return_value=ref,
        ):
            analyzer._call_analysis_cache[scope_key] = "cached-analysis"
            assert analyzer.analyze_function(function) == "cached-analysis"

    payload = analyzer.callee_analysis_cache_diagnostics()
    assert payload["hits"] == 1 and payload["misses"] == 0
    assert payload["targets"][0]["target"] == "function:callee@0x401000"


def test_repeated_miss_targets_lists_only_reasons_seen_at_least_twice():
    rows = [
        {"target": "a", "miss_reasons": {"bound_signature_differs": 2, "target_first_analysis": 1}},
        {"target": "b", "miss_reasons": {"bound_signature_differs": 1}},
        {"target": "c", "miss_reasons": {"storage_bound_signature_differs": 3}},
    ]
    assert repeated_miss_targets(rows) == {
        "bound_signature_differs": ["a"],
        "storage_bound_signature_differs": ["c"],
    }

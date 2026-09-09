# -*- coding: utf-8 -*-
"""Issue #47 (PR-A): successful-decompile parameter snapshot cache の回帰テスト。

観測条件は「decompile 完了 + HighFunction あり」だけが snapshot の根拠であり、
既存の ``_effect_summary_parameter_cache``（partial / richer descriptor cache）の
併合規則は変えない、という契約を固定する。
"""

import pytest
from unittest.mock import Mock, patch

from scripts.function_tracer_pcode.analysis.returns.analyzer import ReturnAnalyzer
from scripts.function_tracer_pcode.analysis.runtime_state import (
    SuccessfulDecompileParameterSnapshot,
)
from scripts.function_tracer_pcode.core.call_target import CallTargetRef


class _FakeFunction:
    def __init__(self, name: str, entry: int):
        self._name = name
        self._entry = entry

    def getName(self):
        return self._name

    def getEntryPoint(self):
        return self._entry


class _FakeFunctionManager:
    def __init__(self, by_addr, by_name):
        self._by_addr = dict(by_addr)
        self._by_name = dict(by_name)

    def getFunctionAt(self, addr):
        return self._by_addr.get(addr)

    def getFunctionContaining(self, addr):
        return self._by_addr.get(addr)

    def getFunctions(self, _forward):
        return list(self._by_name.values())


class _FakeAddressSpace:
    def getAddress(self, value):
        return value


class _FakeAddressFactory:
    def getDefaultAddressSpace(self):
        return _FakeAddressSpace()


class _FakeProgram:
    def __init__(self, functions, program_id=7):
        by_name = {func.getName(): func for func in functions}
        by_addr = {func.getEntryPoint(): func for func in functions}
        self._function_manager = _FakeFunctionManager(by_addr, by_name)
        self._program_id = program_id
        self.transactions = []

    def getFunctionManager(self):
        return self._function_manager

    def getAddressFactory(self):
        return _FakeAddressFactory()

    def getUniqueProgramID(self):
        return self._program_id

    def startTransaction(self, description):
        self.transactions.append(description)
        return len(self.transactions)

    def endTransaction(self, tx_id, commit):
        return None


def _analyzer():
    return ReturnAnalyzer(program=_FakeProgram([_FakeFunction("callee", 0x402000)]), debug=False)


def _target():
    return CallTargetRef.from_name("callee")


def _fresh_parameters():
    return [
        {"name": "param_1", "index": 0, "size": 8, "storage": {"register_name": "x0"}},
        {"name": "param_2", "index": 1, "size": 8, "storage": {"register_name": "x1"}},
    ]


def _completed_results():
    results = Mock()
    results.getHighFunction.return_value = Mock()
    return results


def test_second_lookup_of_the_same_callee_reuses_the_snapshot_without_decompiling():
    analyzer = _analyzer()
    with patch.object(
        analyzer, "_decompile_function", return_value=_completed_results()
    ) as decompile:
        with patch.object(analyzer, "_collect_parameters", side_effect=lambda _high: _fresh_parameters()):
            first = analyzer._get_freshest_callee_parameters(_target())
            second = analyzer._get_freshest_callee_parameters(_target())

    assert decompile.call_count == 1
    assert [param["name"] for param in first] == ["param_1", "param_2"]
    assert [param["name"] for param in second] == ["param_1", "param_2"]

    diagnostics = analyzer.callee_parameter_cache_diagnostics()
    assert diagnostics["hits"] == 1
    assert diagnostics["misses"] == 1
    assert diagnostics["miss_reasons"] == {"no_snapshot": 1}
    assert diagnostics["snapshots_stored"] == 1
    assert diagnostics["entries"] == 1


def test_failed_decompile_is_not_snapshotted_and_the_next_lookup_decompiles_again():
    analyzer = _analyzer()
    cache_key = analyzer._function_cache_key(_FakeFunction("callee", 0x402000))
    analyzer._effect_summary_parameter_cache[cache_key] = [{"name": "partial", "index": 0, "size": 8}]

    with patch.object(analyzer, "_decompile_function", return_value=None) as decompile:
        first = analyzer._get_freshest_callee_parameters(_target())
        second = analyzer._get_freshest_callee_parameters(_target())

    assert decompile.call_count == 2
    assert [param["name"] for param in first] == ["partial"]
    assert [param["name"] for param in second] == ["partial"]
    assert analyzer._callee_parameter_decompile_cache == {}

    diagnostics = analyzer.callee_parameter_cache_diagnostics()
    assert diagnostics["hits"] == 0
    assert diagnostics["misses"] == 2
    assert diagnostics["uncacheable_reasons"] == {"decompile_incomplete": 2}


def test_missing_high_function_is_not_snapshotted_and_the_next_lookup_decompiles_again():
    analyzer = _analyzer()
    results = Mock()
    results.getHighFunction.return_value = None

    with patch.object(analyzer, "_decompile_function", return_value=results) as decompile:
        assert analyzer._get_freshest_callee_parameters(_target()) == []
        assert analyzer._get_freshest_callee_parameters(_target()) == []

    assert decompile.call_count == 2
    assert analyzer._callee_parameter_decompile_cache == {}
    assert analyzer.callee_parameter_cache_diagnostics()["uncacheable_reasons"] == {
        "high_function_missing": 2
    }


def test_incomplete_decompile_after_a_snapshot_never_replaces_it():
    """成功観測の後に失敗しても、snapshot は「失敗」に上書きされない。"""
    analyzer = _analyzer()
    with patch.object(analyzer, "_decompile_function", return_value=_completed_results()):
        with patch.object(analyzer, "_collect_parameters", side_effect=lambda _high: _fresh_parameters()):
            analyzer._get_freshest_callee_parameters(_target())

    with patch.object(analyzer, "_decompile_function", return_value=None) as decompile:
        reused = analyzer._get_freshest_callee_parameters(_target())

    assert decompile.call_count == 0
    assert [param["name"] for param in reused] == ["param_1", "param_2"]


def test_richer_partial_cache_still_wins_over_a_snapshot_hit():
    """既存 ``choose_richer_parameter_descriptors`` の semantics は変えない。"""
    analyzer = _analyzer()
    cache_key = analyzer._function_cache_key(_FakeFunction("callee", 0x402000))

    with patch.object(analyzer, "_decompile_function", return_value=_completed_results()):
        with patch.object(analyzer, "_collect_parameters", side_effect=lambda _high: _fresh_parameters()):
            analyzer._get_freshest_callee_parameters(_target())

        analyzer._effect_summary_parameter_cache[cache_key] = [
            {"name": "rich_1", "index": 0, "size": 8, "data_type": "long", "storage": {"register_name": "x0"}},
            {"name": "rich_2", "index": 1, "size": 8, "data_type": "long", "storage": {"register_name": "x1"}},
            {"name": "rich_3", "index": 2, "size": 8, "data_type": "long", "storage": {"register_name": "x2"}},
        ]
        merged = analyzer._get_freshest_callee_parameters(_target())

    assert [param["name"] for param in merged] == ["rich_1", "rich_2", "rich_3"]


def test_snapshot_is_not_corrupted_by_a_consumer_mutating_the_returned_descriptors():
    """返り値を書き換えても snapshot 本体（再 decompile の代替根拠）は不変。

    ``_effect_summary_parameter_cache`` が返り値と dict を共有するのは従来どおりで、
    このテストが固定するのは新 cache 側の非共有性。
    """
    analyzer = _analyzer()
    cache_key = analyzer._function_cache_key(_FakeFunction("callee", 0x402000))
    with patch.object(analyzer, "_decompile_function", return_value=_completed_results()):
        with patch.object(analyzer, "_collect_parameters", side_effect=lambda _high: _fresh_parameters()):
            first = analyzer._get_freshest_callee_parameters(_target())
            first[0]["name"] = "mutated"
            first[0]["storage"]["register_name"] = "mutated"
            first.append({"name": "injected", "index": 9, "size": 8})

            snapshot = analyzer._callee_parameter_decompile_cache[cache_key]
            assert [param["name"] for param in snapshot.parameters] == ["param_1", "param_2"]
            assert snapshot.parameters[0]["storage"]["register_name"] == "x0"

            # partial cache を空にすると、hit 経路が返すのは snapshot 由来の無傷な複製。
            analyzer._effect_summary_parameter_cache.pop(cache_key, None)
            second = analyzer._get_freshest_callee_parameters(_target())

    assert [param["name"] for param in second] == ["param_1", "param_2"]
    assert second[0]["storage"]["register_name"] == "x0"


def test_collected_parameters_mutated_by_a_consumer_do_not_corrupt_the_snapshot():
    """``_collect_parameters`` の戻り値を後から書き換えても snapshot は不変。"""
    analyzer = _analyzer()
    cache_key = analyzer._function_cache_key(_FakeFunction("callee", 0x402000))
    collected = _fresh_parameters()
    with patch.object(analyzer, "_decompile_function", return_value=_completed_results()):
        with patch.object(analyzer, "_collect_parameters", return_value=collected):
            analyzer._get_freshest_callee_parameters(_target())
            collected[0]["name"] = "mutated"
            collected[0]["storage"]["register_name"] = "mutated"
            collected.append({"name": "injected", "index": 9, "size": 8})

            snapshot = analyzer._callee_parameter_decompile_cache[cache_key]
            assert [param["name"] for param in snapshot.parameters] == ["param_1", "param_2"]
            assert snapshot.parameters[0]["storage"]["register_name"] == "x0"

            analyzer._effect_summary_parameter_cache.pop(cache_key, None)
            reused = analyzer._get_freshest_callee_parameters(_target())

    assert [param["name"] for param in reused] == ["param_1", "param_2"]
    assert reused[0]["storage"]["register_name"] == "x0"


def test_materialized_parameters_are_a_fresh_copy_each_time():
    snapshot = SuccessfulDecompileParameterSnapshot.from_successful_decompile(
        _fresh_parameters(), decompile_contract_id="c", program_identity=7
    )
    first = snapshot.materialize_parameters()
    first[0]["name"] = "mutated"
    first[0]["storage"]["register_name"] = "mutated"
    second = snapshot.materialize_parameters()
    assert second[0]["name"] == "param_1"
    assert second[0]["storage"]["register_name"] == "x0"
    assert second[0] is not first[0]


def test_snapshot_from_a_different_observation_contract_is_not_reused():
    analyzer = _analyzer()
    cache_key = analyzer._function_cache_key(_FakeFunction("callee", 0x402000))
    analyzer._callee_parameter_decompile_cache[cache_key] = (
        SuccessfulDecompileParameterSnapshot.from_successful_decompile(
            [{"name": "stale", "index": 0, "size": 8}],
            decompile_contract_id="some-other-decompile-contract:timeout=1",
            program_identity=7,
        )
    )

    with patch.object(analyzer, "_decompile_function", return_value=_completed_results()) as decompile:
        with patch.object(analyzer, "_collect_parameters", side_effect=lambda _high: _fresh_parameters()):
            refreshed = analyzer._get_freshest_callee_parameters(_target())

    assert decompile.call_count == 1
    assert [param["name"] for param in refreshed] == ["param_1", "param_2"]
    assert analyzer.callee_parameter_cache_diagnostics()["miss_reasons"] == {
        "observation_contract_mismatch": 1
    }


def test_snapshot_from_a_different_program_identity_is_not_reused():
    analyzer = _analyzer()
    cache_key = analyzer._function_cache_key(_FakeFunction("callee", 0x402000))
    contract_id = None

    with patch.object(analyzer, "_decompile_function", return_value=_completed_results()):
        with patch.object(analyzer, "_collect_parameters", side_effect=lambda _high: _fresh_parameters()):
            analyzer._get_freshest_callee_parameters(_target())
            contract_id = analyzer._callee_parameter_decompile_cache[cache_key].decompile_contract_id
            analyzer._callee_parameter_decompile_cache[cache_key] = (
                SuccessfulDecompileParameterSnapshot.from_successful_decompile(
                    [{"name": "other_program", "index": 0, "size": 8}],
                    decompile_contract_id=contract_id,
                    program_identity=999,
                )
            )
            refreshed = analyzer._get_freshest_callee_parameters(_target())

    assert [param["name"] for param in refreshed] == ["param_1", "param_2"]
    assert analyzer.callee_parameter_cache_diagnostics()["miss_reasons"] == {
        "no_snapshot": 1,
        "observation_contract_mismatch": 1,
    }


def test_program_mutation_invalidates_the_snapshot_but_keeps_the_partial_cache():
    analyzer = _analyzer()
    cache_key = analyzer._function_cache_key(_FakeFunction("callee", 0x402000))

    with patch.object(analyzer, "_decompile_function", return_value=_completed_results()) as decompile:
        with patch.object(analyzer, "_collect_parameters", side_effect=lambda _high: _fresh_parameters()):
            analyzer._get_freshest_callee_parameters(_target())
            with analyzer._program_transaction("Disassemble local target 0x1000"):
                pass
            assert analyzer._callee_parameter_decompile_cache == {}
            assert cache_key in analyzer._effect_summary_parameter_cache
            analyzer._get_freshest_callee_parameters(_target())

    assert decompile.call_count == 2
    assert analyzer.callee_parameter_cache_diagnostics()["invalidations"] == 1


def test_unresolved_callee_is_counted_and_never_snapshotted():
    analyzer = _analyzer()
    with patch.object(analyzer, "_decompile_function") as decompile:
        assert analyzer._get_freshest_callee_parameters(CallTargetRef.from_name("missing")) == []

    assert decompile.call_count == 0
    assert analyzer.callee_parameter_cache_diagnostics()["uncacheable_reasons"] == {
        "callee_unresolved": 1
    }


def test_snapshot_refuses_to_represent_a_missing_high_function():
    with pytest.raises(ValueError):
        SuccessfulDecompileParameterSnapshot(
            parameters=(),
            decompile_contract_id="c",
            program_identity=1,
            high_function_present=False,
        )

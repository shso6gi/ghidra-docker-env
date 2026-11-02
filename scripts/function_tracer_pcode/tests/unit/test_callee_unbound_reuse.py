# -*- coding: utf-8 -*-
"""Issue #47 (PR-B): external placeholder callee の束縛ゼロ解析再利用の回帰テスト。

固定する契約:

- 再利用は「external と確定 + 解決が曖昧でない + decompile 完了 + HighFunction あり
  + 本体（戻る以外の P-code）が無い」callee だけ。それ以外は従来の bound-sensitive 経路。
- 再利用しても下流から見える解析結果は従来と同じ（要求された scope の view を返す）。
- 束縛付き解析が束縛ゼロ entry に混入しない。generic function cache key は使わない。
- shadow validation は記録のみで、一致しなければ従来結果を採る。
"""

from unittest.mock import Mock, patch

from scripts.function_tracer_pcode.analysis.returns.analyzer import ReturnAnalyzer
from scripts.function_tracer_pcode.analysis.returns import callee_unbound_reuse as reuse_module
from scripts.function_tracer_pcode.analysis.returns.callee_unbound_reuse import (
    placeholder_body_ineligibility_reason,
    shadow_results_match,
)
from scripts.function_tracer_pcode.config import settings
from scripts.function_tracer_pcode.core.analysis import FunctionReturnAnalysis
from scripts.function_tracer_pcode.core.call_target import CallTargetRef
from scripts.function_tracer_pcode.core.expression import Expression


# --------------------------------------------------------------------------- fakes


class _FakeVarnode:
    def __init__(self, constant: bool = True):
        self._constant = constant

    def isConstant(self):
        return self._constant


class _FakeOp:
    def __init__(self, mnemonic="RETURN", inputs=None):
        self._mnemonic = mnemonic
        self._inputs = list(inputs if inputs is not None else [_FakeVarnode(True)])

    def getMnemonic(self):
        return self._mnemonic

    def getNumInputs(self):
        return len(self._inputs)

    def getInput(self, index):
        return self._inputs[index]


class _FakeIterator:
    def __init__(self, ops):
        self._ops = list(ops)

    def hasNext(self):
        return bool(self._ops)

    def next(self):
        return self._ops.pop(0)


class _FakeBlock:
    def __init__(self, ops):
        self._ops = list(ops)

    def getIterator(self):
        return _FakeIterator(self._ops)


class _FakeHighFunction:
    def __init__(self, ops):
        self._ops = list(ops)

    def getBasicBlocks(self):
        return [_FakeBlock(self._ops)]


def _placeholder_high():
    """Ghidra が external placeholder に対して返す形（定数入力だけの RETURN 1 個）。"""
    return _FakeHighFunction([_FakeOp("RETURN", [_FakeVarnode(True)])])


class _FakeFunction:
    def __init__(self, name, entry, *, external=False, thunk=False, thunked=None):
        self._name = name
        self._entry = entry
        self._external = external
        self._thunk = thunk
        self._thunked = thunked

    def getName(self):
        return self._name

    def getEntryPoint(self):
        return self._entry

    def isExternal(self):
        return self._external

    def isThunk(self):
        return self._thunk

    def getThunkedFunction(self, _recursive):
        return self._thunked


def _external_placeholder():
    """external へ解決される thunk（``log`` 等の PLT/undefined 記号）。"""
    return _FakeFunction(
        "log", 0x401100, thunk=True, thunked=_FakeFunction("log", 0x501100, external=True)
    )


def _internal_callee():
    return _FakeFunction("helper", 0x401200)


def _unresolved_thunk():
    return _FakeFunction("mystery", 0x401300, thunk=True, thunked=None)


class _FakeFunctionManager:
    def __init__(self, functions):
        self._by_addr = {func.getEntryPoint(): func for func in functions}
        self._by_name = {func.getName(): func for func in functions}

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
        self._function_manager = _FakeFunctionManager(functions)
        self._program_id = program_id

    def getFunctionManager(self):
        return self._function_manager

    def getAddressFactory(self):
        return _FakeAddressFactory()

    def getUniqueProgramID(self):
        return self._program_id

    def startTransaction(self, description):
        return 1

    def endTransaction(self, tx_id, commit):
        return None


def _analyzer(function):
    return ReturnAnalyzer(program=_FakeProgram([function]), debug=False, binary_id="B1")


def _completed_results(high=None):
    results = Mock()
    results.getHighFunction.return_value = high if high is not None else _placeholder_high()
    return results


def _analysis(function, scope_key, *, binary_id="B1", parameter_count=1, note="placeholder"):
    parameters = [
        {"name": f"param_{index}", "index": index, "size": 8}
        for index in range(parameter_count)
    ]
    return FunctionReturnAnalysis(
        function_name=str(function.getName()),
        entry_point=hex(function.getEntryPoint()),
        parameters=parameters,
        returns=[],
        analysis_scope_key=scope_key,
        binary_id=binary_id,
        analysis_notes=[note],
    )


def _install_analysis_loop(analyzer, function, *, analysis_factory=None):
    """``_impl_analyze_function`` の「cache → 再利用 → 解析 → cache 保存」だけを再現する。

    Ghidra を要らなくしたうえで、再利用の判断と cache 書き込みは production と同じ
    関数を通す。束縛値が無い解析を generic ``_function_cache_key`` にも保存するのも
    production と同じ（PR-B が作る束縛ゼロ解析はこの別名を持つ）。
    返り値は「実際に解析した scope key」の記録。
    """

    performed = []
    reuse = analyzer._reuse_unbound_placeholder_analysis
    factory = analysis_factory or (lambda key: _analysis(function, key))

    def analyze_function(
        target,
        timeout=60,
        active_functions=None,
        bound_parameter_values=None,
        bound_parameter_storage_values=None,
    ):
        bound_values = analyzer._normalize_bound_parameter_values(bound_parameter_values)
        bound_storage = analyzer._normalize_bound_parameter_storage_values(
            bound_parameter_storage_values
        )
        scope_key = analyzer._analysis_scope_key(target, bound_values, bound_storage)
        cached = analyzer._call_analysis_cache.get(scope_key)
        if cached is not None:
            return cached
        reused = reuse(
            target,
            CallTargetRef.from_function(target),
            scope_key,
            bound_values,
            bound_storage,
            timeout,
            active_functions,
        )
        if reused is not None:
            return reused
        performed.append(scope_key)
        analysis = factory(scope_key)
        analyzer._call_analysis_cache[scope_key] = analysis
        generic_key = analyzer._function_cache_key(target)
        if generic_key is not None and not bound_values:
            analyzer._call_analysis_cache[generic_key] = analysis
        return analysis

    analyzer.analyze_function = analyze_function
    return performed


def _bound(index_value, storage_value=None):
    values = {0: Expression.constant(index_value, 8)}
    storage = {("register_storage", "x0"): Expression.constant(storage_value or index_value, 8)}
    return values, storage


# ------------------------------------------------------- static body predicate


def test_a_bare_return_placeholder_is_treated_as_having_no_body():
    assert placeholder_body_ineligibility_reason(_placeholder_high()) is None
    # op が 1 つも無い HighFunction も本体不在。
    assert placeholder_body_ineligibility_reason(_FakeHighFunction([])) is None


def test_a_return_that_carries_a_value_is_not_a_placeholder():
    high = _FakeHighFunction([_FakeOp("RETURN", [_FakeVarnode(True), _FakeVarnode(False)])])
    assert placeholder_body_ineligibility_reason(high) == "pcode_body_present"


def test_any_other_pcode_op_means_the_callee_has_a_body():
    high = _FakeHighFunction([_FakeOp("COPY", [_FakeVarnode(True)]), _FakeOp("RETURN")])
    assert placeholder_body_ineligibility_reason(high) == "pcode_body_present"


def test_the_body_predicate_fails_closed_when_the_op_stream_is_unreadable():
    assert placeholder_body_ineligibility_reason(None) == "high_function_missing"

    class _Broken:
        def getBasicBlocks(self):
            raise RuntimeError("boom")

    assert placeholder_body_ineligibility_reason(_Broken()) == "pcode_body_unreadable"

    class _NonBoolVarnode:
        def isConstant(self):
            return 1  # not an exact bool

    high = _FakeHighFunction([_FakeOp("RETURN", [_NonBoolVarnode()])])
    assert placeholder_body_ineligibility_reason(high) == "pcode_body_unreadable"


# ------------------------------------------------------------------- verdicts


def test_an_internal_callee_is_never_eligible_and_is_not_decompiled_for_it():
    function = _internal_callee()
    analyzer = _analyzer(function)
    with patch.object(analyzer, "_decompile_function") as decompile:
        verdict = analyzer._callee_unbound_reuse_verdict(function, "function:helper")
    assert verdict.eligible is False
    assert verdict.reason == "callee_is_internal"
    assert decompile.call_count == 0


def test_an_ambiguous_external_resolution_is_never_eligible():
    function = _unresolved_thunk()
    analyzer = _analyzer(function)
    with patch.object(analyzer, "_decompile_function") as decompile:
        verdict = analyzer._callee_unbound_reuse_verdict(function, "function:mystery")
    assert verdict.eligible is False
    assert verdict.reason == "external_resolution_ambiguous"
    assert verdict.resolution_reason == "thunk_target_unresolved"
    assert decompile.call_count == 0


def test_an_incomplete_decompile_is_never_eligible():
    function = _external_placeholder()
    analyzer = _analyzer(function)
    with patch.object(analyzer, "_decompile_function", return_value=None):
        verdict = analyzer._callee_unbound_reuse_verdict(function, "function:log")
    assert verdict.eligible is False
    assert verdict.reason == "decompile_incomplete"


def test_a_missing_high_function_is_never_eligible():
    function = _external_placeholder()
    analyzer = _analyzer(function)
    results = Mock()
    results.getHighFunction.return_value = None
    with patch.object(analyzer, "_decompile_function", return_value=results):
        verdict = analyzer._callee_unbound_reuse_verdict(function, "function:log")
    assert verdict.eligible is False
    assert verdict.reason == "high_function_missing"


def test_the_verdict_is_decided_once_per_callee_and_dropped_on_program_mutation():
    function = _external_placeholder()
    analyzer = _analyzer(function)
    with patch.object(
        analyzer, "_decompile_function", return_value=_completed_results()
    ) as decompile:
        first = analyzer._callee_unbound_reuse_verdict(function, "function:log")
        second = analyzer._callee_unbound_reuse_verdict(function, "function:log")
        assert first is second
        assert decompile.call_count == 1

        # program を書き換えたら decompile 由来の判定は捨てて取り直す。
        with analyzer._program_transaction("retype"):
            pass
        analyzer._callee_unbound_reuse_verdict(function, "function:log")
        assert decompile.call_count == 2


# --------------------------------------------------------------------- reuse


def test_an_eligible_external_is_analyzed_once_for_different_bound_arguments():
    function = _external_placeholder()
    analyzer = _analyzer(function)
    performed = _install_analysis_loop(analyzer, function)
    with patch.object(analyzer, "_decompile_function", return_value=_completed_results()):
        first_values, first_storage = _bound(7)
        second_values, second_storage = _bound(9)
        first = analyzer.analyze_function(
            function,
            bound_parameter_values=first_values,
            bound_parameter_storage_values=first_storage,
        )
        second = analyzer.analyze_function(
            function,
            bound_parameter_values=second_values,
            bound_parameter_storage_values=second_storage,
        )

    # 実際に走った解析は束縛ゼロの 1 回だけ。
    assert len(performed) == 1
    assert performed[0][2] == () and performed[0][3] == ()
    diagnostics = analyzer.callee_unbound_reuse_diagnostics()
    assert diagnostics["reuses"] == 2
    assert diagnostics["unbound_analyses"] == 1
    assert diagnostics["verdicts"] == {"eligible_external_placeholder": 1}
    assert diagnostics["shadow_comparisons"] == 0
    row = diagnostics["targets"][0]
    assert row["target"] == "function:log@0x401100"
    assert row["eligible"] is True and row["reuses"] == 2

    # 下流は「要求された scope で解析した結果」として扱えなければならない。
    assert first.analysis_scope_key == analyzer._analysis_scope_key(
        function, first_values, first_storage
    )
    assert second.analysis_scope_key == analyzer._analysis_scope_key(
        function, second_values, second_storage
    )
    assert first.analysis_scope_key != second.analysis_scope_key


def test_the_reused_view_shares_no_mutable_state_with_the_unbound_entry():
    function = _external_placeholder()
    analyzer = _analyzer(function)
    _install_analysis_loop(analyzer, function)
    with patch.object(analyzer, "_decompile_function", return_value=_completed_results()):
        values, storage = _bound(7)
        view = analyzer.analyze_function(
            function,
            bound_parameter_values=values,
            bound_parameter_storage_values=storage,
        )
    unbound_key = analyzer._analysis_scope_key(function)
    unbound = analyzer._call_analysis_cache[unbound_key]

    assert view is not unbound
    assert view.parameters is not unbound.parameters
    assert view.analysis_notes is not unbound.analysis_notes
    view.parameters[0]["name"] = "mutated"
    view.analysis_notes.append("mutated")
    assert unbound.parameters[0]["name"] == "param_0"
    assert unbound.analysis_notes == ["placeholder"]


def test_a_bound_analysis_never_lands_in_the_unbound_entry():
    function = _external_placeholder()
    analyzer = _analyzer(function)
    _install_analysis_loop(analyzer, function)
    with patch.object(analyzer, "_decompile_function", return_value=_completed_results()):
        values, storage = _bound(7)
        analyzer.analyze_function(
            function,
            bound_parameter_values=values,
            bound_parameter_storage_values=storage,
        )
        # storage 束縛だけの要求も同じ束縛ゼロ entry から満たされる。
        analyzer.analyze_function(
            function, bound_parameter_storage_values=storage
        )

    unbound_key = analyzer._analysis_scope_key(function)
    unbound = analyzer._call_analysis_cache[unbound_key]
    assert unbound.analysis_scope_key == unbound_key
    assert unbound.analysis_scope_key[2] == () and unbound.analysis_scope_key[3] == ()

    # 束縛付きの結果は要求された scope key にだけ入る。generic ``_function_cache_key``
    # には既存規則どおり束縛ゼロ解析だけが入り、storage 束縛付きの結果は混入しない。
    generic_key = analyzer._function_cache_key(function)
    assert analyzer._call_analysis_cache[generic_key] is unbound
    for key, entry in analyzer._call_analysis_cache.items():
        if key == generic_key:
            continue
        assert key[0] == "analysis_scope"
        assert entry.analysis_scope_key == key


def test_an_internal_callee_keeps_the_bound_sensitive_path():
    function = _internal_callee()
    analyzer = _analyzer(function)
    performed = _install_analysis_loop(analyzer, function)
    with patch.object(analyzer, "_decompile_function", return_value=_completed_results()):
        for value in (7, 9):
            values, storage = _bound(value)
            analyzer.analyze_function(
                function,
                bound_parameter_values=values,
                bound_parameter_storage_values=storage,
            )
    assert len(performed) == 2
    assert analyzer.callee_unbound_reuse_diagnostics()["reuses"] == 0


def test_a_callee_with_a_pcode_body_keeps_the_bound_sensitive_path():
    function = _external_placeholder()
    analyzer = _analyzer(function)
    performed = _install_analysis_loop(analyzer, function)
    body = _FakeHighFunction([_FakeOp("INT_ADD", [_FakeVarnode(False)]), _FakeOp("RETURN")])
    with patch.object(
        analyzer, "_decompile_function", return_value=_completed_results(body)
    ):
        for value in (7, 9):
            values, storage = _bound(value)
            analyzer.analyze_function(
                function,
                bound_parameter_values=values,
                bound_parameter_storage_values=storage,
            )
    assert len(performed) == 2
    diagnostics = analyzer.callee_unbound_reuse_diagnostics()
    assert diagnostics["verdicts"] == {"pcode_body_present": 1}
    assert diagnostics["reuses"] == 0


def test_an_unresolved_thunk_keeps_the_bound_sensitive_path():
    function = _unresolved_thunk()
    analyzer = _analyzer(function)
    performed = _install_analysis_loop(analyzer, function)
    with patch.object(analyzer, "_decompile_function", return_value=_completed_results()):
        for value in (7, 9):
            values, storage = _bound(value)
            analyzer.analyze_function(
                function,
                bound_parameter_values=values,
                bound_parameter_storage_values=storage,
            )
    assert len(performed) == 2
    assert analyzer.callee_unbound_reuse_diagnostics()["verdicts"] == {
        "external_resolution_ambiguous": 1
    }


def test_reuse_can_be_switched_off_by_configuration():
    function = _external_placeholder()
    analyzer = _analyzer(function)
    performed = _install_analysis_loop(analyzer, function)
    with patch.object(settings, "CALLEE_UNBOUND_REUSE_ENABLED", False):
        with patch.object(analyzer, "_decompile_function", return_value=_completed_results()):
            for value in (7, 9):
                values, storage = _bound(value)
                analyzer.analyze_function(
                    function,
                    bound_parameter_values=values,
                    bound_parameter_storage_values=storage,
                )
    assert len(performed) == 2


def _generation_factory(function, generation):
    """世代を note に刻む analysis factory（mutation 前後の object を区別する）。"""

    def factory(scope_key):
        return _analysis(function, scope_key, note=f"gen{generation[0]}")

    return factory


def test_a_bound_view_is_not_served_from_the_cache_after_a_program_mutation():
    """Program 変更後は、変更前に materialize した束縛 view を返さない。"""
    function = _external_placeholder()
    analyzer = _analyzer(function)
    generation = [1]
    performed = _install_analysis_loop(
        analyzer, function, analysis_factory=_generation_factory(function, generation)
    )
    values, storage = _bound(7)
    with patch.object(
        analyzer, "_decompile_function", return_value=_completed_results()
    ) as decompile:
        before = analyzer.analyze_function(
            function,
            bound_parameter_values=values,
            bound_parameter_storage_values=storage,
        )
        view_key = analyzer._analysis_scope_key(function, values, storage)
        assert analyzer._call_analysis_cache[view_key] is before
        assert decompile.call_count == 1 and len(performed) == 1

        with analyzer._program_transaction("retype"):
            pass

        # 変更前の view は cache から消えている（先に cache が返してしまわない）。
        assert view_key not in analyzer._call_analysis_cache

        generation[0] = 2
        after = analyzer.analyze_function(
            function,
            bound_parameter_values=values,
            bound_parameter_storage_values=storage,
        )

    assert after is not before
    assert after.analysis_notes == ["gen2"]
    # 適格判定も束縛ゼロ解析も fresh にやり直している。
    assert decompile.call_count == 2
    assert len(performed) == 2

    diagnostics = analyzer.callee_unbound_reuse_diagnostics()
    assert diagnostics["invalidations"] == 1
    # 束縛ゼロ entry・その generic 別名・束縛 view の 3 件。
    assert diagnostics["evicted_cache_entries"] == 3


def test_the_unbound_entry_is_not_used_as_reuse_authority_after_a_mutation():
    """変更前の束縛ゼロ解析を、変更後の再利用の根拠にしない。"""
    function = _external_placeholder()
    analyzer = _analyzer(function)
    generation = [1]
    _install_analysis_loop(
        analyzer, function, analysis_factory=_generation_factory(function, generation)
    )
    unbound_key = analyzer._analysis_scope_key(function)
    with patch.object(analyzer, "_decompile_function", return_value=_completed_results()):
        first_values, first_storage = _bound(7)
        analyzer.analyze_function(
            function,
            bound_parameter_values=first_values,
            bound_parameter_storage_values=first_storage,
        )
        stale_unbound = analyzer._call_analysis_cache[unbound_key]

        with analyzer._program_transaction("retype"):
            pass
        assert unbound_key not in analyzer._call_analysis_cache

        generation[0] = 2
        # 別の束縛 scope から要求しても、根拠は取り直した束縛ゼロ解析になる。
        second_values, second_storage = _bound(9)
        reused = analyzer.analyze_function(
            function,
            bound_parameter_values=second_values,
            bound_parameter_storage_values=second_storage,
        )

    fresh_unbound = analyzer._call_analysis_cache[unbound_key]
    assert fresh_unbound is not stale_unbound
    assert fresh_unbound.analysis_notes == ["gen2"]
    assert reused.analysis_notes == ["gen2"]


def test_the_generic_alias_of_the_unbound_analysis_is_dropped_by_a_mutation():
    """束縛ゼロ解析を指す generic ``_function_cache_key`` の別名も残さない。"""
    function = _external_placeholder()
    analyzer = _analyzer(function)
    _install_analysis_loop(analyzer, function)
    generic_key = analyzer._function_cache_key(function)
    with patch.object(analyzer, "_decompile_function", return_value=_completed_results()):
        values, storage = _bound(7)
        analyzer.analyze_function(
            function,
            bound_parameter_values=values,
            bound_parameter_storage_values=storage,
        )
        unbound = analyzer._call_analysis_cache[analyzer._analysis_scope_key(function)]
        # 既存規則どおり、束縛ゼロ解析は generic 別名にも入っている。
        assert analyzer._call_analysis_cache[generic_key] is unbound

        with analyzer._program_transaction("retype"):
            pass

    assert generic_key not in analyzer._call_analysis_cache


def test_a_mutation_only_drops_what_the_reuse_path_owns():
    """再利用が所有していない cache entry は巻き添えにしない。"""
    function = _external_placeholder()
    other = _internal_callee()
    analyzer = ReturnAnalyzer(
        program=_FakeProgram([function, other]), debug=False, binary_id="B1"
    )
    _install_analysis_loop(analyzer, function)
    with patch.object(analyzer, "_decompile_function", return_value=_completed_results()):
        values, storage = _bound(7)
        analyzer.analyze_function(
            function,
            bound_parameter_values=values,
            bound_parameter_storage_values=storage,
        )
        view_key = analyzer._analysis_scope_key(function, values, storage)

        # 無関係な entry: 別 callee の scope key / 別 callee の generic key。
        other_scope_key = analyzer._analysis_scope_key(other)
        other_generic_key = analyzer._function_cache_key(other)
        other_analysis = _analysis(other, other_scope_key, note="unrelated")
        analyzer._call_analysis_cache[other_scope_key] = other_analysis
        analyzer._call_analysis_cache[other_generic_key] = other_analysis
        # 再利用が置いた key を別経路が上書きした場合も、それは再利用の authority では
        # ないので落とさない（その entry の寿命は従来どおり）。
        replaced = _analysis(function, view_key, note="written-by-another-path")
        analyzer._call_analysis_cache[view_key] = replaced

        with analyzer._program_transaction("retype"):
            pass

    assert analyzer._call_analysis_cache[other_scope_key] is other_analysis
    assert analyzer._call_analysis_cache[other_generic_key] is other_analysis
    assert analyzer._call_analysis_cache[view_key] is replaced


# -------------------------------------------------------------------- shadow


def test_shadow_validation_adopts_the_reused_view_when_the_projections_match():
    function = _external_placeholder()
    analyzer = _analyzer(function)
    performed = _install_analysis_loop(analyzer, function)
    with patch.object(settings, "CALLEE_UNBOUND_REUSE_SHADOW", True):
        with patch.object(analyzer, "_decompile_function", return_value=_completed_results()):
            values, storage = _bound(7)
            result = analyzer.analyze_function(
                function,
                bound_parameter_values=values,
                bound_parameter_storage_values=storage,
            )

    # shadow 中は従来解析も走るので削減は起きない（束縛ゼロ + bound-sensitive）。
    assert len(performed) == 2
    diagnostics = analyzer.callee_unbound_reuse_diagnostics()
    assert diagnostics["shadow_comparisons"] == 1
    assert diagnostics["shadow_mismatches"] == 0
    assert diagnostics["shadow_mismatch_targets"] == []
    assert result.analysis_notes == ["placeholder"]


def test_shadow_mismatch_keeps_the_bound_sensitive_result_and_records_it():
    function = _external_placeholder()
    analyzer = _analyzer(function)

    def factory(scope_key):
        # 束縛付き解析だけ内容が違う（本来起こらないはずの差を作る）。
        note = "bound-sensitive" if scope_key[2] or scope_key[3] else "placeholder"
        return _analysis(function, scope_key, note=note)

    _install_analysis_loop(analyzer, function, analysis_factory=factory)
    with patch.object(settings, "CALLEE_UNBOUND_REUSE_SHADOW", True):
        with patch.object(analyzer, "_decompile_function", return_value=_completed_results()):
            values, storage = _bound(7)
            result = analyzer.analyze_function(
                function,
                bound_parameter_values=values,
                bound_parameter_storage_values=storage,
            )

    assert result.analysis_notes == ["bound-sensitive"]
    diagnostics = analyzer.callee_unbound_reuse_diagnostics()
    assert diagnostics["shadow_comparisons"] == 1
    assert diagnostics["shadow_mismatches"] == 1
    assert diagnostics["shadow_mismatch_targets"] == ["function:log@0x401100"]
    assert diagnostics["reuses"] == 0


def test_shadow_comparison_requires_the_same_binary_and_callee():
    function = _external_placeholder()
    key = ("analysis_scope", ("function", 7, 0x401100), (), ())
    left = _analysis(function, key, binary_id="B1")
    right = _analysis(function, key, binary_id="B2")
    assert shadow_results_match(left, left) is True
    # binary_id は比較から外さない。
    assert shadow_results_match(left, right) is False
    assert shadow_results_match(left, None) is False
    other = _analysis(_internal_callee(), key, binary_id="B1")
    assert shadow_results_match(left, other) is False


# --------------------------------------------------------------- diagnostics


def test_reuse_failures_and_diagnostics_failures_never_break_the_analysis():
    function = _external_placeholder()
    analyzer = _analyzer(function)
    performed = _install_analysis_loop(analyzer, function)
    broken = Mock()
    broken.record_verdict.side_effect = RuntimeError("boom")
    analyzer._callee_unbound_reuse_stats = broken
    with patch.object(analyzer, "_decompile_function", return_value=_completed_results()):
        values, storage = _bound(7)
        analysis = analyzer.analyze_function(
            function,
            bound_parameter_values=values,
            bound_parameter_storage_values=storage,
        )
    # 再利用が壊れても従来経路で解析は完了する。
    assert analysis is not None
    assert len(performed) == 1

    failing = Mock()
    failing.snapshot.side_effect = RuntimeError("boom")
    analyzer._callee_unbound_reuse_stats = failing
    assert "error" in analyzer.callee_unbound_reuse_diagnostics()


def test_analyze_function_consults_the_reuse_hook_before_decompiling():
    """production の ``analyze_function`` が hook を通ることを固定する。"""
    function = _external_placeholder()
    analyzer = _analyzer(function)
    sentinel = _analysis(function, ("analysis_scope", ("function", 7, 0x401100), (), ()))
    with patch.object(
        analyzer, "_reuse_unbound_placeholder_analysis", return_value=sentinel
    ) as hook:
        with patch(
            "scripts.function_tracer_pcode.ghidra.decompilation_broker.decompile_function"
        ) as decompile:
            values, storage = _bound(7)
            result = analyzer.analyze_function(
                function,
                bound_parameter_values=values,
                bound_parameter_storage_values=storage,
            )
    assert result is sentinel
    assert hook.call_count == 1
    assert decompile.call_count == 0


def test_the_unbound_request_itself_never_enters_the_reuse_path():
    function = _external_placeholder()
    analyzer = _analyzer(function)
    assert (
        reuse_module._impl__reuse_unbound_placeholder_analysis(
            analyzer, function, CallTargetRef.from_function(function),
            ("analysis_scope", ("function", 7, 0x401100), (), ()),
            {}, {}, 60, None,
        )
        is None
    )

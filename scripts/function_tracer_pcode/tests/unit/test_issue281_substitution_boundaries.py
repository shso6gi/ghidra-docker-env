# -*- coding: utf-8 -*-
"""Issue #281: callee の式を caller の引数へ置き換える派生（`substitute_expression`）と、拒否の境界。

`substitute_expression` は callee の node を operand だけ差し替えて作り直す。以前は ref・field を写す複製
（`_clone_expression_with_operands`）で作り、operand が変わっても「この値は callee の parameter N」という
`LocationBaseRef` や `storage_info` が残った（PR-281-A の probe で 96 pair 中 6 回）。今は
`derive_with_operands` が扱いを決め、保てなければ `OperandDerivationRefused` を上げる。

拒否したとき **callee の元の node に戻してはいけない**（caller の文脈では callee の parameter を指す別の値）。
境界は呼び出しの展開・effect の置き換えの単位で、展開をまるごとやめる:

* bounded refinement の `_expand_deferred_call`: `[]`（呼び出し側は展開しない deferred call を使う）。
  展開の evidence は展開が確定してから記録する
* call_recovery の `_resolve_call_expansions` / `_resolve_local_code_target_expansions`: `None`
* `summarize_store_effects`: その呼び出しを effect の分からない呼び出しにする
* 同じ文脈の置き換え（`_apply_condition_parameter_replacements`）: 置き換える前の式（正しい値）

callee の memory 読み出しの順序・location を caller の時間軸へ移すのは置き換えの前の `call_boundary`
（`test_issue281_call_boundary.py`）。拒否は同じ境界で扱う。
"""

from types import SimpleNamespace

import pytest

from scripts.function_tracer_pcode.analysis import bounded_refinement as bounded_refinement_module
from scripts.function_tracer_pcode.analysis.bounded_refinement import BoundedCallRefiner, ExpressionExpansion
from scripts.function_tracer_pcode.analysis.effects.call_boundary import REFUSED_CALLEE_PLACE
from scripts.function_tracer_pcode.analysis.effects.call_argument import (
    _impl__apply_condition_parameter_replacements as apply_condition_parameter_replacements,
)
from scripts.function_tracer_pcode.analysis.effects.expression_forms import _clone_expression_with_operands
from scripts.function_tracer_pcode.analysis.effects.location import _impl_substitute_expression as substitute_expression
from scripts.function_tracer_pcode.analysis.returns import call_recovery
from scripts.function_tracer_pcode.core import (
    Condition,
    Expression,
    ExpressionType,
    LocationBaseRef,
)
from scripts.function_tracer_pcode.core.intrinsics import PTRADD_OPCODE
from scripts.function_tracer_pcode.core.operand_derivation import (
    REFUSED_OPERAND_DEPENDENT_REF,
    REFUSED_OPERAND_DEPENDENT_STORAGE,
    OperandDerivationRefused,
)
from scripts.function_tracer_pcode.core.storage import StorageInfo
from scripts.function_tracer_pcode.tests.conftest import create_mock_analysis


def _callee_param(index: int = 0, size: int = 4) -> Expression:
    return Expression.parameter(f"param_{index + 1}", index=index, data_type="int", size=size)


def _const(value: int, size: int = 4) -> Expression:
    return Expression.constant(value, size=size)


def _caller_argument() -> Expression:
    return Expression.binary_op("INT_ADD", Expression.parameter("x", index=0, size=4), _const(1))


def _analysis(name: str, value: Expression):
    analysis = create_mock_analysis(name)
    analysis.returns[0].value = value
    return analysis


#: callee の parameter の表（置き換えの key は表の parameter から引く）
CALLEE_PARAMETERS = [{"name": "param_1", "index": 0, "data_type": "int"}]


def _replacements(argument: Expression):
    return {("parameter", 0): argument}


def _stale_base_value() -> Expression:
    """tracer が引数の幅の adapter に付ける「この値は callee の parameter 5」の主張（置き換えの対象外の番号）。"""

    return Expression.binary_op("INT_AND", _callee_param(0), _const(0xFF)).clone_with(
        runtime_ref=LocationBaseRef.parameter("param_6", index=5)
    )


# ---------------------------------------------------------------------------
# substitute_expression の派生
# ---------------------------------------------------------------------------


def test_substitution_refuses_a_value_whose_parameter_base_claim_becomes_stale():
    expr = _stale_base_value()
    argument = _caller_argument()
    with pytest.raises(OperandDerivationRefused) as raised:
        substitute_expression(expr, _replacements(argument), CALLEE_PARAMETERS)
    assert raised.value.reason == REFUSED_OPERAND_DEPENDENT_REF
    # 負例（修正前の複製）: operand は caller の値なのに、node は callee の parameter 5 だと主張し続ける
    stale = _clone_expression_with_operands(expr, [argument, _const(0xFF)])
    assert stale.runtime_ref == LocationBaseRef.parameter("param_6", index=5)


def test_substitution_refuses_a_stale_storage_claim():
    stack = StorageInfo(is_register=False, space_name="stack", offset=-8, size=4)
    expr = Expression.unary_op("INT_ZEXT", _callee_param(0)).clone_with(size=8, storage_info=stack)
    with pytest.raises(OperandDerivationRefused) as raised:
        substitute_expression(expr, _replacements(_caller_argument()), CALLEE_PARAMETERS)
    assert raised.value.reason == REFUSED_OPERAND_DEPENDENT_STORAGE


def test_substitution_without_operand_dependent_refs_keeps_fields_and_values():
    argument = _caller_argument()
    expr = Expression.intrinsic(
        "PTRADD", [_callee_param(0, size=8), _const(2, size=8), _const(4, size=8)], size=8, opcode=PTRADD_OPCODE,
    )
    rewritten = substitute_expression(expr, _replacements(argument), CALLEE_PARAMETERS)
    assert rewritten.expr_type is ExpressionType.INTRINSIC
    assert rewritten.opcode == PTRADD_OPCODE
    assert rewritten.operands[1:] == expr.operands[1:]
    # 置き換えた operand は caller の値（幅の調整は builder の契約: ここでは同じ object か、その調整）
    assert rewritten.operands[0] is not expr.operands[0]


def test_a_node_whose_claim_is_replaced_as_a_whole_is_not_refused():
    """主張している parameter 自身が置き換えの対象なら、node ごと caller の値になる（派生しない）。"""

    argument = _caller_argument()
    claimed = Expression.binary_op("INT_AND", _callee_param(0), _const(0xFF)).clone_with(
        runtime_ref=LocationBaseRef.parameter("param_1", index=0)
    )
    rewritten = substitute_expression(claimed, _replacements(argument), CALLEE_PARAMETERS)
    assert rewritten.runtime_ref is not claimed.runtime_ref


def test_same_context_replacement_keeps_the_last_correct_expression_on_refusal():
    original = _stale_base_value()
    condition = Condition(Expression.binary_op("INT_EQUAL", _callee_param(0), _const(3)))
    rewritten = apply_condition_parameter_replacements(original, [condition], CALLEE_PARAMETERS)
    # 同じ文脈の置き換えなので、置き換える前の式は正しい値のまま（派生が拒否されたので置き換えを止める）
    assert rewritten is original


# ---------------------------------------------------------------------------
# bounded refinement の境界: 呼び出しの展開をまるごとやめる
# ---------------------------------------------------------------------------


class _Deferred:
    def __init__(self):
        self.arguments = (_caller_argument(),)
        self.deferred_call_ref = SimpleNamespace(display_name=lambda: "callee")

    def identity_key(self):
        return ("deferred", 1)


def _refiner_with_two_candidates(monkeypatch, refuse_second: bool):
    refiner = BoundedCallRefiner(lambda *_: None, max_unroll=1, max_cases=8, debug=False)
    first = _analysis("callee_a", _callee_param(0))
    second = _analysis("callee_b", _stale_base_value())
    guard = Condition(Expression.binary_op("INT_EQUAL", Expression.parameter("t", index=1, size=4), _const(0)))
    candidates = [("a", [guard], first), ("b", [Condition(guard.expression, negated=True)], second)]
    monkeypatch.setattr(refiner, "_resolve_deferred_call_candidates", lambda deferred: candidates)
    monkeypatch.setattr(refiner, "_analysis_is_fully_argument_specialized", lambda analysis: False)
    monkeypatch.setattr(
        refiner, "_align_deferred_arguments_to_callee", lambda deferred, caller, callee: [_caller_argument()]
    )
    monkeypatch.setattr(bounded_refinement_module, "_call_arguments_width_safe_for_callee_analysis", lambda *a: True)
    monkeypatch.setattr(bounded_refinement_module, "_build_parameter_replacements", lambda params, args: _replacements(args[0]))
    if not refuse_second:
        second.returns[0].value = _callee_param(0)
    evidence = []
    monkeypatch.setattr(
        refiner, "_record_bounded_call_refinement_expansion_evidence", lambda **kwargs: evidence.append(kwargs)
    )
    return refiner, evidence


def test_a_refused_candidate_abandons_the_whole_call_expansion(monkeypatch):
    refiner, evidence = _refiner_with_two_candidates(monkeypatch, refuse_second=True)
    caller = create_mock_analysis("caller")

    expansions = refiner._expand_deferred_call(_Deferred(), caller, 1, set())

    # 1 つ目の target の値だけが残ると、2 つ目の target の枝の値が黙って消える
    assert expansions == []
    # 使わない展開の evidence を残さない
    assert evidence == []
    # callee の parameter の基底を主張する値の node は、置き換えの前に関数境界（`call_boundary`）が拒否する
    # （review 4。以前は置き換えの派生が `operand_dependent_runtime_ref` で拒否していた）
    assert any(
        note.startswith("bounded_call_refinement_operand_derivation_refused:" + REFUSED_CALLEE_PLACE)
        for note in caller.analysis_notes
    )


def test_unrefused_candidates_are_all_expanded_with_their_evidence(monkeypatch):
    refiner, evidence = _refiner_with_two_candidates(monkeypatch, refuse_second=False)
    caller = create_mock_analysis("caller")

    expansions = refiner._expand_deferred_call(_Deferred(), caller, 1, set())

    assert len(expansions) == 2
    assert [item["target_ref"] for item in evidence] == ["a", "b"]


def test_the_expression_falls_back_to_the_unexpanded_call_on_refusal(monkeypatch):
    refiner, _evidence = _refiner_with_two_candidates(monkeypatch, refuse_second=True)
    caller = create_mock_analysis("caller")
    call = Expression(ExpressionType.UNKNOWN, name="deferred_call", size=4)
    monkeypatch.setattr(refiner, "_lookup_deferred_call", lambda expr, analysis: _Deferred())

    expansions = refiner._expand_expression(call, caller, 1, set())

    assert expansions == [ExpressionExpansion(call, [], frozenset())]


# ---------------------------------------------------------------------------
# call_recovery の境界: 展開できない（None）
# ---------------------------------------------------------------------------


def _refusing(*_args, **_kwargs):
    raise OperandDerivationRefused(REFUSED_OPERAND_DEPENDENT_REF, expr_type="BINARY_OP", ref_type="LocationBaseRef")


def test_call_expansion_is_abandoned_when_specialization_is_refused():
    analysis = _analysis("callee", _stale_base_value())
    target_ref = SimpleNamespace(is_code_address=lambda: False, address_offset=None, display_name=lambda: "callee")
    messages = []
    owner = SimpleNamespace(
        _coerce_runtime_target_ref=lambda target: target_ref,
        _target_active_key=lambda ref: None,
        _invoke_get_or_analyze_call_target=lambda *a, **k: analysis,
        _analysis_is_fully_argument_specialized=lambda a: False,
        _specialize_call_analysis=_refusing,
        _debug_print=messages.append,
    )
    result = call_recovery._impl__resolve_call_expansions(owner, "callee", [_caller_argument()], set())
    assert result is None
    assert any("skipped" in message for message in messages)


def test_local_target_expansion_is_abandoned_and_cached_when_specialization_is_refused(monkeypatch):
    from scripts.function_tracer_pcode.ghidra import decompilation_broker

    results = SimpleNamespace(decompileCompleted=lambda: True, getHighFunction=lambda: object())
    monkeypatch.setattr(decompilation_broker, "decompile_within_deadline", lambda *a, **k: results)
    address_space = SimpleNamespace(getAddress=lambda value: value)
    function = SimpleNamespace(getName=lambda: "f")
    program = SimpleNamespace(
        getAddressFactory=lambda: SimpleNamespace(getDefaultAddressSpace=lambda: address_space),
        getFunctionManager=lambda: SimpleNamespace(getFunctionContaining=lambda addr: function),
    )
    tracer = SimpleNamespace()
    owner = SimpleNamespace(
        program=program,
        _local_target_cache={},
        _local_target_cache_key=lambda address, args, call_site=None: ("local", address),
        _collect_parameters=lambda high_function: [],
        _bound_parameter_values_from_call_args=lambda args, params: {},
        _bound_parameter_storage_values_from_call_args=lambda args, params: {},
        _make_tracer=lambda *a, **k: tracer,
        _make_deferred_call_recorder=lambda containing, program_order=None: None,
        _expand_linear_code_target=lambda addr, tracer_, containing: [object()],
        _specialize_local_target_expansions=_refusing,
        _debug_print=lambda message: None,
    )
    result = call_recovery._impl__resolve_local_code_target_expansions(owner, 0x1000, set(), args=[_caller_argument()])
    assert result is None
    assert owner._local_target_cache[("local", 0x1000)] is None

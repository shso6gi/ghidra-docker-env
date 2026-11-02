# -*- coding: utf-8 -*-
"""未宣言の記号を SMT に描かない（Issue #16 の未宣言記号の部分）。

symbol mapping を持つ描画は、query が宣言した入力記号（parameter・extra variable）を mapping に
載せる。mapping に無い VARIABLE / PARAMETER の節点を素の名前で描くと、solver は未宣言の定数として
parse に失敗する（monolithic は ERROR、pairwise は solver ERROR）。描画はそこで型つきの拒否
（``UndeclaredSmtSymbolError``）を送出し、strategy は他の拒否と同じ UNKNOWN にする。

* 宣言を自分で持つ記号（runtime ref の ``declares_variable_symbol``）と、address 文脈で literal に
  描いた節点は対象外。mapping を渡さない描画は今どおり素の名前（この規則の範囲外）。
* monolithic は call projection の lowering を本体の ``try`` より前で行うので、そこでの拒否も
  同じ UNKNOWN と inconclusive な receipt にする（strategy の外へ出すと ERROR になる）。
"""

from __future__ import annotations

from types import SimpleNamespace

import pytest

from scripts.function_tracer_pcode.core.render_smt.sides import with_side

from scripts.function_tracer_pcode.core import (
    AddressValueRef,
    CanonicalLocation,
    Condition,
    Expression,
    LocationBaseRef,
    ReturnInfo,
)
from scripts.function_tracer_pcode.core.render_smt import (
    SMT_SEMANTICS_REFUSALS,
    UndeclaredSmtSymbolError,
    UnsupportedSmtSemanticsError,
)
from scripts.function_tracer_pcode.proof.formula.builder import FormulaBuilder
from scripts.function_tracer_pcode.proof.formula.input_correspondence import build_input_correspondence_set
from scripts.function_tracer_pcode.proof.strategies.monolithic import MonolithicStrategy
from scripts.function_tracer_pcode.smt.parallel import ParallelSolverRunner
from scripts.function_tracer_pcode.tests.unit._publication import published
from scripts.function_tracer_pcode.tests.unit.test_issue185_type_hypothesis_domain import _raw, _descriptor


def _var(name="in_stack_8", **kwargs):
    return Expression.variable(name, size=4, **kwargs)


def _add(left, right):
    return Expression.binary_op("INT_ADD", left, right)


def test_refusal_is_one_of_the_typed_smt_semantics_refusals():
    error = UndeclaredSmtSymbolError(symbol_kind="VARIABLE", symbol="in_stack_8")
    assert isinstance(error, UnsupportedSmtSemanticsError) and isinstance(error, SMT_SEMANTICS_REFUSALS)
    assert error.refusal_target_fields() == ("undeclared_smt_symbol", "VARIABLE", "in_stack_8")


@pytest.mark.parametrize("kind, node", [
    ("VARIABLE", _var()),
    ("PARAMETER", Expression.parameter("param_2", 1, size=4)),
])
def test_a_symbol_missing_from_the_mapping_is_refused(kind, node):
    """修正前は mapping に無い節点を素の名前で描いていた（solver は未宣言の定数で失敗する）。"""

    expr = published(_add(Expression.parameter("param_1", 0, size=4), node))
    with pytest.raises(UndeclaredSmtSymbolError) as caught:
        expr.to_smt(symbol_name_mapping={"param_1": "param_1_1"})
    assert (caught.value.symbol_kind, caught.value.symbol) == (kind, node.name)
    # 条件の中でも同じ。
    condition = published(Condition(Expression.binary_op("INT_EQUAL", node, Expression.constant(0, 4)), False))
    with pytest.raises(UndeclaredSmtSymbolError):
        condition.to_smt(symbol_name_mapping={})


def test_mapped_symbols_and_unmapped_renders_are_unchanged():
    expr = published(_add(Expression.parameter("param_1", 0, size=4), _var()))
    rendered = expr.to_smt(symbol_name_mapping={"param_1": "param_1_1", "in_stack_8": "in_stack_8_1"})
    assert "param_1_1" in rendered and "in_stack_8_1" in rendered
    # mapping を渡さない描画は素の名前のまま（この規則の範囲外）。
    bare = expr.to_smt()
    assert "param_1" in bare and "in_stack_8" in bare


def test_a_symbol_that_declares_itself_is_not_refused():
    location = CanonicalLocation(base_ref=LocationBaseRef.parameter("ptr", index=0), offset=0, size=4)
    node = published(_var("post_ptr", runtime_ref=location))
    # Issue #282: 自前で宣言する記号はその側の状態。左右の query の写像（側つき）では側の記号になり、側の無い写像では
    # 描かない（左右のどちらの状態か分からない）
    assert node.to_smt(symbol_name_mapping=with_side({}, 1)) == node.to_smt() + "_s1"
    with pytest.raises(UndeclaredSmtSymbolError):
        node.to_smt(symbol_name_mapping={})


def _address_variable(name="g_table", *, offset=0x1000):
    return Expression.variable(name, size=8, runtime_ref=AddressValueRef(
        address_offset=offset, display_hint=name, is_initialized=True, can_read=True, can_write=False,
        is_volatile=False,
    ))


def test_only_an_address_rendered_as_a_literal_is_exempt():
    load = published(Expression.memory(_address_variable(), size=4))
    assert "(_ bv4096 " in load.to_smt(symbol_name_mapping=with_side({}, 1))
    # address 文脈でも literal に描けない節点は、宣言が無ければ拒否する。
    with pytest.raises(UndeclaredSmtSymbolError):
        published(Expression.memory(Expression.variable("base", size=8), size=4)).to_smt(symbol_name_mapping=with_side({}, 1))


# --- monolithic: call projection の lowering は本体の try より前 -------------------------------------


def _pair():
    descriptors = [_descriptor("param_1", 4, "int", True)]
    value = Expression.parameter("param_1", 0, data_type="int", size=4)
    return (
        _raw("f", descriptors, [ReturnInfo("0x10", value, [])]),
        _raw("g", descriptors, [ReturnInfo("0x10", value, [])]),
    )


@pytest.mark.parametrize("refusing_step", ["base_context", "call_projection_lowering"])
def test_monolithic_refusal_before_its_main_try_is_unknown_with_an_inconclusive_receipt(monkeypatch, refusing_step):
    """修正前はこの区間の拒否が strategy の外へ出て、pair は ERROR になっていた。"""

    import scripts.function_tracer_pcode.proof.call_effect.preflight as preflight
    import scripts.function_tracer_pcode.proof.monolithic_authority as monolithic_authority
    import scripts.function_tracer_pcode.proof.strategies.monolithic as monolithic

    analysis1, analysis2 = _pair()
    issued = []
    frame = SimpleNamespace(
        prepared=SimpleNamespace(
            analysis1=analysis1,
            analysis2=analysis2,
            input_correspondence=build_input_correspondence_set(analysis1, analysis2),
            surface_digest="surface",
        ),
        comparison_binding=object(),
        projection=SimpleNamespace(semantic_bindings=("certified-call-binding",)),
        production_branch_authority_lease=object(),
        monolithic_execution_authority_lease=object(),
        receipt=None,
    )

    def issue(dispatch_frame, frozen_surface, census, cause):
        issued.append((frozen_surface, census, cause))
        dispatch_frame.receipt = "inconclusive-receipt"

    def refuse(*_args, **_kwargs):
        raise UndeclaredSmtSymbolError(symbol_kind="VARIABLE", symbol="in_stack_8")

    monkeypatch.setattr(preflight, "current_dispatch_depth", lambda: 1)
    monkeypatch.setattr(preflight, "consume_prepared_dispatch_frame", lambda *_args: frame)
    monkeypatch.setattr(preflight, "issue_inconclusive_monolithic_receipts", issue)
    monkeypatch.setattr(monolithic, "comparison_is_current", lambda _binding: True)
    monkeypatch.setattr(monolithic_authority, "freeze_surface", lambda *_args: "frozen")
    monkeypatch.setattr(monolithic_authority, "reconstruct_canonical_census", lambda _surface: "census")
    strategy = MonolithicStrategy(FormulaBuilder(), ParallelSolverRunner(timeout=5))
    if refusing_step == "base_context":
        monkeypatch.setattr(strategy.formula_builder, "build_base_context", refuse)
    else:
        monkeypatch.setattr(preflight, "lower_call_projection_for_case_pair", refuse)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert getattr(result, "error_kind", None) is None
    assert [reason.reason_id for reason in result.unknown_reasons] == ["expression_semantics_unsupported"]
    assert tuple(result.unknown_reasons[0].evidence_refs) == ("undeclared_smt_symbol",)
    assert issued == [("frozen", "census", "VARIABLE in_stack_8 is not declared by the query's symbol mapping")]
    assert result.comparison_execution_receipt == "inconclusive-receipt"

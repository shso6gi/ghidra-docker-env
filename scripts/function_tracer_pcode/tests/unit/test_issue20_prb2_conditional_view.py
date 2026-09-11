# -*- coding: utf-8 -*-
"""Conditional semantic view + CALL/UF infrastructure (Issue #20 PR-20-B2).

B2 は **dormant な基盤**である。ここで固定するのは主に

* conditional view が仮定の下でだけ CALL/UF を導入すること
* 無条件 lane が CALL を従来どおり拒否し続けること
* assumption_set を途中で最小化しないこと
* assumed no-write / normal-return が base analysis へ漏れないこと
* 証明済み引数証拠しか使わず、足りなければ fail closed になること

であり、conditional verdict / receipt / production lane は B3 の責務なので
ここでは扱わない。
"""

from __future__ import annotations

import inspect
import json

import pytest

from scripts.function_tracer_pcode.analysis.effects.external_call_models import (
    ExternalCallEffectPolicy,
)
from scripts.function_tracer_pcode.analysis.effects.pure_function_catalog import (
    catalog_signature_widths,
)
from scripts.function_tracer_pcode.core.analysis import (
    DeferredCallInfo,
    FunctionReturnAnalysis,
    ReturnInfo,
)
from scripts.function_tracer_pcode.core.call_target import CallTargetRef
from scripts.function_tracer_pcode.core.condition import Condition
from scripts.function_tracer_pcode.core.expression import Expression, ExpressionType
from scripts.function_tracer_pcode.core.render_smt import (
    CallDeclarationConflict,
    call_smt_declaration,
    call_smt_declaration_lines,
    collect_call_smt_declarations,
    expression_contains_call,
    expression_contains_unsupported_smt_ops,
)
from scripts.function_tracer_pcode.core.runtime_refs import (
    CallModelCandidateRef,
    DeferredCallRef,
)
from scripts.function_tracer_pcode.proof import conditional_view as view_module
from scripts.function_tracer_pcode.proof.assumptions import (
    AssumptionKind,
    AssumptionPremise,
)
from scripts.function_tracer_pcode.proof.conditional_view import (
    ConditionalSemanticView,
    build_conditional_equivalence_formula,
    create_conditional_view,
    external_callee_spec_premise,
)
from scripts.function_tracer_pcode.proof.formula.builder import (
    CallFormulaUnsupported,
    FormulaBuilder,
)


NO_OBSERVATION = ExternalCallEffectPolicy()


# --- fixtures --------------------------------------------------------------


def _candidate(symbol="log", *, argument_widths=(64,), return_width=64, provider="c99_math_catalog_v1"):
    return CallModelCandidateRef(
        provider=provider,
        canonical_symbol=symbol,
        signature_key=(
            "c99_math_signature_v1",
            symbol,
            tuple(("float", width) for width in argument_widths),
            ("float", return_width),
        ),
        provenance_key=(
            "external_import_provenance_v1",
            "thunk_to_external",
            "<EXTERNAL>",
            (symbol,),
        ),
    )


def _param(name="x", index=0, size=8):
    return Expression.parameter(name, index=index, data_type="double", size=size)


def _deferred(
    sequence,
    *,
    candidate,
    arguments,
    recovery_status="complete",
    entry=0x1000,
):
    target_ref = CallTargetRef.from_name(
        candidate.canonical_symbol if candidate is not None else "opaque",
        program_id=entry,
        entry_offset=entry + sequence,
    )
    return DeferredCallInfo(
        placeholder_name=f"call#{sequence}",
        target_ref=target_ref,
        arguments=list(arguments),
        deferred_call_ref=DeferredCallRef(
            caller_program_id=entry,
            caller_entry_offset=entry,
            target_ref=target_ref,
            sequence=sequence,
        ),
        call_argument_recovery_status=recovery_status,
        call_model_candidate=candidate,
    )


def _analysis(deferred_calls, *, binary_id="binary1", unknown_size=8, entry=0x1000):
    parameters = [{"name": "x", "index": 0, "size": 8, "data_type": "double", "is_signed": True}]
    value = None
    for info in deferred_calls:
        node = Expression.unknown(
            info.placeholder_name, runtime_ref=info.unknown_ref
        ).clone_with(size=unknown_size)
        value = node if value is None else Expression.binary_op("FLOAT_ADD", value, node)
    if value is None:
        value = Expression.constant(0, size=8)
    return FunctionReturnAnalysis(
        function_name="snippet",
        entry_point=hex(entry),
        function_ref=CallTargetRef.from_name("snippet", program_id=entry, entry_offset=entry),
        binary_id=binary_id,
        parameters=parameters,
        returns=[ReturnInfo(address=hex(entry), value=value, conditions=[])],
        return_type="double",
        deferred_calls={
            info.deferred_call_ref.stable_key(): info for info in deferred_calls
        },
    )


def _single_call_analysis(**kwargs):
    candidate = kwargs.pop("candidate", None) or _candidate()
    arguments = kwargs.pop("arguments", None) or [_param()]
    recovery_status = kwargs.pop("recovery_status", "complete")
    info = _deferred(
        1, candidate=candidate, arguments=arguments, recovery_status=recovery_status
    )
    return _analysis([info], **kwargs), info


# --- CALL / UF declarations ------------------------------------------------


def _call(symbol, operands, return_bytes=8):
    return Expression(
        expr_type=ExpressionType.CALL,
        name=symbol,
        operands=list(operands),
        size=return_bytes,
    )


def test_same_symbol_and_widths_declare_the_same_uf():
    left = _call("log", [_param("x")])
    right = _call("log", [_param("y", index=1)])
    assert collect_call_smt_declarations(left) == collect_call_smt_declarations(right)
    assert call_smt_declaration_lines(collect_call_smt_declarations(left)) == [
        "(declare-fun call_log ((_ BitVec 64)) (_ BitVec 64))"
    ]


def test_different_canonical_symbols_declare_different_ufs():
    log_declarations = collect_call_smt_declarations(_call("log", [_param()]))
    exp_declarations = collect_call_smt_declarations(_call("exp", [_param()]))
    assert set(log_declarations) != set(exp_declarations)


def test_conflicting_declaration_for_one_symbol_fails_closed():
    narrow = _call("log", [_param("x", size=4)], return_bytes=4)
    wide = _call("log", [_param("y", index=1, size=8)], return_bytes=8)
    declarations = {}
    collect_call_smt_declarations(narrow, declarations)
    with pytest.raises(CallDeclarationConflict):
        collect_call_smt_declarations(wide, declarations)


def test_non_call_nodes_produce_no_declaration():
    assert call_smt_declaration(_param()) is None
    assert collect_call_smt_declarations(_param()) == {}


def test_declaration_widths_follow_the_inherited_oracle_normalization():
    """幅の正規化規則は condition SMT oracle から引き継いだものと同一。

    conditional view は CALL を作る **前に** catalog の厳密な幅と一致することを
    確認するので、この正規化に寄りかかることはない。
    """
    from scripts.function_tracer_pcode.analysis.condition.smt_oracle import (
        ConditionSMTOracle,
    )

    node = _call("log", [_param("x", size=4)], return_bytes=4)
    assert call_smt_declaration(node) == ConditionSMTOracle._collect_call_declaration(node)
    assert call_smt_declaration(node) == ("call_log", (32,), 32)


def test_condition_oracle_keeps_using_the_shared_declaration_rule():
    """oracle の private helper は共有 helper への委譲になっている。"""
    from scripts.function_tracer_pcode.analysis.condition.smt_oracle import (
        ConditionSMTOracle,
    )

    node = _call("log", [_param()])
    assert ConditionSMTOracle._collect_call_declaration(node) == call_smt_declaration(node)


# --- conditional view construction ----------------------------------------


def test_view_maps_a_candidate_call_to_a_canonical_call_expression():
    analysis, info = _single_call_analysis()
    result = create_conditional_view(analysis, observation_policy=NO_OBSERVATION)
    assert result.constructed, result.refusal_reason
    view = result.view
    assert len(view.call_models) == 1
    model = view.call_models[0]
    assert model.canonical_symbol == "log"
    assert model.uf_symbol == "call_log"
    assert model.argument_widths == (64,)
    assert model.return_width_bits == 64
    assert view.call_declarations == (("call_log", (64,), 64),)

    rendered = view.analysis.returns[0].value
    assert rendered.expr_type == ExpressionType.CALL
    assert rendered.name == "log"
    assert [str(operand) for operand in rendered.operands] == [str(info.arguments[0])]


def test_alias_candidate_reaches_the_same_uf_as_its_canonical_symbol():
    """alias 由来でも canonical symbol が同じなら同じ UF になる。"""
    alias_candidate = _candidate("log")
    alias_candidate = CallModelCandidateRef(
        provider=alias_candidate.provider,
        canonical_symbol="log",
        signature_key=alias_candidate.signature_key,
        provenance_key=(
            "external_import_provenance_v1",
            "thunk_to_external",
            "<EXTERNAL>",
            ("__log_finite",),
        ),
    )
    alias_analysis, _ = _single_call_analysis(candidate=alias_candidate)
    canonical_analysis, _ = _single_call_analysis(candidate=_candidate("log"))

    alias_view = create_conditional_view(alias_analysis, observation_policy=NO_OBSERVATION).view
    canonical_view = create_conditional_view(
        canonical_analysis, observation_policy=NO_OBSERVATION
    ).view
    assert alias_view.call_models[0].uf_identity() == canonical_view.call_models[0].uf_identity()
    assert alias_view.call_declarations == canonical_view.call_declarations
    # provenance が違うので premise は別物のまま（仮定を取り違えない）。
    assert alias_view.assumption_set != canonical_view.assumption_set


def test_different_symbols_produce_different_uf_identities():
    log_analysis, _ = _single_call_analysis(candidate=_candidate("log"))
    exp_analysis, _ = _single_call_analysis(candidate=_candidate("exp"))
    log_view = create_conditional_view(log_analysis, observation_policy=NO_OBSERVATION).view
    exp_view = create_conditional_view(exp_analysis, observation_policy=NO_OBSERVATION).view
    assert log_view.call_models[0].uf_identity() != exp_view.call_models[0].uf_identity()


def test_unobserved_reference_width_takes_the_declared_return_width():
    """参照側が幅を持たない (size 0) のは食い違いではない。

    その場合の戻り幅は callee の宣言 signature が authority なので catalog の幅を
    使う。実バイナリでは deferred-call の UNKNOWN 参照が幅を持たないことが多い。
    """
    analysis, _ = _single_call_analysis(unknown_size=0)
    result = create_conditional_view(analysis, observation_policy=NO_OBSERVATION)
    assert result.constructed, result.refusal_reason
    assert result.view.call_models[0].return_width_bits == 64
    assert result.view.analysis.returns[0].value.size == 8


def test_return_width_mismatch_refuses_the_call():
    analysis, _ = _single_call_analysis(unknown_size=4)
    result = create_conditional_view(analysis, observation_policy=NO_OBSERVATION)
    assert not result.constructed
    assert result.refusal_reason == view_module.VIEW_REFUSED_NO_MAPPED_CALL
    assert [reason for _key, reason in result.call_diagnostics] == [
        view_module.CALL_SKIPPED_RETURN_WIDTH_MISMATCH
    ]


def test_argument_width_mismatch_refuses_the_call():
    analysis, _ = _single_call_analysis(arguments=[_param("x", size=4)])
    result = create_conditional_view(analysis, observation_policy=NO_OBSERVATION)
    assert not result.constructed
    assert [reason for _key, reason in result.call_diagnostics] == [
        view_module.CALL_SKIPPED_ARGUMENT_WIDTH_MISMATCH
    ]


def test_argument_arity_mismatch_refuses_the_call():
    analysis, _ = _single_call_analysis(arguments=[_param(), _param("y", index=1)])
    result = create_conditional_view(analysis, observation_policy=NO_OBSERVATION)
    assert not result.constructed
    assert [reason for _key, reason in result.call_diagnostics] == [
        view_module.CALL_SKIPPED_ARGUMENT_ARITY_MISMATCH
    ]


def test_unusable_catalog_signature_refuses_the_call():
    broken = CallModelCandidateRef(
        provider="c99_math_catalog_v1",
        canonical_symbol="log",
        signature_key=("not_a_signature", "log"),
        provenance_key=("external_import_provenance_v1", "thunk_to_external", "<EXTERNAL>", ("log",)),
    )
    assert catalog_signature_widths(broken.signature_key) is None
    analysis, _ = _single_call_analysis(candidate=broken)
    result = create_conditional_view(analysis, observation_policy=NO_OBSERVATION)
    assert not result.constructed
    assert [reason for _key, reason in result.call_diagnostics] == [
        view_module.CALL_SKIPPED_SIGNATURE_UNUSABLE
    ]


# --- argument soundness ----------------------------------------------------


@pytest.mark.parametrize("status", ["inconclusive", "recoverable_partial"])
def test_unproven_argument_evidence_is_never_promoted(status):
    """PR-20-D が complete と言っていない callsite は写像しない。"""
    analysis, _ = _single_call_analysis(recovery_status=status)
    result = create_conditional_view(analysis, observation_policy=NO_OBSERVATION)
    assert not result.constructed
    assert [reason for _key, reason in result.call_diagnostics] == [
        view_module.CALL_SKIPPED_ARGUMENT_EVIDENCE_UNPROVEN
    ]


def test_partially_proven_calls_map_only_the_proven_ones():
    """1 つが complete、もう 1 つが inconclusive なら前者だけを写像する。"""
    proven = _deferred(1, candidate=_candidate(), arguments=[_param()])
    unproven = _deferred(
        2, candidate=_candidate(), arguments=[_param("y", index=1)], recovery_status="inconclusive"
    )
    analysis = _analysis([proven, unproven])
    result = create_conditional_view(analysis, observation_policy=NO_OBSERVATION)
    assert result.constructed
    assert len(result.view.call_models) == 1
    assert result.view.call_models[0].deferred_call_key == proven.deferred_call_ref.stable_key()
    assert [reason for _key, reason in result.view.unmapped_calls] == [
        view_module.CALL_SKIPPED_ARGUMENT_EVIDENCE_UNPROVEN
    ]
    # 写像しなかった callsite は元の UNKNOWN のまま残る（fail closed）。
    remaining = result.view.analysis.deferred_calls
    assert unproven.deferred_call_ref.stable_key() in remaining
    assert proven.deferred_call_ref.stable_key() not in remaining


def test_same_symbol_with_different_operands_stays_distinct():
    """``log(x)`` と ``log(x + 1)`` を同一化しない。"""
    plain = _deferred(1, candidate=_candidate(), arguments=[_param()])
    shifted_argument = Expression.binary_op("FLOAT_ADD", _param(), Expression.constant(1, size=8))
    shifted = _deferred(2, candidate=_candidate(), arguments=[shifted_argument])
    analysis = _analysis([plain, shifted])
    view = create_conditional_view(analysis, observation_policy=NO_OBSERVATION).view

    calls = []

    def walk(expr):
        if expr is None:
            return
        if expr.expr_type == ExpressionType.CALL:
            calls.append(expr)
        for operand in getattr(expr, "operands", None) or []:
            walk(operand)

    walk(view.analysis.returns[0].value)
    assert len(calls) == 2
    assert {str(call) for call in calls} == {str(calls[0]), str(calls[1])}
    assert str(calls[0]) != str(calls[1])
    # 同じ関数なので UF 宣言は 1 つ。引数が違うだけ。
    assert view.call_declarations == (("call_log", (64,), 64),)


def test_side_specific_fresh_arguments_are_not_coupled_by_the_view():
    """左右の fresh 引数は view を通しても別 symbol のまま。"""
    from scripts.function_tracer_pcode.core.runtime_refs import (
        AbiArgumentSlotRef,
        FreshCallArgumentRef,
        fresh_call_argument_refs_are_side_distinct,
    )

    slot = AbiArgumentSlotRef(ordinal=0, storage_class="register", width_bits=64)
    left_ref = FreshCallArgumentRef(binary_id="binary1", slot=slot)
    right_ref = FreshCallArgumentRef(binary_id="binary2", slot=slot)
    assert fresh_call_argument_refs_are_side_distinct(left_ref, right_ref)

    def _fresh_expression(ref):
        return Expression.unknown(ref.display_name(), runtime_ref=ref).clone_with(size=8)

    left_analysis = _analysis(
        [_deferred(1, candidate=_candidate(), arguments=[_fresh_expression(left_ref)])],
        binary_id="binary1",
    )
    right_analysis = _analysis(
        [_deferred(1, candidate=_candidate(), arguments=[_fresh_expression(right_ref)])],
        binary_id="binary2",
    )
    left_view = create_conditional_view(left_analysis, observation_policy=NO_OBSERVATION).view
    right_view = create_conditional_view(right_analysis, observation_policy=NO_OBSERVATION).view

    left_call = left_view.analysis.returns[0].value
    right_call = right_view.analysis.returns[0].value
    assert left_call.expr_type == ExpressionType.CALL
    left_operand_ref = getattr(left_call.operands[0], "runtime_ref", None)
    right_operand_ref = getattr(right_call.operands[0], "runtime_ref", None)
    assert left_operand_ref.stable_key() != right_operand_ref.stable_key()
    # UF identity は一致するが、それは「同じ関数」であって「同じ引数値」ではない。
    assert left_view.call_models[0].uf_identity() == right_view.call_models[0].uf_identity()


def test_candidate_alone_does_not_assert_callsite_correspondence():
    """view は片側だけを見る。左右の callsite 数が違っても view は独立に立つ。"""
    left = _analysis([_deferred(1, candidate=_candidate(), arguments=[_param()])])
    right = _analysis(
        [
            _deferred(1, candidate=_candidate(), arguments=[_param()]),
            _deferred(2, candidate=_candidate(), arguments=[_param("y", index=1)]),
        ]
    )
    left_view = create_conditional_view(left, observation_policy=NO_OBSERVATION).view
    right_view = create_conditional_view(right, observation_policy=NO_OBSERVATION).view
    assert len(left_view.call_models) == 1
    assert len(right_view.call_models) == 2
    assert left_view.view_key() != right_view.view_key()


# --- assumptions -----------------------------------------------------------


def test_view_carries_an_external_callee_spec_assumption():
    analysis, _ = _single_call_analysis()
    view = create_conditional_view(analysis, observation_policy=NO_OBSERVATION).view
    assert len(view.assumption_set) == 1
    premise = view.assumption_set[0]
    assert type(premise) is AssumptionPremise
    assert premise.kind is AssumptionKind.EXTERNAL_CALLEE_SPEC
    assert premise.subject == "log"
    assert premise.payload_value("canonical_symbol") == "log"
    assert premise.payload_value("no_observable_memory_write") is True
    assert premise.payload_value("returns_normally") is True
    assert premise.payload_value("behaves_as_catalog_specification") is True
    assert premise.payload_value("return_width_bits") == 64
    assert premise.payload_value("argument_width_bits") == (64,)


def test_assumption_set_is_deterministic_and_deduplicated():
    first = _deferred(1, candidate=_candidate("log"), arguments=[_param()])
    second = _deferred(2, candidate=_candidate("log"), arguments=[_param("y", index=1)])
    third = _deferred(3, candidate=_candidate("exp"), arguments=[_param("z", index=2)])
    view = create_conditional_view(
        _analysis([first, second, third]), observation_policy=NO_OBSERVATION
    ).view
    # 同じ symbol の 2 callsite は 1 premise に dedup、順序は premise key 順。
    assert len(view.call_models) == 3
    subjects = [premise.subject for premise in view.assumption_set]
    assert subjects == ["exp", "log"]

    again = create_conditional_view(
        _analysis([third, second, first]), observation_policy=NO_OBSERVATION
    ).view
    assert again.assumption_set == view.assumption_set


def test_assumption_set_is_not_minimized_when_a_uf_disappears():
    """UF が式から消えても premise は落とさない（正本 §4.3.6）。"""
    analysis, _ = _single_call_analysis()
    view = create_conditional_view(analysis, observation_policy=NO_OBSERVATION).view
    assert view.assumption_set

    simplified = ConditionalSemanticView(
        binary_id=view.binary_id,
        view_builder_version=view.view_builder_version,
        call_models=view.call_models,
        assumption_set=view.assumption_set,
        call_declarations=(),
        analysis=view.analysis,
    )
    # 宣言が 1 つも残らない（= UF が formula から消えた）状態でも、
    # 依存する premise の集合は変わらない。
    assert simplified.assumption_set == view.assumption_set
    with pytest.raises(ValueError):
        ConditionalSemanticView(
            binary_id=view.binary_id,
            view_builder_version=view.view_builder_version,
            call_models=view.call_models,
            assumption_set=(),
            call_declarations=view.call_declarations,
            analysis=view.analysis,
        )


def test_external_callee_spec_premise_requires_a_candidate():
    with pytest.raises(TypeError):
        external_callee_spec_premise(
            {"canonical_symbol": "log"}, argument_widths=(64,), return_width_bits=64
        )


# --- base analysis must not be polluted ------------------------------------


def test_base_analysis_is_unchanged_by_view_creation():
    analysis, info = _single_call_analysis()
    before = json.dumps(analysis.to_dict(), sort_keys=True, default=repr)
    effect_summary_before = analysis.effect_summary

    result = create_conditional_view(analysis, observation_policy=NO_OBSERVATION)
    assert result.constructed

    after = json.dumps(analysis.to_dict(), sort_keys=True, default=repr)
    assert after == before
    assert analysis.effect_summary is effect_summary_before
    # deferred call も effect_class もそのまま。
    assert info.deferred_call_ref.stable_key() in analysis.deferred_calls
    assert info.effect_class == "unknown_effect"
    assert analysis.returns[0].value.expr_type != ExpressionType.CALL


def test_view_does_not_write_assumptions_into_the_effect_summary():
    analysis, _ = _single_call_analysis()
    view = create_conditional_view(analysis, observation_policy=NO_OBSERVATION).view
    # view は base と effect_summary を共有するので、そこへ書き込んでいないこと
    # （= 仮定が analysis fact へ昇格していないこと）を直接確認する。
    assert view.analysis.effect_summary is analysis.effect_summary
    payload = json.dumps(view.analysis.to_dict(), sort_keys=True, default=repr)
    for forbidden in ("EXTERNAL_CALLEE_SPEC", "no_observable_memory_write", "returns_normally"):
        assert forbidden not in payload


def test_analysis_layer_does_not_import_the_assumption_contract():
    import ast
    from pathlib import Path

    analysis_root = Path(view_module.__file__).resolve().parents[1] / "analysis"
    offenders = []
    for path in analysis_root.rglob("*.py"):
        tree = ast.parse(path.read_text(encoding="utf-8"))
        for node in ast.walk(tree):
            module = None
            if isinstance(node, ast.ImportFrom):
                module = node.module
            elif isinstance(node, ast.Import):
                module = ",".join(alias.name for alias in node.names)
            if module and ("proof.assumptions" in module or "proof.conditional_view" in module):
                offenders.append(str(path))
    assert not offenders


# --- observation boundary --------------------------------------------------


@pytest.mark.parametrize(
    "policy",
    [
        ExternalCallEffectPolicy(observe_errno=True),
        ExternalCallEffectPolicy(observe_fenv=True),
        ExternalCallEffectPolicy(observe_errno=True, observe_fenv=True),
    ],
)
def test_observation_modes_refuse_the_conditional_view(policy):
    analysis, _ = _single_call_analysis()
    result = create_conditional_view(analysis, observation_policy=policy)
    assert not result.constructed
    assert result.refusal_reason == view_module.VIEW_REFUSED_OBSERVATION_ACTIVE


def test_missing_observation_policy_refuses_the_conditional_view():
    analysis, _ = _single_call_analysis()
    result = create_conditional_view(analysis, observation_policy=None)
    assert not result.constructed
    assert result.refusal_reason == view_module.VIEW_REFUSED_OBSERVATION_POLICY_UNAVAILABLE


def test_analysis_without_candidate_calls_has_no_view():
    analysis = _analysis([_deferred(1, candidate=None, arguments=[_param()])])
    result = create_conditional_view(analysis, observation_policy=NO_OBSERVATION)
    assert not result.constructed
    assert result.refusal_reason == view_module.VIEW_REFUSED_NO_MAPPED_CALL
    assert [reason for _key, reason in result.call_diagnostics] == [
        view_module.CALL_SKIPPED_NO_CANDIDATE
    ]


# --- lane separation -------------------------------------------------------


def test_unconditional_expression_gate_still_rejects_call():
    call_expr = _call("log", [_param()])
    assert expression_contains_unsupported_smt_ops(call_expr) is True
    assert expression_contains_unsupported_smt_ops(call_expr, allow_call=True) is False


def test_call_presence_predicate_matches_the_allow_call_difference():
    call_expr = _call("log", [_param()])
    plain = Expression.binary_op("FLOAT_ADD", _param(), Expression.constant(1, size=8))
    assert expression_contains_call(call_expr) is True
    assert expression_contains_call(plain) is False
    # allow_call が作る差分と同じものを見ている。
    assert (
        expression_contains_unsupported_smt_ops(call_expr, allow_call=False)
        and not expression_contains_unsupported_smt_ops(call_expr, allow_call=True)
    )


def test_unconditional_builder_rejects_a_call_analysis_end_to_end():
    """宣言を出さないだけでなく、formula 構築そのものを fail closed にする。"""
    analysis, _ = _single_call_analysis()
    view = create_conditional_view(analysis, observation_policy=NO_OBSERVATION).view
    builder = FormulaBuilder()
    assert builder.allow_call is False
    with pytest.raises(CallFormulaUnsupported):
        builder.build_equivalence_formula_extended(view.analysis, view.analysis)
    with pytest.raises(CallFormulaUnsupported):
        builder.build_base_context(view.analysis, view.analysis)
    with pytest.raises(CallFormulaUnsupported):
        builder._collect_call_smt_declarations(view.analysis)


def test_unconditional_builder_rejects_a_call_in_a_guard():
    analysis, info = _single_call_analysis()
    view = create_conditional_view(analysis, observation_policy=NO_OBSERVATION).view
    call_expr = view.analysis.returns[0].value
    guarded = view.analysis.semantic_successor(
        returns=[
            ReturnInfo(
                address="0x1000",
                value=Expression.constant(0, size=8),
                conditions=[Condition(call_expr, False)],
            )
        ]
    )
    with pytest.raises(CallFormulaUnsupported):
        FormulaBuilder().build_equivalence_formula_extended(guarded, guarded)


def test_conditional_builder_declares_the_call_uf():
    builder = FormulaBuilder(allow_call=True)
    analysis, _ = _single_call_analysis()
    view = create_conditional_view(analysis, observation_policy=NO_OBSERVATION).view
    assert builder._collect_call_smt_declarations(view.analysis) == [
        "(declare-fun call_log ((_ BitVec 64)) (_ BitVec 64))"
    ]


def test_conditional_entry_point_builds_a_declared_and_applied_formula():
    """conditional view からは formula が組め、宣言と応用の両方が現れる。"""
    left, _ = _single_call_analysis(binary_id="binary1")
    right, _ = _single_call_analysis(binary_id="binary2")
    left_view = create_conditional_view(left, observation_policy=NO_OBSERVATION).view
    right_view = create_conditional_view(right, observation_policy=NO_OBSERVATION).view

    built = build_conditional_equivalence_formula(left_view, right_view)
    assert "(declare-fun call_log ((_ BitVec 64)) (_ BitVec 64))" in built.formula
    # return 定義側にも UF の応用が現れる（宣言だけの formula ではない）。
    application_lines = [
        line
        for line in built.formula.splitlines()
        if "call_log" in line and not line.lstrip().startswith("(declare-fun")
    ]
    assert application_lines
    # assumption は両 view の和で、最小化しない。
    assert built.assumption_set == left_view.assumption_set
    assert all(
        premise.kind is AssumptionKind.EXTERNAL_CALLEE_SPEC
        for premise in built.assumption_set
    )


def test_conditional_entry_point_unions_assumption_sets_without_minimizing():
    left, _ = _single_call_analysis(candidate=_candidate("log"), binary_id="binary1")
    right, _ = _single_call_analysis(candidate=_candidate("exp"), binary_id="binary2")
    left_view = create_conditional_view(left, observation_policy=NO_OBSERVATION).view
    right_view = create_conditional_view(right, observation_policy=NO_OBSERVATION).view
    built = build_conditional_equivalence_formula(left_view, right_view)
    assert [premise.subject for premise in built.assumption_set] == ["exp", "log"]
    assert len(built.assumption_set) == 2


def test_conditional_entry_point_rejects_semantics_changing_builder_options():
    """builder option を外から注入させない（追跡外の仮定が formula に入る）。"""
    left, _ = _single_call_analysis(binary_id="binary1")
    right, _ = _single_call_analysis(binary_id="binary2")
    left_view = create_conditional_view(left, observation_policy=NO_OBSERVATION).view
    right_view = create_conditional_view(right, observation_policy=NO_OBSERVATION).view

    for option in ("assume_fp_non_nan", "exclude_ub", "allow_call"):
        with pytest.raises(TypeError):
            build_conditional_equivalence_formula(
                left_view, right_view, **{option: True}
            )
    signature = inspect.signature(build_conditional_equivalence_formula)
    assert not [
        name
        for name, parameter in signature.parameters.items()
        if parameter.kind is inspect.Parameter.VAR_KEYWORD
    ]
    assert set(signature.parameters) == {"left_view", "right_view", "debug"}


def test_conditional_formula_carries_no_untracked_fp_assumption():
    """追跡されない FP non-NaN assertion が conditional formula に混入しない。"""
    left, _ = _single_call_analysis(binary_id="binary1")
    right, _ = _single_call_analysis(binary_id="binary2")
    left_view = create_conditional_view(left, observation_policy=NO_OBSERVATION).view
    right_view = create_conditional_view(right, observation_policy=NO_OBSERVATION).view

    built = build_conditional_equivalence_formula(left_view, right_view)
    assert "fp.isNaN" not in built.formula
    assert "Explicit FP input-domain assumptions" not in built.formula
    # 対照: 同じ analysis でも option を入れれば実際に assertion が増える
    # （= この test が空振りしていないこと）。
    injected = FormulaBuilder(allow_call=True, assume_fp_non_nan=True)
    injected_formula = injected.build_equivalence_formula_extended(
        left_view.analysis, right_view.analysis
    ).formula
    assert "fp.isNaN" in injected_formula
    # entry point 経由の formula は、その追跡外 assertion を含まない。
    assert built.formula != injected_formula


def test_conditional_entry_point_pins_every_semantic_builder_option():
    """semantic option を既定任せにしない（既定が変われば意味が黙って動く）。"""
    from scripts.function_tracer_pcode.proof.formula import builder as builder_module

    recorded = []

    class _RecordingFormulaBuilder(builder_module.FormulaBuilder):
        def __init__(self, *args, **kwargs):
            recorded.append((args, dict(kwargs)))
            super().__init__(*args, **kwargs)

    left, _ = _single_call_analysis(binary_id="binary1")
    right, _ = _single_call_analysis(binary_id="binary2")
    left_view = create_conditional_view(left, observation_policy=NO_OBSERVATION).view
    right_view = create_conditional_view(right, observation_policy=NO_OBSERVATION).view

    original = builder_module.FormulaBuilder
    builder_module.FormulaBuilder = _RecordingFormulaBuilder
    try:
        build_conditional_equivalence_formula(left_view, right_view)
    finally:
        builder_module.FormulaBuilder = original

    assert len(recorded) == 1
    positional, keywords = recorded[0]
    assert positional == ()
    assert keywords == {
        "debug": False,
        "exclude_ub": True,
        "assume_fp_non_nan": False,
        "allow_call": True,
    }


def test_conditional_entry_point_debug_option_does_not_change_the_formula():
    left, _ = _single_call_analysis(binary_id="binary1")
    right, _ = _single_call_analysis(binary_id="binary2")
    left_view = create_conditional_view(left, observation_policy=NO_OBSERVATION).view
    right_view = create_conditional_view(right, observation_policy=NO_OBSERVATION).view
    plain = build_conditional_equivalence_formula(left_view, right_view)
    verbose = build_conditional_equivalence_formula(left_view, right_view, debug=True)
    assert plain.formula == verbose.formula
    assert plain.assumption_set == verbose.assumption_set
    with pytest.raises(TypeError):
        build_conditional_equivalence_formula(left_view, right_view, debug=1)


def test_conditional_entry_point_only_accepts_conditional_views():
    analysis, _ = _single_call_analysis()
    view = create_conditional_view(analysis, observation_policy=NO_OBSERVATION).view
    with pytest.raises(TypeError):
        build_conditional_equivalence_formula(view, view.analysis)
    with pytest.raises(TypeError):
        build_conditional_equivalence_formula(analysis, analysis)


def test_conditional_builder_fails_closed_on_a_signature_conflict():
    builder = FormulaBuilder(allow_call=True)
    narrow, _ = _single_call_analysis(
        candidate=_candidate("log", argument_widths=(32,), return_width=32),
        arguments=[_param("x", size=4)],
        unknown_size=4,
    )
    wide, _ = _single_call_analysis()
    narrow_view = create_conditional_view(narrow, observation_policy=NO_OBSERVATION).view
    wide_view = create_conditional_view(wide, observation_policy=NO_OBSERVATION).view
    with pytest.raises(CallFormulaUnsupported):
        builder._collect_call_smt_declarations(narrow_view.analysis, wide_view.analysis)


def test_conditional_builder_flag_must_be_an_exact_bool():
    with pytest.raises(TypeError):
        FormulaBuilder(allow_call=1)


def test_unconditional_formula_output_is_unchanged_by_the_flag():
    """CALL を含まない通常 analysis では、両 builder の出力が一致する。"""
    plain = FunctionReturnAnalysis(
        function_name="snippet",
        entry_point="0x1000",
        function_ref=CallTargetRef.from_name("snippet", program_id=0x1000, entry_offset=0x1000),
        binary_id="binary1",
        parameters=[{"name": "x", "index": 0, "size": 8, "data_type": "long", "is_signed": True}],
        returns=[
            ReturnInfo(
                address="0x1000",
                value=Expression.binary_op(
                    "INT_ADD", _param("x", size=8), Expression.constant(1, size=8)
                ),
                conditions=[],
            )
        ],
        return_type="long",
    )
    other = plain.semantic_successor(binary_id="binary2")
    unconditional = FormulaBuilder().build_equivalence_formula_extended(plain, other)
    conditional = FormulaBuilder(allow_call=True).build_equivalence_formula_extended(
        plain, other
    )
    assert unconditional.formula == conditional.formula


# --- legacy sqrt path ------------------------------------------------------


def test_legacy_pure_return_call_table_is_gone_after_the_b3_cutover():
    """旧 sqrt/sqrtf の無条件 pure-return 経路は PR-20-B3 で撤去済み。"""
    from scripts.function_tracer_pcode.proof import deferred_call_abstraction

    assert not hasattr(deferred_call_abstraction, "_PURE_RETURN_CALLS")
    assert not hasattr(deferred_call_abstraction, "_pure_call_match_key")
    assert not hasattr(deferred_call_abstraction, "_pure_return_policy_size")


def test_conditional_view_has_exactly_one_production_entry_point():
    """view を production から使うのは PR-20-B3 の conditional lane だけ。"""
    import ast
    from pathlib import Path

    package_root = Path(view_module.__file__).resolve().parents[1]
    importers = []
    for path in package_root.rglob("*.py"):
        if "tests" in path.parts or path.name == "conditional_view.py":
            continue
        tree = ast.parse(path.read_text(encoding="utf-8"))
        for node in ast.walk(tree):
            module = None
            if isinstance(node, ast.ImportFrom):
                module = node.module
            elif isinstance(node, ast.Import):
                module = ",".join(alias.name for alias in node.names)
            if module and "conditional_view" in module:
                importers.append(str(path.relative_to(package_root)))
    # lane adapter (proof) だけが view を production 経路へ持ち込む。receipt 化は
    # authority 側で行うので、checker / reporting / cli からの直接 import は無い。
    assert importers == ["proof/conditional_lane.py"], importers

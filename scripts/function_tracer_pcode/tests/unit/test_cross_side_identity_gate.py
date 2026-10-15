# -*- coding: utf-8 -*-
"""plan v4 PR-P: owner を含まない key による左右の同一視の gate（I3・Q3）。

左右の値を index・名前・owner を含まない key で同じとみなす計算は、最終 InputCorrespondence が
「位置どおり・同じ名前・全幅の等式」のときだけ許す。反例（入れ替えた対応で非等価の pair が EQ
になる ``a_04`` の形）・対照（位置どおりの対応で等価な pair は EQ のまま）・production 経路
（``run_production_check``）・契約の検査を外すと落ちること（site の gate を開けても最終 gate が
止める / 最終 gate も外すと誤った EQ）を、この file で固定する。
"""

from __future__ import annotations

from dataclasses import replace
from types import SimpleNamespace

import pytest

from scripts.function_tracer_pcode.core import (
    CallTargetRef,
    CountedLoopSummaryRef,
    Expression,
    ExpressionType,
    ReturnInfo,
)
from scripts.function_tracer_pcode.core.analysis import FunctionReturnAnalysis, publish_raw_function_analysis
from scripts.function_tracer_pcode.core.runtime_refs import (
    CanonicalLocation,
    LocationBaseRef,
    PostStateReadRef,
    PostStateSnapshotRef,
)
from scripts.function_tracer_pcode.core.runtime_refs.loops import LoopSummaryRef, LoopTermDescriptorRef
from scripts.function_tracer_pcode.proof.formula.input_correspondence import (
    CrossSideIdentification,
    InputRelationKind,
    bind_evidence_to_comparison,
    build_input_correspondence_set,
    closure_reads_are_full,
    comparison_evidence,
    comparison_scope,
    final_equivalence_identity_gate,
    owner_free_identity_gate,
    positional_identity_gate,
    positional_parameter_identity_gate,
)
from scripts.function_tracer_pcode.proof.formula.input_correspondence.binding import CROSS_SIDE_IDENTIFICATION_KEY
from scripts.function_tracer_pcode.proof.obligations import (
    PairClosureEvidence,
    PairClosureKind,
    PairDispositionLedger,
    PairLedgerBinding,
    closure_identification_floor,
)
from scripts.function_tracer_pcode.proof.obligations import pair_disposition as ledger_module
from scripts.function_tracer_pcode.proof.strategies.pairwise_query_builder import extract_return_cases
from scripts.function_tracer_pcode.tests.unit._input_correspondence_support import (
    comparison_binding_of,
    positional_comparison,
)


# ---------------------------------------------------------------------------
# fixtures: a_03 / a_04 の形（limit = n の loop 和を、左右で引数の順が違う関数が返す）
# ---------------------------------------------------------------------------


def _p(name, index, size=8):
    return Expression(ExpressionType.PARAMETER, name=name, value=index, size=size)


def _c(value, size=8):
    return Expression(ExpressionType.CONSTANT, value=value, size=size)


def _loop_value(limit_leaf):
    summary = LoopSummaryRef(
        start_expr=_c(0), limit_expr=limit_leaf, step_expr=_c(1),
        term_descriptor=LoopTermDescriptorRef(kind="constant", result_size=8, residue_cases=((1, 0, 0, 1),)),
    )
    ref = CountedLoopSummaryRef(
        induction_step=1, result_size=8, signed_loop=True,
        residue_cases=((1, 0, 0, 1),), loop_summary=summary,
    )
    node = Expression(ExpressionType.INTRINSIC, name="counted_loop_sum", operands=[], size=8)
    node.runtime_ref = ref
    return node


def _d(name, index, size=8):
    return {"name": name, "index": index, "size": size, "data_type": "long", "is_signed": True}


def _unpublished(fname, descs, value):
    from scripts.function_tracer_pcode.tests.unit.test_issue185_type_hypothesis_domain import _abi_facts

    analysis = FunctionReturnAnalysis(
        function_name=fname, entry_point="0x401000", parameters=[dict(x) for x in descs],
        returns=[ReturnInfo(address="0x401010", conditions=[], value=value)],
        function_ref=CallTargetRef.from_name(fname, program_id=sum(map(ord, fname)), entry_offset=0x401000),
        binary_id="bin-" + fname,
    )
    analysis.return_type = "long"
    analysis.return_abi_facts = _abi_facts(return_type="/long", type_length=8, storage="PRESENT")
    return analysis


def _raw(fname, descs, value):
    return publish_raw_function_analysis(_unpublished(fname, descs, value))


def _swapped_pair():
    """左 f(n:0, m:1) は n を返し、右 g(m:0, n:1) は m を返す（relation は n↔n・m↔m で十分）。"""

    return (
        _raw("f", [_d("n", 0), _d("m", 1)], _loop_value(_p("n", 0))),
        _raw("g", [_d("m", 0), _d("n", 1)], _loop_value(_p("m", 0))),
    )


def _identity_pair(limit=None):
    limit = limit or (lambda: _p("n", 0))
    return (
        _raw("f", [_d("n", 0), _d("m", 1)], _loop_value(limit())),
        _raw("g", [_d("n", 0), _d("m", 1)], _loop_value(limit())),
    )


# ---------------------------------------------------------------------------
# positional_identity_gate（pair 全体の述語）
# ---------------------------------------------------------------------------


def test_positional_gate_accepts_only_a_full_positional_relation():
    identity = build_input_correspondence_set(*_identity_pair())
    assert positional_identity_gate(identity).passed

    swapped = build_input_correspondence_set(*_swapped_pair())
    assert swapped.decisive_sufficient  # relation としては十分（R4・名前で組む）
    refused = positional_identity_gate(swapped)
    assert not refused.passed
    assert any("not_positional" in ref for ref in refused.evidence_refs)

    assert not positional_identity_gate(None).passed
    assert positional_identity_gate(None).evidence_refs == ("cross_side_identity:relation_unavailable",)


def test_positional_gate_refuses_a_same_index_same_name_pair_that_is_not_full():
    # 両側とも n を読まない（どの幅でも閉じるので R3 SEMANTIC_PROJECTION）。index・名前・幅は同じでも、
    # 組は全幅の等式でない（relation は上位の bit を結ばない）。
    left = _raw("f", [_d("n", 0)], _c(1))
    right = _raw("g", [_d("n", 0)], _c(1))
    relation = build_input_correspondence_set(left, right)
    (pair,) = relation.correspondences
    assert pair.kind is InputRelationKind.SEMANTIC_PROJECTION and relation.decisive_sufficient
    refused = positional_identity_gate(relation)
    assert refused.evidence_refs == (
        "cross_side_identity:not_full_register_equality:param[0,0]:SEMANTIC_PROJECTION",
    )


def test_positional_gate_refuses_a_relation_with_a_non_full_pair():
    # 右だけ m を 32 bit で読む（WIDTH_OVERLAP / R3 の組）。index と名前は同じでも全幅の等式でない。
    left = _raw("f", [_d("n", 0), _d("m", 1)], _loop_value(_p("n", 0)))
    right = _raw("g", [_d("n", 0), _d("m", 1, size=4)], _loop_value(_p("n", 0)))
    relation = build_input_correspondence_set(left, right)
    assert any(item.kind is not InputRelationKind.FULL_REGISTER_EQUALITY for item in relation.correspondences)
    assert not positional_identity_gate(relation).passed


def test_positional_gate_refuses_a_table_that_differs_from_the_relation():
    relation = build_input_correspondence_set(*_identity_pair())
    renamed = replace(relation, right_parameters=tuple(
        replace(row, original_name="renamed") if row.index == 1 else row for row in relation.right_parameters
    ))
    refused = positional_identity_gate(renamed)
    assert not refused.passed
    assert "cross_side_identity:table_differs_from_relation:right" in refused.evidence_refs


def test_relation_digest_separates_relations_that_differ_only_by_names_or_tables():
    identity = build_input_correspondence_set(*_identity_pair())
    swapped = build_input_correspondence_set(*_swapped_pair())
    # 組の (index, 幅) だけは同じ形でも、名前が違えば別の比較の authority。
    assert identity.digest != swapped.digest
    renamed = replace(identity, right_parameters=tuple(
        replace(row, original_name="renamed") for row in identity.right_parameters
    ))
    assert renamed.digest != identity.digest


def test_positional_parameter_gate_requires_the_index_to_be_a_row_on_both_sides():
    relation = build_input_correspondence_set(*_identity_pair())
    assert positional_parameter_identity_gate(relation, 1).passed
    assert not positional_parameter_identity_gate(relation, 2).passed
    assert not positional_parameter_identity_gate(relation, True).passed
    swapped = build_input_correspondence_set(*_swapped_pair())
    assert not positional_parameter_identity_gate(swapped, 0).passed


# ---------------------------------------------------------------------------
# closure_reads_are_full（closure の局所の検査）
# ---------------------------------------------------------------------------


def test_closure_reads_refuse_a_narrow_parameter_read_also_inside_a_runtime_ref():
    relation = build_input_correspondence_set(*_identity_pair())
    full = _loop_value(_p("n", 0))
    narrow = _loop_value(_p("n", 0, size=4))  # limit の leaf だけが ref の中で狭い
    assert closure_reads_are_full(relation, (full,), (full,)).passed
    refused = closure_reads_are_full(relation, (full,), (narrow,))
    assert not refused.passed
    assert refused.evidence_refs == ("cross_side_identity:parameter_read_not_full:right:idx0:4B/64b",)


def test_closure_reads_refuse_leaves_that_do_not_name_their_row():
    relation = build_input_correspondence_set(*_identity_pair())
    assert not closure_reads_are_full(relation, (_p("m", 0),), (_p("n", 0),)).passed  # 名前は行 1
    assert not closure_reads_are_full(relation, (_p("n", None),), (_p("n", 0),)).passed  # index なし
    assert not closure_reads_are_full(relation, (_p("n", 7),), (_p("n", 0),)).passed  # 表に無い index


def test_closure_reads_refuse_a_graph_input_variable_shared_only_by_name():
    relation = build_input_correspondence_set(*_identity_pair())
    in_stack = Expression.variable("in_stack_00000028", size=8)
    refused = closure_reads_are_full(relation, (in_stack,), (Expression.variable("in_stack_00000028", size=8),))
    assert not refused.passed
    assert refused.evidence_refs[0] == "cross_side_identity:input_variable:left:in_stack_00000028"


def test_a_parameter_held_only_as_a_number_in_a_ref_is_covered_by_the_pair_wide_predicate():
    """review r1: ``LocationBaseRef`` は parameter を数値でしか持たない（carrier に leaf が無い）。

    読みを集める検査は素通りするが、pair 全体の述語は ref の形に依存せず、入れ替えた relation を拒む。
    """

    def post_state(name, index):
        location = CanonicalLocation(base_ref=LocationBaseRef.parameter(name, index=index), offset=0, size=4)
        ref = PostStateReadRef(location=location, snapshot_ref=PostStateSnapshotRef.function_return())
        return Expression.variable(f"post_{name}", size=4, runtime_ref=ref)

    swapped = build_input_correspondence_set(*_swapped_pair())
    left, right = (post_state("n", 0),), (post_state("n", 1),)
    assert not owner_free_identity_gate(left, right, ics=swapped).passed
    assert not owner_free_identity_gate(left, right, ics=None).passed


def test_owner_free_gate_reads_the_current_comparison_and_refuses_outside_it():
    left, right = _identity_pair()
    values = (_p("n", 0),)
    assert not owner_free_identity_gate(values, values).passed
    with comparison_scope(comparison_binding_of(left, right)):
        assert owner_free_identity_gate(values, values).passed
    swapped_left, swapped_right = _swapped_pair()
    with comparison_scope(comparison_binding_of(swapped_left, swapped_right)):
        assert not owner_free_identity_gate(values, values).passed
    # 明示の ``None`` は「relation が無い」で、現在の比較へ退避しない。
    with comparison_scope(comparison_binding_of(left, right)):
        assert not owner_free_identity_gate(values, values, ics=None).passed


# ---------------------------------------------------------------------------
# ledger: closure の左右の同一視の封印（record_pair_closed / 最終 gate が読む値）
# ---------------------------------------------------------------------------


def _binding():
    return PairLedgerBinding(
        comparison_session_id="s", branch_id="b", prepared_surface_digest="d" * 64,
        projection_id="p", frame_generation=1, derived_view_id=("v",), premise_digest="premise",
        graph_generation=1, comparison_authority_digest="c" * 64,
    )


def _producer_artifact(binding, monkeypatch):
    """登録した validator の代わりに、この test の関数を issuer として runtime reduction の artifact を作る。"""

    def issue():
        return ledger_module.issue_producer_validated_closure(
            ledger_module.RuntimeReductionClosureArtifact, binding, ("pair", "p"), ("evidence",),
        )

    monkeypatch.setitem(
        ledger_module._TRUSTED_PRODUCER_VALIDATOR_CODES,
        ledger_module.RuntimeReductionClosureArtifact.PRODUCER_KIND,
        issue.__code__,
    )
    return issue()


def test_owner_free_closure_kinds_cannot_be_declared_as_correspondence(monkeypatch):
    binding = _binding()
    artifact = _producer_artifact(binding, monkeypatch)
    assert closure_identification_floor(artifact) is CrossSideIdentification.OWNER_FREE
    closure = PairClosureEvidence.validated(
        (0, 0), PairClosureKind.RECOVERY, binding, artifact,
        identification=CrossSideIdentification.CORRESPONDENCE,
    )
    assert closure.identification is CrossSideIdentification.OWNER_FREE
    assert closure.validates(binding)
    # 封印した後で申告を書き換えると検証を通らない（digest と下限の両方）。
    forged = replace(closure, identification=CrossSideIdentification.CORRESPONDENCE)
    assert not forged.validates(binding)
    ledger = PairDispositionLedger(binding, 1)
    with pytest.raises(ValueError):
        ledger.close(forged)
    ledger.close(closure)
    assert ledger.owner_free_closures() == ((0, 0),)


def test_a_closure_with_a_consistent_digest_still_cannot_go_below_its_floor(monkeypatch):
    import hashlib

    binding = _binding()
    artifact = _producer_artifact(binding, monkeypatch)
    closure = PairClosureEvidence.validated(
        (0, 0), PairClosureKind.RECOVERY, binding, artifact, identification=CrossSideIdentification.OWNER_FREE,
    )
    # digest も申告に合わせて作り直した偽造（下限の検査だけが止める）。
    digest = hashlib.sha256(repr((
        binding.stable_key(), artifact.stable_key(), (), (), (), CrossSideIdentification.CORRESPONDENCE.value,
    )).encode()).hexdigest()
    forged = replace(closure, identification=CrossSideIdentification.CORRESPONDENCE, evidence_digest=digest)
    assert not forged.validates(binding)


def test_the_closure_digest_seals_the_identification(monkeypatch):
    binding = _binding()
    artifact = _producer_artifact(binding, monkeypatch)
    # 下限が CORRESPONDENCE の種類として扱う（申告の書き換えを digest だけが止める）。
    monkeypatch.setattr(ledger_module, "closure_identification_floor", lambda _artifact: CrossSideIdentification.CORRESPONDENCE)
    closure = PairClosureEvidence.validated(
        (0, 0), PairClosureKind.RECOVERY, binding, artifact, identification=CrossSideIdentification.OWNER_FREE,
    )
    assert closure.validates(binding)
    assert not replace(closure, identification=CrossSideIdentification.CORRESPONDENCE).validates(binding)


def test_structural_equality_by_name_has_an_owner_free_floor_and_void_return_does_not():
    def structural(kind):
        return ledger_module.StructuralEqualityClosureArtifact(
            receipt=None, premise_digest="p", query_label="(0,0)", producer_kind=kind, authority_digest="",
        )

    assert closure_identification_floor(structural("rewrite-structural")) is CrossSideIdentification.OWNER_FREE
    assert closure_identification_floor(structural("loop-template")) is CrossSideIdentification.OWNER_FREE
    assert closure_identification_floor(structural("void-return")) is CrossSideIdentification.CORRESPONDENCE
    assert closure_identification_floor(object()) is CrossSideIdentification.OWNER_FREE


def test_a_closure_requires_an_exact_identification(monkeypatch):
    binding = _binding()
    artifact = _producer_artifact(binding, monkeypatch)
    with pytest.raises(TypeError):
        PairClosureEvidence.validated((0, 0), PairClosureKind.RECOVERY, binding, artifact)  # type: ignore[call-arg]
    with pytest.raises(TypeError):
        PairClosureEvidence.validated(
            (0, 0), PairClosureKind.RECOVERY, binding, artifact, identification="correspondence",
        )


def test_record_pair_closed_seals_owner_free_when_the_query_carries_owner_free_assertions(monkeypatch):
    from scripts.function_tracer_pcode.proof.strategies.pairwise_services.orchestration import record_pair_closed

    binding = _binding()
    artifact = _producer_artifact(binding, monkeypatch)
    ledger = PairDispositionLedger(binding, 3)
    record_pair_closed(ledger, {}, (0, 0), PairClosureKind.RECOVERY, binding, artifact)
    assert ledger.closures[(0, 0)].identification is CrossSideIdentification.OWNER_FREE

    # SMT の closure でも、readonly の契約・deferred call の lowering の等式を足した pair は owner を含まない
    # （下限が CORRESPONDENCE の種類として扱い、申告だけが OWNER_FREE にすることを見る）。
    monkeypatch.setattr(ledger_module, "closure_identification_floor", lambda _artifact: CrossSideIdentification.CORRESPONDENCE)
    record_pair_closed(ledger, {}, (1, 0), PairClosureKind.RECOVERY, binding, artifact)
    assert ledger.closures[(1, 0)].identification is CrossSideIdentification.CORRESPONDENCE
    record_pair_closed(
        ledger, {"pairwise_extra_assertions_by_pair": {"(0,1)": ("(assert (= l r))",)}},
        (0, 1), PairClosureKind.RECOVERY, binding, artifact,
    )
    assert ledger.closures[(0, 1)].identification is CrossSideIdentification.OWNER_FREE


# ---------------------------------------------------------------------------
# 比較の証拠（completed recovery proof）の採用規則
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("declared", [CrossSideIdentification.OWNER_FREE, None])
def test_owner_free_evidence_is_adopted_only_under_a_positional_relation(declared):
    swapped = comparison_binding_of(*_swapped_pair())
    identity = comparison_binding_of(*_identity_pair())
    for binding, adopted in ((identity, True), (swapped, False)):
        record = bind_evidence_to_comparison({"proof_obligation_id": ("p",)}, binding, identification=declared)
        assert (CROSS_SIDE_IDENTIFICATION_KEY in record) is (declared is not None)
        with comparison_scope(binding):
            assert (comparison_evidence((record,)) == (record,)) is adopted


def test_correspondence_evidence_is_adopted_under_any_relation_of_its_comparison():
    swapped = comparison_binding_of(*_swapped_pair())
    record = bind_evidence_to_comparison(
        {"proof_obligation_id": ("p",)}, swapped, identification=CrossSideIdentification.CORRESPONDENCE,
    )
    with comparison_scope(swapped):
        assert comparison_evidence((record,)) == (record,)
    # 申告に知らない値を書いても owner を含まない扱い（fail-closed）。
    record[CROSS_SIDE_IDENTIFICATION_KEY] = "something_else"
    with comparison_scope(swapped):
        assert comparison_evidence((record,)) == ()


def test_the_evidence_writer_requires_a_declaration():
    from scripts.function_tracer_pcode.proof.formula.input_correspondence import store_comparison_evidence

    analysis = SimpleNamespace(completed_recovery_proof_evidence=())
    with pytest.raises(TypeError):
        store_comparison_evidence(analysis, [{"proof_obligation_id": ("p",)}])  # type: ignore[call-arg]
    with pytest.raises(TypeError):
        store_comparison_evidence(analysis, [{"proof_obligation_id": ("p",)}], identification="owner_free")


# ---------------------------------------------------------------------------
# site の gate（補助 query・構造の等価）
# ---------------------------------------------------------------------------


def _case(analysis):
    (case,) = extract_return_cases(analysis)
    return case


def test_auxiliary_symbols_are_not_shared_by_index_under_a_swapped_relation():
    """``a_02``: 入れ替えた relation で ``aux_param_0`` が左右の別の入力になり、自明な UNSAT を作った。"""

    from unittest.mock import Mock

    from scripts.function_tracer_pcode.proof.strategies.pairwise import PairwiseStrategy

    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    for pair, shared in ((_swapped_pair(), False), (_identity_pair(), True)):
        left, right = pair
        with comparison_scope(comparison_binding_of(left, right)):
            specs = strategy._collect_intrinsic_parameter_specs(
                _case(left), _case(right), _p("n", 0), _p("m", 0),
            )
        assert (specs is not None) is shared


def test_structural_equality_by_name_is_not_trivial_without_a_positional_relation():
    from scripts.function_tracer_pcode.proof.strategies import pairwise_solver_proven_rewrite as rewrite

    strategy = SimpleNamespace(debug=False)
    ctx = {"return_size1": 64, "return_size2": 64}
    left, right = _swapped_pair()
    same_name_left = _raw("f", [_d("n", 0), _d("m", 1)], _p("n", 0))
    same_name_right = _raw("g", [_d("m", 0), _d("n", 1)], _p("n", 1))
    with comparison_scope(comparison_binding_of(same_name_left, same_name_right)):
        assert not rewrite._rewritten_values_are_trivially_equal(
            strategy, ctx, _case(same_name_left), _case(same_name_right),
        )
    identity_left, identity_right = _raw("f", [_d("n", 0)], _p("n", 0)), _raw("g", [_d("n", 0)], _p("n", 0))
    with comparison_scope(comparison_binding_of(identity_left, identity_right)):
        assert rewrite._rewritten_values_are_trivially_equal(
            strategy, ctx, _case(identity_left), _case(identity_right),
        )
    # 名前の同じ入力 VARIABLE だけで閉じる構造の等価は、位置どおりの relation でも作らない。
    var_left = _raw("f", [_d("n", 0)], Expression.variable("in_stack_00000028", size=8))
    var_right = _raw("g", [_d("n", 0)], Expression.variable("in_stack_00000028", size=8))
    with comparison_scope(comparison_binding_of(var_left, var_right)):
        assert not rewrite._rewritten_values_are_trivially_equal(
            strategy, ctx, _case(var_left), _case(var_right),
        )
    del left, right


def test_the_runtime_reduction_producer_refuses_a_narrow_limit_read_under_an_identity_relation():
    """狭い読みの limit: 両側とも n を index 0 で読むが、右は 32 bit だけ。index だけの Method-B key
    （``('loop_limit_parameter', 0)``）は読みの幅を持たないので、producer は closure を作らない。"""

    from unittest.mock import Mock

    from scripts.function_tracer_pcode.proof.strategies.pairwise import PairwiseStrategy

    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    left = _raw("f", [_d("n", 0)], _loop_value(_p("n", 0)))
    right_full = _raw("g", [_d("n", 0)], _loop_value(_p("n", 0)))
    right_narrow = _raw("g", [_d("n", 0)], _loop_value(_p("n", 0, size=4)))
    with positional_comparison((_d("n", 0),)):
        assert strategy._cases_have_equivalent_runtime_reductions(_case(left), _case(right_full)) is True
        assert not owner_free_identity_gate((_case(left),), (_case(right_narrow),)).passed


# ---------------------------------------------------------------------------
# 最終の EQ gate（backstop）
# ---------------------------------------------------------------------------


def test_final_gate_refuses_owner_free_sources_only_without_a_positional_relation():
    swapped = build_input_correspondence_set(*_swapped_pair())
    identity = build_input_correspondence_set(*_identity_pair())
    assert final_equivalence_identity_gate((), swapped).passed
    assert final_equivalence_identity_gate(("pair(0, 0)",), identity).passed
    refused = final_equivalence_identity_gate(("pair(0, 0)",), swapped)
    assert not refused.passed
    assert refused.evidence_refs[0] == "cross_side_identity:owner_free_source:pair(0, 0)"


def test_the_preflight_final_gate_vetoes_an_owner_free_eq_under_a_swapped_relation(monkeypatch):
    from scripts.function_tracer_pcode.checker.preflight_gate import PreflightGateMixin

    binding = _binding()
    artifact = _producer_artifact(binding, monkeypatch)
    ledger = PairDispositionLedger(binding, 1)
    ledger.close(PairClosureEvidence.validated(
        (0, 0), PairClosureKind.RECOVERY, binding, artifact,
        identification=CrossSideIdentification.OWNER_FREE,
    ))
    for relation, expected in (
        (build_input_correspondence_set(*_identity_pair()), True),
        (build_input_correspondence_set(*_swapped_pair()), None),
    ):
        frame = SimpleNamespace(
            pair_disposition_ledger=ledger, prepared=SimpleNamespace(input_correspondence=relation),
            comparison_session_id="session", branch_id="S_PAIRWISE", generation=1,
        )
        result = SimpleNamespace(is_equivalent=True, unknown_reasons=[])
        PreflightGateMixin._veto_unproven_cross_side_identity(None, result, frame)
        assert result.is_equivalent is expected
        if expected is None:
            (reason,) = result.unknown_reasons
            assert reason.reason_id == "cross_side_identity_unproven"
            assert reason.evidence_refs[0].startswith("cross_side_identity:owner_free_source:")


# ---------------------------------------------------------------------------
# production の経路（実際の checker・authority・cutover）
# ---------------------------------------------------------------------------


def _production(case_id, left, right):
    from scripts.function_tracer_pcode.tests.unit._production_check_harness import run_production_check

    return run_production_check(case_id, left, right)


def _a04_cases():
    return {
        # 入れ替えた relation の下で等価でない pair（main では EQUIVALENT になった）
        "swapped_noneq": (
            _unpublished("f", [_d("n", 0), _d("m", 1)], _loop_value(_p("n", 0))),
            _unpublished("g", [_d("m", 0), _d("n", 1)], _loop_value(_p("m", 0))),
        ),
        # 位置どおりの relation で等価な pair（EQ のまま）
        "identity_eq_control": (
            _unpublished("f", [_d("n", 0), _d("m", 1)], _loop_value(_p("n", 0))),
            _unpublished("g", [_d("n", 0), _d("m", 1)], _loop_value(_p("n", 0))),
        ),
    }


def test_a04_swapped_correspondence_is_not_equivalent_in_production():
    cases = _a04_cases()
    swapped = _production("prp-a04-swapped", *cases["swapped_noneq"])
    assert swapped["final_outcome"] != "EQUIVALENT"
    assert swapped["final_outcome"] == "UNKNOWN"
    control = _production("prp-a04-control", *cases["identity_eq_control"])
    assert control["final_outcome"] == "EQUIVALENT"


def test_a04_the_final_gate_stops_the_false_eq_when_every_site_gate_is_open(monkeypatch):
    """site の gate を全部開けても最終の EQ gate が止める。最終 gate も外すと誤った EQ に戻る
    （= この反例は検査を外すと落ちる、本物の反例である）。"""

    from scripts.function_tracer_pcode.checker.preflight_gate import PreflightGateMixin
    from scripts.function_tracer_pcode.proof.obligations import pair_closure_producers

    monkeypatch.setattr(pair_closure_producers, "_owner_free_identity_admitted", lambda *_args: True)
    swapped = _production("prp-a04-sites-open", *_a04_cases()["swapped_noneq"])
    assert swapped["final_outcome"] == "UNKNOWN"
    # 止めたのは最終の EQ gate（この reason を出すのはそこだけ）
    assert "cross_side_identity_unproven" in {
        reason.get("reason_id") for reason in swapped.get("unknown_reasons") or () if isinstance(reason, dict)
    }

    monkeypatch.setattr(PreflightGateMixin, "_veto_unproven_cross_side_identity", lambda *_args: None)
    unguarded = _production("prp-a04-all-open", *_a04_cases()["swapped_noneq"])
    assert unguarded["final_outcome"] == "EQUIVALENT"


# ---------------------------------------------------------------------------
# deferred call の lowering（f(x, y) = g(x) と f(y, x) = g(y) の形）
# ---------------------------------------------------------------------------


def _lowering_check(monkeypatch, right_names):
    from unittest.mock import Mock

    from scripts.function_tracer_pcode.proof.strategies.pairwise import PairwiseStrategy
    from scripts.function_tracer_pcode.smt import ParallelResult, SolverResult, SolverStatus
    from scripts.function_tracer_pcode.tests.unit._input_correspondence_support import echo_input_correspondence
    from scripts.function_tracer_pcode.tests.unit._sat_decisiveness_fixtures import (
        _analysis_with_deferred_call_argument_blocker,
        _base_context_for_single_int_param,
        _patch_pairwise_single_case,
    )

    base_ctx = _base_context_for_single_int_param()
    formula_builder = echo_input_correspondence(Mock())
    formula_builder.build_base_context.return_value = base_ctx
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    # 左は fp(a)、右は fp(<index 1>) を呼ぶ。右の index 1 の名前を b にすると、relation は a↔a（1↔2）・
    # b↔b（2↔1）で、左右の呼び出しは別の入力を渡す。index で正規化した引数の key は同じになる。
    left = _analysis_with_deferred_call_argument_blocker(
        function_name="func1", binary_id="B1", entry=0x1000, return_deferred_unknown=True, argument_indices=(1,),
    )
    right = _analysis_with_deferred_call_argument_blocker(
        function_name="func2", binary_id="B14", entry=0x2000, return_deferred_unknown=True, argument_indices=(1,),
        parameter_names=right_names,
    )
    _patch_pairwise_single_case(monkeypatch, strategy, left, right)
    solver_runner.run_sequential = Mock(side_effect=[
        ParallelResult(results=[SolverResult(solver_name="z3", status=SolverStatus.SAT, elapsed_time=0.001)]),
        ParallelResult(results=[SolverResult(solver_name="z3", status=SolverStatus.UNSAT, elapsed_time=0.001)]),
    ] + [ParallelResult(results=[SolverResult(solver_name="z3", status=SolverStatus.UNKNOWN, elapsed_time=0.001)])] * 8)
    return strategy.check(left, right), base_ctx


def test_deferred_call_lowering_does_not_pair_calls_by_index_under_a_swapped_relation(monkeypatch):
    result, base_ctx = _lowering_check(monkeypatch, ("fp", "b", "a"))
    assert result.is_equivalent is None
    assert "(0,0)" not in (base_ctx.get("pairwise_extra_assertions_by_pair") or {})


def test_deferred_call_lowering_still_pairs_calls_under_a_positional_relation(monkeypatch):
    result, base_ctx = _lowering_check(monkeypatch, ("fp", "a", "b"))
    assert result.is_equivalent is True
    assertions = base_ctx["pairwise_extra_assertions_by_pair"]["(0,0)"]
    assert any(line.startswith("(assert (= rtunk_") for line in assertions)


# ---------------------------------------------------------------------------
# 残りの関所（readonly の契約の等式・loop template・loop pair の replanner・abi width の共有 memory）
# ---------------------------------------------------------------------------


def _scopes():
    """(位置どおりの比較, 入れ替えた比較)。"""

    return comparison_binding_of(*_identity_pair()), comparison_binding_of(*_swapped_pair())


def test_the_readonly_contract_equality_is_added_only_under_a_positional_relation(monkeypatch):
    from unittest.mock import Mock

    from scripts.function_tracer_pcode.core import ReadonlyReductionRef
    from scripts.function_tracer_pcode.proof.strategies.pairwise import PairwiseStrategy

    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    monkeypatch.setattr(strategy, "_case_pair_readonly_contract_result_size", lambda *_a: 4)
    monkeypatch.setattr(
        strategy, "_runtime_loop_contract_shortcut_decision",
        lambda *_a, **_k: SimpleNamespace(equivalent=True, requires_guard_equivalence=False),
    )

    def case(text):
        ref = ReadonlyReductionRef(
            reduction_kind="memory_sum", pointer_base_ref=LocationBaseRef.parameter("n", index=0),
            count_parameter_name="m", count_parameter_index=1, stride=4, element_size=4, result_size=4,
        )
        value = Expression.intrinsic("READONLY_SUM", (), size=4, runtime_ref=ref, opcode=0xF001)
        return SimpleNamespace(
            value_expr=value, conditions=[], get_value_smt=lambda *_a, **_k: text,
            should_sign_extend_value=lambda: False,
        )

    positional, swapped = _scopes()
    with comparison_scope(positional):
        assert strategy._readonly_contract_pairwise_extra_assertions(case("l"), case("r"), None, None)[-1] == (
            "(assert (= l r))"
        )
    with comparison_scope(swapped):
        assert strategy._readonly_contract_pairwise_extra_assertions(case("l"), case("r"), None, None) == ()


def test_the_loop_template_proof_is_not_tried_without_a_positional_relation(monkeypatch):
    from unittest.mock import Mock

    from scripts.function_tracer_pcode.proof.strategies import loop_template as template_module
    from scripts.function_tracer_pcode.proof.strategies.pairwise import PairwiseStrategy
    from scripts.function_tracer_pcode.proof.strategies.pairwise_models import QueryResult

    class Reached(Exception):
        pass

    def reached(*_a, **_k):
        raise Reached()

    monkeypatch.setattr(PairwiseStrategy, "_try_normalization_equivalence", lambda *_a, **_k: QueryResult(None))
    monkeypatch.setattr(template_module, "require_equal_return_bit_widths", reached)
    strategy = template_module.LoopTemplatePairwiseStrategy(Mock(), Mock(), debug=False)
    left, right = _identity_pair()
    cases = (_case(left), _case(right))
    positional, swapped = _scopes()
    with comparison_scope(swapped):
        assert strategy._try_normalization_equivalence({}, *cases, None, None, "(0,0)").is_equivalent is None
    with comparison_scope(positional), pytest.raises(Reached):
        strategy._try_normalization_equivalence({}, *cases, None, None, "(0,0)")


def test_the_loop_pair_replanner_uses_owner_free_value_proofs_only_under_a_positional_relation():
    from scripts.function_tracer_pcode.proof.strategies.pairwise_services.orchestration import (
        _register_loop_pair_replanner,
    )

    registered = []
    runtime = SimpleNamespace(
        premise_digest="premise",
        register_pair_query_replanner=lambda pair_id, kind, replan: registered.append(replan),
    )
    strategy = SimpleNamespace(
        _obligation_runtime_session=runtime,
        _recovery_proof_is_complete=lambda *_a: False,
        _case_pair_counted_loop_summaries_match_by_closed_values=lambda *_a, **_k: True,
        _counted_loop_values_are_provably_equivalent=lambda *_a, **_k: True,
    )
    left, right = _identity_pair()
    _register_loop_pair_replanner(
        strategy, "(0,0)", SimpleNamespace(object_target_key=("t",)), left, right,
        _case(left), _case(right), {}, (),
    )
    (replan,) = registered
    _requirement, _kind, produce = replan()
    positional, swapped = _scopes()
    with comparison_scope(positional):
        assert produce().is_equivalent is True
    with comparison_scope(swapped):
        assert produce().is_equivalent is None


def test_the_shared_readonly_memory_contract_needs_a_positional_relation():
    from scripts.function_tracer_pcode.tests.unit import test_unknown_taxonomy_v2_phase6_abi_width_readonly as abi

    positional = abi._readonly_seed(identified=True)
    assert positional.shared_input_memory_contract is not None
    swapped = abi._readonly_seed(identified=True, comparison=comparison_scope(_scopes()[1]))
    assert swapped.shared_input_memory_contract is None
    outside = abi._readonly_seed(identified=True, comparison=comparison_scope(None))
    assert outside.shared_input_memory_contract is None


def test_the_evidence_writer_records_the_declaration_of_what_it_binds():
    from scripts.function_tracer_pcode.proof.formula.input_correspondence import store_comparison_evidence

    positional, _swapped = _scopes()
    for declared in CrossSideIdentification:
        analysis = SimpleNamespace(completed_recovery_proof_evidence=())
        with comparison_scope(positional):
            store_comparison_evidence(analysis, [{"proof_obligation_id": ("p",)}], identification=declared)
        (record,) = analysis.completed_recovery_proof_evidence
        assert record[CROSS_SIDE_IDENTIFICATION_KEY] == declared.value
    analysis = SimpleNamespace(completed_recovery_proof_evidence=())
    with comparison_scope(positional):
        store_comparison_evidence(analysis, [{"proof_obligation_id": ("p",)}], identification=None)
    assert CROSS_SIDE_IDENTIFICATION_KEY not in analysis.completed_recovery_proof_evidence[0]


# ---------------------------------------------------------------------------
# call effect の memory の stage（左右の最終の memory 位置を ``("parameter", i)`` で組にする）
# ---------------------------------------------------------------------------


def test_the_memory_stage_pairs_parameter_locations_only_under_a_positional_parameter_table():
    from scripts.function_tracer_pcode.proof.call_effect import producer

    def proof_input(right_names):
        return SimpleNamespace(
            left_parameters=(_d("p", 0), _d("q", 1)),
            right_parameters=tuple(_d(name, index) for index, name in enumerate(right_names)),
        )

    producer._require_positional_parameter_locations(proof_input(("p", "q")), failure_prefix="memory_effect")
    with pytest.raises(ValueError, match="^memory_effect_location_relation_missing$"):
        # 右の p は index 1: 左の *p0 と右の *p0 は別の入力が指す位置
        producer._require_positional_parameter_locations(proof_input(("q", "p")), failure_prefix="memory_effect")
    with pytest.raises(ValueError, match="^caller_memory_effect_location_relation_missing$"):
        producer._require_positional_parameter_locations(
            SimpleNamespace(left_parameters=(_d("p", 0),), right_parameters=(_d("p", 0, size=4),)),
            failure_prefix="caller_memory_effect",
        )


# ---------------------------------------------------------------------------
# Method-B / readonly identity の closure と、その証拠を作る recorder（読みの幅も見る）
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("validator_name", ["validate_method_b_candidate", "validate_readonly_identity_candidate"])
def test_evidence_backed_closures_refuse_a_narrow_read_inside_a_ref_under_an_identity_relation(monkeypatch, validator_name):
    """index だけの key（``('loop_limit_parameter', 0)``）は読みの幅を持たない。証拠で閉じる closure も、
    比べる case の読み（runtime ref の中を含む）が全幅のときだけ発行する。"""

    from scripts.function_tracer_pcode.proof.obligations import pair_closure_producers as producers

    executed = []
    monkeypatch.setattr(producers, "_fixed_proof_implementation", lambda *_a: object())
    monkeypatch.setattr(producers, "_execute_pinned_proof", lambda *_a, **_k: executed.append(1) or (True, True))
    left = _raw("f", [_d("n", 0)], _loop_value(_p("n", 0)))
    right_full = _raw("g", [_d("n", 0)], _loop_value(_p("n", 0)))
    right_narrow = _raw("g", [_d("n", 0)], _loop_value(_p("n", 0, size=4)))
    validator = getattr(producers, validator_name)
    candidate_type = (
        producers.MethodBClosureCandidate if validator_name == "validate_method_b_candidate"
        else producers.ReadonlyIdentityCandidate
    )
    with positional_comparison((_d("n", 0),)) as comparison:
        binding = replace(_binding(), comparison_authority_digest=comparison.digest)
        candidate = candidate_type.create(binding, "(0,0)", ("target",), ())
        assert validator(None, binding, candidate, None, left, right_full, _case(left), _case(right_narrow)) is None
        assert executed == []
        assert validator(None, binding, candidate, None, left, right_full, _case(left), _case(right_full)) is not None
        assert executed == [1]


@pytest.mark.parametrize(("module_name", "recorder", "arguments"), [
    ("auxiliary_smt", "_impl__record_completed_method_b_dual_summary_solver_proof_if_safe", 2),
    ("method_b_closure", "_impl__record_completed_method_b_covering_case_proof_if_safe", 2),
    ("readonly_reduction", "_impl__record_completed_readonly_identity_projection_proof_if_safe", 3),
])
def test_owner_free_recorders_check_the_cases_before_recording(monkeypatch, module_name, recorder, arguments):
    import importlib

    module = importlib.import_module(
        "scripts.function_tracer_pcode.proof.strategies.pairwise_services." + module_name
    )
    seen = []

    def refuse(left, right, **_kwargs):
        seen.append((left, right))
        from scripts.function_tracer_pcode.proof.formula.input_correspondence import CrossSideIdentityGate

        return CrossSideIdentityGate.refuse(("probe",))

    monkeypatch.setattr(module, "owner_free_identity_gate", refuse)
    strategy = SimpleNamespace(enable_completed_recovery_proofs=True)
    case1, case2 = object(), object()
    analysis = SimpleNamespace(completed_recovery_proof_evidence=())
    leading = (SimpleNamespace(reason_id="x"),) + (analysis,) * (arguments - 1)
    kwargs = {"input_correspondence": None} if module_name == "readonly_reduction" else {}
    assert getattr(module, recorder)(strategy, *leading, case1, case2, **kwargs) is None
    assert seen == [((case1,), (case2,))]
    assert analysis.completed_recovery_proof_evidence == ()


def test_the_cross_side_identity_reason_blocks_only_equivalence_and_needs_a_source():
    from scripts.function_tracer_pcode.authority.domains.cross_side_identity import (
        CROSS_SIDE_IDENTITY_REASON_ID,
        CrossSideIdentityBlockerSignal,
    )
    from scripts.function_tracer_pcode.authority.lifecycle.pilot import PILOT_TYPED_CAUSE_KINDS
    from scripts.function_tracer_pcode.authority.process.supervisor import PROCESS_DURABLE_REASON_REGISTRY

    definition = PROCESS_DURABLE_REASON_REGISTRY.get(CROSS_SIDE_IDENTITY_REASON_ID)
    assert definition.decision_effect == "blocks_equivalence"
    assert CROSS_SIDE_IDENTITY_REASON_ID in PILOT_TYPED_CAUSE_KINDS
    fields = dict(
        comparison_session_id="s", branch_id="S_PAIRWISE", generation=1, input_correspondence_digest="d" * 64,
    )
    with pytest.raises(ValueError):
        CrossSideIdentityBlockerSignal(owner_free_sources=(), **fields)
    with pytest.raises(TypeError):
        CrossSideIdentityBlockerSignal(owner_free_sources=("pair(0, 0)",), **{**fields, "generation": True})
    first = CrossSideIdentityBlockerSignal(owner_free_sources=("pair(0, 0)",), **fields)
    other = CrossSideIdentityBlockerSignal(owner_free_sources=("pair(0, 0)",), **{**fields, "generation": 2})
    assert first.cause_target() != other.cause_target()


def test_the_cross_side_identity_encoder_observes_one_cause_per_vetoed_comparison():
    from scripts.function_tracer_pcode.authority.domains.cross_side_identity import (
        CROSS_SIDE_IDENTITY_REASON_ID,
        CrossSideIdentityBlockerSignal,
        CrossSideIdentityPilotEncoder,
    )
    from scripts.function_tracer_pcode.authority.lifecycle.stream import EventType

    session = SimpleNamespace(
        identity=SimpleNamespace(
            result_occurrence_id="result-a", source_snapshot_fingerprint="source-a",
            execution_identity_digest="execution-a",
        ),
        domain_signal_state={},
    )
    fields = dict(
        comparison_session_id="s", branch_id="S_PAIRWISE", input_correspondence_digest="d" * 64,
        owner_free_sources=("pair(0, 0)",), evidence_refs=("cross_side_identity:not_positional:param[0,1]:n~n",),
    )
    encoder = CrossSideIdentityPilotEncoder()
    first = CrossSideIdentityBlockerSignal(generation=1, **fields)
    (intent,) = encoder(session, first)
    assert intent.event_type is EventType.CAUSE_OBSERVED
    occurrence = encoder.authority_for_signal(session, first).occurrence
    assert occurrence.reason_id == CROSS_SIDE_IDENTITY_REASON_ID
    assert not encoder.has_observed(session, first)
    encoder.commit_emitted_signal(session, first, (intent,))
    # 同じ比較の拒否の繰り返しは 1 つの cause（reducer は同じ occurrence を 2 度受け付けない）。
    assert encoder.has_observed(session, first)
    assert encoder(session, CrossSideIdentityBlockerSignal(generation=1, **fields)) == ()
    # 別の generation（replan の後の比較）は別の cause。
    second = CrossSideIdentityBlockerSignal(generation=2, **fields)
    assert encoder.authority_for_signal(session, second).occurrence.occurrence_id != occurrence.occurrence_id
    assert len(encoder(session, second)) == 1
    # 別の比較の結果（result occurrence）では別の occurrence。
    other = SimpleNamespace(identity=SimpleNamespace(
        result_occurrence_id="result-b", source_snapshot_fingerprint="source-a",
        execution_identity_digest="execution-a",
    ), domain_signal_state={})
    assert encoder.authority_for_signal(other, first).occurrence.occurrence_id != occurrence.occurrence_id
    with pytest.raises(TypeError):
        encoder(session, object())

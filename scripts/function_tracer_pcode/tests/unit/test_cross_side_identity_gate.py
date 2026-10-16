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
    certify_owner_free_identity,
    closure_reads_are_full,
    comparison_evidence,
    issued_certificate,
    comparison_scope,
    current_relation,
    final_equivalence_identity_gate,
    owner_free_identity_gate,
    positional_identity_gate,
    positional_parameter_identity_gate,
)
from scripts.function_tracer_pcode.proof.formula.input_correspondence.binding import (
    CROSS_SIDE_IDENTIFICATION_KEY,
    CROSS_SIDE_IDENTITY_CERTIFICATE_KEY,
    owner_free_evidence_values,
)
from scripts.function_tracer_pcode.proof.formula.input_correspondence.certificates import (
    derive_owner_free_pair_assertions,
)
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
# 検査の証明書: owner を含まない closure・証拠・query の等式は、gate が発行した証明書なしに作れない
# ---------------------------------------------------------------------------


def _positional_comparison_binding():
    return comparison_binding_of(*_identity_pair())


def _binding(comparison=None):
    comparison = comparison or _positional_comparison_binding()
    return PairLedgerBinding(
        comparison_session_id="s", branch_id="b", prepared_surface_digest="d" * 64,
        projection_id="p", frame_generation=1, derived_view_id=("v",), premise_digest="premise",
        graph_generation=1, comparison_authority_digest=comparison.digest,
    )


def _certificate(subject, comparison=None, left=(), right=None):
    """``comparison`` の中で ``left`` / ``right`` を検査した証明書（既定は値なし = 読む値が無い）。"""

    comparison = comparison or _positional_comparison_binding()
    with comparison_scope(comparison):
        verdict = certify_owner_free_identity(left, left if right is None else right, subject=subject)
    assert verdict.passed, verdict.evidence_refs
    return verdict.certificate


def _producer_artifact(binding, monkeypatch, certificate, checked_values=((), ()), pair_id="(0,0)"):
    """登録した validator の代わりに、この test の関数を issuer として runtime reduction の artifact を作る。"""

    def issue():
        return ledger_module.issue_producer_validated_closure(
            ledger_module.RuntimeReductionClosureArtifact, binding, (pair_id, "p"), ("evidence",),
            identity_certificate=certificate, checked_values=checked_values,
        )

    monkeypatch.setitem(
        ledger_module._TRUSTED_PRODUCER_VALIDATOR_CODES,
        ledger_module.RuntimeReductionClosureArtifact.PRODUCER_KIND,
        issue.__code__,
    )
    return issue()


def test_certificates_are_issued_only_by_the_gate_inside_a_comparison_and_a_session(_pair_certificate_session):
    import copy
    import dataclasses

    from scripts.function_tracer_pcode.proof.formula.input_correspondence.certificates import (
        CrossSideIdentityCertificate,
        certificate_session,
        entered_certificate_session,
    )

    with pytest.raises(TypeError):
        CrossSideIdentityCertificate("id", "c" * 64, "r" * 64, ("pair", "(0,0)"), ((), ()), None, _pair_certificate_session)
    # 比較の外・入れ替えた relation では発行しない。
    assert certify_owner_free_identity((), (), subject=("pair", "(0,0)")).certificate is None
    with comparison_scope(comparison_binding_of(*_swapped_pair())):
        assert certify_owner_free_identity((), (), subject=("pair", "(0,0)")).certificate is None
    comparison = _positional_comparison_binding()
    # session の外では発行しない。
    with entered_certificate_session(None), comparison_scope(comparison):
        refused = certify_owner_free_identity((), (), subject=("pair", "(0,0)"))
    assert refused.certificate is None
    assert refused.evidence_refs == ("cross_side_identity:certificate_session_unavailable",)
    certificate = _certificate(("pair", "(0,0)"), comparison)
    assert certificate.covers(("pair", "(0,0)"), comparison_digest=comparison.digest)
    assert not certificate.covers(("pair", "(0,1)"), comparison_digest=comparison.digest)
    assert not certificate.covers(("pair", "(0,0)"), comparison_digest="0" * 64)
    # 作り直した証明書（replace・copy・deepcopy）は台帳に載っていないので通らない。
    for forged in (
        dataclasses.replace(certificate), copy.copy(certificate), copy.deepcopy(certificate),
    ):
        assert forged is not certificate
        assert not forged.covers(("pair", "(0,0)"), comparison_digest=comparison.digest)
    assert issued_certificate(certificate.certificate_id) is certificate
    # 別の session（入れ子でない別の実行）の中では、この session の証明書を引けない。
    with entered_certificate_session(None), certificate_session():
        assert issued_certificate(certificate.certificate_id) is None


def test_a_certificate_attests_only_the_values_it_checked():
    """同じ subject・同じ比較でも、検査した値（同じ object の同じ並び）以外には使えない。"""

    full_left = _raw("f", [_d("n", 0)], _p("n", 0))
    full_right = _raw("g", [_d("n", 0)], _p("n", 0))
    other_left = _raw("f", [_d("n", 0)], _p("n", 0))
    comparison = comparison_binding_of(full_left, full_right)
    left_case, right_case = _case(full_left), _case(full_right)
    certificate = _certificate(("pair", "(0,0)"), comparison, (left_case,), (right_case,))
    assert certificate.attests((left_case,), (right_case,))
    # 同じ published 値を持つ別の case object（作り直した ReturnCase）は同じ値を読む。
    assert certificate.attests((_case(full_left),), (right_case,))
    # 別の値（構造が同じでも別の object）・付け替えた case の属性・並びの違いは通らない。
    assert not certificate.attests((_case(other_left),), (right_case,))
    assert not certificate.attests((right_case,), (left_case,))
    reassigned = _case(full_left)
    reassigned.value_expr = _case(other_left).value_expr
    assert not certificate.attests((reassigned,), (right_case,))


def test_an_owner_free_closure_requires_the_certificate_of_its_pair_and_comparison(monkeypatch):
    comparison = _positional_comparison_binding()
    binding = _binding(comparison)
    certificate = _certificate(("pair", "(0,0)"), comparison)
    artifact = _producer_artifact(binding, monkeypatch, certificate)
    assert closure_identification_floor(artifact) is CrossSideIdentification.OWNER_FREE
    for missing in (None, _certificate(("pair", "(0,1)"), comparison), _certificate(("pair", "(0,0)"))):
        if missing is not None and missing.covers(("pair", "(0,0)"), comparison_digest=binding.comparison_authority_digest):
            continue
        with pytest.raises(ValueError):
            PairClosureEvidence.validated(
                (0, 0), PairClosureKind.RECOVERY, binding, artifact,
                identification=CrossSideIdentification.OWNER_FREE, identity_certificate=missing,
            )
    closure = PairClosureEvidence.validated(
        (0, 0), PairClosureKind.RECOVERY, binding, artifact,
        identification=CrossSideIdentification.CORRESPONDENCE, identity_certificate=certificate,
    )
    # 種類の下限で owner を含まない（申告では下げられない）。
    assert closure.identification is CrossSideIdentification.OWNER_FREE
    assert closure.validates(binding)
    # 封印した後で申告・証明書を書き換えると検証を通らない。
    assert not replace(closure, identification=CrossSideIdentification.CORRESPONDENCE).validates(binding)
    assert not replace(closure, identity_certificate=None).validates(binding)
    other = _certificate(("pair", "(0,0)"), comparison)
    assert not replace(closure, identity_certificate=other).validates(binding)
    ledger = PairDispositionLedger(binding, 1)
    ledger.close(closure)
    assert ledger.owner_free_closures() == (((0, 0), certificate),)


def test_a_producer_closure_cannot_be_issued_without_a_certificate_of_its_comparison(monkeypatch):
    comparison = _positional_comparison_binding()
    binding = _binding(comparison)
    with pytest.raises(ValueError):
        _producer_artifact(binding, monkeypatch, None)
    other_comparison = comparison_binding_of(*_identity_pair(lambda: _p("m", 1)))
    with pytest.raises(ValueError):
        _producer_artifact(binding, monkeypatch, _certificate(("pair", "(0,0)"), other_comparison))
    # この pair・この比較の証明書でも、closure の入力でない値を検査したものは使えない。
    left, right = _identity_pair()
    checked = ((_case(left),), (_case(right),))
    certificate = _certificate(("pair", "(0,0)"), comparison, *checked)
    with pytest.raises(ValueError):
        _producer_artifact(binding, monkeypatch, certificate)  # 入力は値なし
    with pytest.raises(ValueError):
        _producer_artifact(binding, monkeypatch, certificate, checked, pair_id="(0,1)")  # 別の pair
    assert _producer_artifact(binding, monkeypatch, certificate, checked).identity_certificate is certificate


def test_a_correspondence_closure_does_not_carry_a_certificate(monkeypatch):
    comparison = _positional_comparison_binding()
    binding = _binding(comparison)
    artifact = _producer_artifact(binding, monkeypatch, _certificate(("pair", "(0,0)"), comparison))
    monkeypatch.setattr(ledger_module, "closure_identification_floor", lambda _artifact: CrossSideIdentification.CORRESPONDENCE)
    with pytest.raises(ValueError):
        PairClosureEvidence.validated(
            (0, 0), PairClosureKind.RECOVERY, binding, artifact,
            identification=CrossSideIdentification.CORRESPONDENCE,
            identity_certificate=_certificate(("pair", "(0,0)"), comparison),
        )
    closure = PairClosureEvidence.validated(
        (0, 0), PairClosureKind.RECOVERY, binding, artifact, identification=CrossSideIdentification.CORRESPONDENCE,
    )
    assert closure.validates(binding)
    # 申告の書き換えは digest が止める。
    assert not replace(closure, identification=CrossSideIdentification.OWNER_FREE).validates(binding)


def test_structural_equality_by_name_has_an_owner_free_floor_and_void_return_does_not():
    def structural(kind):
        return ledger_module.StructuralEqualityClosureArtifact(
            receipt=None, premise_digest="p", query_label="(0,0)", producer_kind=kind, authority_digest="",
        )

    assert closure_identification_floor(structural("rewrite-structural")) is CrossSideIdentification.OWNER_FREE
    assert closure_identification_floor(structural("loop-template")) is CrossSideIdentification.OWNER_FREE
    assert closure_identification_floor(structural("void-return")) is CrossSideIdentification.CORRESPONDENCE
    assert closure_identification_floor(object()) is CrossSideIdentification.OWNER_FREE


def test_a_name_based_structural_receipt_requires_the_certificate_of_its_pair():
    # issuer は登録した producer の code object に pin されるので、ここでは receipt の検査そのものを
    # 直接呼ぶ: 登録表の code を一時的にこの関数の code にして呼ぶ。
    comparison = _positional_comparison_binding()

    def issue(certificate, kind, checked=((), ()), within=comparison):
        with comparison_scope(within):
            return ledger_module.issue_structural_equality_receipt(
                query_label="(0,0)", proof_kind=kind, evidence=(kind,), identity_certificate=certificate,
                checked_values=None if certificate is None else checked,
            )

    table = ledger_module._TRUSTED_STRUCTURAL_EQUALITY_PRODUCER_CODES
    saved = dict(table)
    try:
        for kind in ("rewrite-structural", "loop-template", "void-return"):
            table[kind] = issue.__code__
        for kind in ("rewrite-structural", "loop-template"):
            for wrong in (None, _certificate(("pair", "(0,1)"), comparison)):
                with pytest.raises(ValueError):
                    issue(wrong, kind)
            left, right = _identity_pair()
            checked = ((_case(left),), (_case(right),))
            values_certificate = _certificate(("pair", "(0,0)"), comparison, *checked)
            with pytest.raises(ValueError):
                issue(values_certificate, kind)  # 証明書は別の値（case）を検査した
            with pytest.raises(ValueError):
                # 別の比較の中では発行しない
                issue(values_certificate, kind, checked, within=comparison_binding_of(*_swapped_pair()))
            receipt = issue(values_certificate, kind, checked)
            assert receipt.identity_certificate is not None and receipt.validates_authority()
        with pytest.raises(ValueError):
            issue(_certificate(("pair", "(0,0)"), comparison), "void-return")
        assert issue(None, "void-return").identity_certificate is None
    finally:
        table.clear()
        table.update(saved)


def test_a_closure_requires_an_exact_identification(monkeypatch):
    comparison = _positional_comparison_binding()
    binding = _binding(comparison)
    artifact = _producer_artifact(binding, monkeypatch, _certificate(("pair", "(0,0)"), comparison))
    with pytest.raises(TypeError):
        PairClosureEvidence.validated((0, 0), PairClosureKind.RECOVERY, binding, artifact)  # type: ignore[call-arg]
    with pytest.raises(TypeError):
        PairClosureEvidence.validated(
            (0, 0), PairClosureKind.RECOVERY, binding, artifact, identification="correspondence",
        )


def test_record_pair_closed_takes_the_certificate_from_the_artifact_or_the_query_assertions(monkeypatch):
    from scripts.function_tracer_pcode.proof.strategies.pairwise_services.orchestration import record_pair_closed

    comparison = _positional_comparison_binding()
    binding = _binding(comparison)
    certificate = _certificate(("pair", "(0,0)"), comparison)
    artifact = _producer_artifact(binding, monkeypatch, certificate)
    ledger = PairDispositionLedger(binding, 3)
    record_pair_closed(ledger, {}, (0, 0), PairClosureKind.RECOVERY, binding, artifact)
    assert ledger.closures[(0, 0)].identity_certificate is certificate

    # SMT の closure でも、owner を含まない等式を足した pair は owner を含まず、等式と一緒に登録した
    # 証明書を ledger へ渡す（下限が CORRESPONDENCE の種類として扱い、等式の側の経路だけを見る）。
    class _SolverUnsat:
        """relation の premise の下の SMT の closure（下限が CORRESPONDENCE の種類）の代わり。"""

        def validates(self, *_args):
            return True

        def stable_key(self):
            return ("solver-unsat-stub",)

    plain = _SolverUnsat()
    assert closure_identification_floor(plain) is CrossSideIdentification.OWNER_FREE
    monkeypatch.setattr(ledger_module, "closure_identification_floor", lambda _artifact: CrossSideIdentification.CORRESPONDENCE)
    record_pair_closed(ledger, {}, (1, 0), PairClosureKind.RECOVERY, binding, plain)
    assert ledger.closures[(1, 0)].identification is CrossSideIdentification.CORRESPONDENCE
    left, right = _identity_pair()
    checked = ((_case(left),), (_case(right),))
    pair_certificate = _certificate(("pair", "(0,1)"), comparison, *checked)
    carrier = derive_owner_free_pair_assertions(pair_certificate, *checked, lambda _l, _r: ("(assert (= l r))",))
    for base_ctx in (
        # 等式はあるが carrier が無い（登録の経路を迂回した等式）。
        {"pairwise_extra_assertions_by_pair": {"(0,1)": ("(assert (= l r))",)}},
        # carrier と query の行が違う（carrier の後で書き換えた等式）。
        {
            "pairwise_extra_assertions_by_pair": {"(0,1)": ("(assert (= l_narrow r))",)},
            "pairwise_extra_assertion_carriers_by_pair": {"(0,1)": carrier},
        },
        # 別の pair の carrier。
        {
            "pairwise_extra_assertions_by_pair": {"(0,2)": ("(assert (= l r))",)},
            "pairwise_extra_assertion_carriers_by_pair": {"(0,2)": carrier},
        },
    ):
        pair_key = (0, 2) if "(0,2)" in base_ctx["pairwise_extra_assertions_by_pair"] else (0, 1)
        with pytest.raises(ValueError):
            record_pair_closed(ledger, base_ctx, pair_key, PairClosureKind.RECOVERY, binding, plain)
    record_pair_closed(
        ledger, {
            "pairwise_extra_assertions_by_pair": {"(0,1)": ("(assert (= l r))",)},
            "pairwise_extra_assertion_carriers_by_pair": {"(0,1)": carrier},
        },
        (0, 1), PairClosureKind.RECOVERY, binding, plain,
    )
    assert ledger.closures[(0, 1)].identification is CrossSideIdentification.OWNER_FREE
    assert ledger.closures[(0, 1)].identity_certificate is pair_certificate


def test_owner_free_query_assertions_are_built_from_and_registered_with_the_certificate_of_their_values():
    from unittest.mock import Mock

    from scripts.function_tracer_pcode.proof.strategies.pairwise import PairwiseStrategy
    from scripts.function_tracer_pcode.proof.strategies.pairwise_services._shared import OwnerFreePairAssertions

    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    comparison = _positional_comparison_binding()
    left, right = _identity_pair()
    checked = ((_case(left),), (_case(right),))
    built_from = []

    def build(left_values, right_values):
        built_from.append((left_values, right_values))
        return ("(assert (= l r))",)

    base_ctx = {}
    with comparison_scope(comparison):
        with pytest.raises(TypeError):
            strategy._register_pairwise_extra_assertions(base_ctx, "(0,0)", ("(assert (= l r))",))
        certificate = _certificate(("pair", "(0,0)"), comparison, *checked)
        with pytest.raises(TypeError):
            OwnerFreePairAssertions(("(assert (= l r))",), certificate, checked)  # 作るのは derive だけ
        with pytest.raises(ValueError):
            # 証明書が検査していない値から作る
            derive_owner_free_pair_assertions(certificate, (), (), build)
        carrier = derive_owner_free_pair_assertions(certificate, *checked, build)
        assert built_from == [checked]
        for wrong_pair in ("(0,1)",):
            with pytest.raises(ValueError):
                strategy._register_pairwise_extra_assertions(base_ctx, wrong_pair, carrier)
        strategy._register_pairwise_extra_assertions(base_ctx, "(0,0)", carrier)
    assert base_ctx["pairwise_extra_assertion_carriers_by_pair"]["(0,0)"] is carrier
    with comparison_scope(comparison_binding_of(*_identity_pair(lambda: _p("m", 1)))):
        with pytest.raises(ValueError):
            # 別の比較の証明書
            strategy._register_pairwise_extra_assertions(base_ctx, "(0,0)", carrier)
    strategy._clear_pairwise_extra_assertions(base_ctx, "(0,0)")
    assert "(0,0)" not in base_ctx["pairwise_extra_assertion_carriers_by_pair"]


def test_counterexample_2b_a_full_width_certificate_cannot_carry_a_narrow_equality():
    """review 3: 全幅の値で得た証明書を、局所 gate が拒否する狭い読みの等式の登録に使えた（API 上の不足）。"""

    full_left = _raw("f", [_d("n", 0)], _p("n", 0))
    full_right = _raw("g", [_d("n", 0)], _p("n", 0))
    narrow_left = _raw("f", [_d("n", 0)], _p("n", 0, size=4))
    comparison = comparison_binding_of(full_left, full_right)
    full = ((_case(full_left),), (_case(full_right),))
    narrow = ((_case(narrow_left),), (_case(full_right),))
    with comparison_scope(comparison):
        assert not certify_owner_free_identity(*narrow, subject=("pair", "(0,0)")).passed
        certificate = certify_owner_free_identity(*full, subject=("pair", "(0,0)")).certificate
        with pytest.raises(ValueError):
            derive_owner_free_pair_assertions(certificate, *narrow, lambda _l, _r: ("(assert (= l r))",))


# ---------------------------------------------------------------------------
# 比較の証拠（completed recovery proof）の採用規則
# ---------------------------------------------------------------------------


def _pair_values(limit=None):
    left, right = _identity_pair(limit)
    return ((_case(left),), (_case(right),))


def _owner_free_record(comparison, target=("target",), checked=None):
    checked = checked if checked is not None else _pair_values()
    certificate = _certificate(("comparison_evidence", target), comparison, *checked)
    return bind_evidence_to_comparison(
        {"proof_obligation_id": ("p",), "object_target_key": target}, comparison,
        identification=CrossSideIdentification.OWNER_FREE, certificate=certificate, checked_values=checked,
    ), certificate, checked


def test_owner_free_evidence_is_adopted_only_by_a_reader_of_the_values_it_was_made_from():
    comparison = _positional_comparison_binding()
    record, certificate, checked = _owner_free_record(comparison)
    assert record[CROSS_SIDE_IDENTITY_CERTIFICATE_KEY] == certificate.certificate_id
    with comparison_scope(comparison):
        # 値を示さない読み手（集約など）は採用しない。
        assert comparison_evidence((record,)) == ()
        with owner_free_evidence_values(*checked):
            assert comparison_evidence((record,)) == (record,)
        # 同じ object_target_key・同じ比較でも、別の pair の値を示す読み手には使えない。
        with owner_free_evidence_values(*_pair_values(lambda: _p("n", 0, size=4))):
            assert comparison_evidence((record,)) == ()
    # 申告だけ（証明書の id が無い・発行されていない・別の対象）は採用しない。
    for mutate in (
        lambda r: r.pop(CROSS_SIDE_IDENTITY_CERTIFICATE_KEY),
        lambda r: r.__setitem__(CROSS_SIDE_IDENTITY_CERTIFICATE_KEY, "0" * 64),
        lambda r: r.__setitem__("object_target_key", ("other",)),
    ):
        forged = dict(record)
        mutate(forged)
        with comparison_scope(comparison), owner_free_evidence_values(*checked):
            assert comparison_evidence((forged,)) == ()
    undeclared = dict(record)
    undeclared.pop(CROSS_SIDE_IDENTIFICATION_KEY)
    with comparison_scope(comparison), owner_free_evidence_values(*checked):
        assert comparison_evidence((undeclared,)) == ()


def test_owner_free_evidence_expires_with_its_session():
    """遅延して読む証拠は session が開いている間は使え、session を閉じると使えない。"""

    from scripts.function_tracer_pcode.proof.formula.input_correspondence.binding import run_in_current_comparison
    from scripts.function_tracer_pcode.proof.formula.input_correspondence.certificates import (
        certificate_session,
        entered_certificate_session,
    )

    comparison = _positional_comparison_binding()
    with entered_certificate_session(None), certificate_session():
        record, _certificate_value, checked = _owner_free_record(comparison)
        def read():
            with owner_free_evidence_values(*checked):
                return comparison_evidence((record,))

        with comparison_scope(comparison):
            later = run_in_current_comparison(read)
        # 登録した実行がまだ続いている間（遅延 producer）は、呼んだ場所の session に依らず採用する
        # （callable が登録した session を運ぶ）。
        assert later() == (record,)
        with entered_certificate_session(None):
            assert later() == (record,)
    # 実行が終わった後は、同じ callable でも採用しない（失効）。
    assert later() == ()


def test_owner_free_evidence_cannot_be_bound_without_the_certificate_of_its_subject_and_values():
    comparison = _positional_comparison_binding()
    checked = _pair_values()
    for certificate, values in (
        (None, checked),
        (_certificate(("comparison_evidence", ("other",)), comparison, *checked), checked),
        (_certificate(("comparison_evidence", ("target",)), comparison, *checked), _pair_values()),  # 別の値
        (_certificate(("comparison_evidence", ("target",)), comparison, *checked), None),
    ):
        with pytest.raises(ValueError):
            bind_evidence_to_comparison(
                {"object_target_key": ("target",)}, comparison,
                identification=CrossSideIdentification.OWNER_FREE, certificate=certificate, checked_values=values,
            )
    with pytest.raises(ValueError):
        bind_evidence_to_comparison(
            {"object_target_key": ("target",)}, comparison,
            identification=CrossSideIdentification.CORRESPONDENCE,
            certificate=_certificate(("comparison_evidence", ("target",)), comparison, *checked),
        )


def test_correspondence_evidence_is_adopted_under_any_relation_of_its_comparison():
    swapped = comparison_binding_of(*_swapped_pair())
    record = bind_evidence_to_comparison(
        {"proof_obligation_id": ("p",)}, swapped, identification=CrossSideIdentification.CORRESPONDENCE,
    )
    with comparison_scope(swapped):
        assert comparison_evidence((record,)) == (record,)
    # 申告に知らない値を書いても採用しない（fail-closed）。
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
    with comparison_scope(_positional_comparison_binding()), pytest.raises(ValueError):
        store_comparison_evidence(
            analysis, [{"object_target_key": ("t",)}], identification=CrossSideIdentification.OWNER_FREE,
        )


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


def test_structural_equality_by_name_is_certified_only_under_a_positional_relation():
    """自明な一致（名前・runtime ref の key で左右を同一視）は、``certify_owner_free_identity`` が
    pair の証明書を出したときだけ使う（``try_solver_proven_rewrite_equivalence`` がその順に呼ぶ）。"""

    from scripts.function_tracer_pcode.proof.strategies import pairwise_solver_proven_rewrite as rewrite

    strategy = SimpleNamespace(debug=False)
    ctx = {"return_size1": 64, "return_size2": 64}
    subject = ("pair", "(0,0)")
    same_name_left = _raw("f", [_d("n", 0), _d("m", 1)], _p("n", 0))
    same_name_right = _raw("g", [_d("m", 0), _d("n", 1)], _p("n", 1))
    with comparison_scope(comparison_binding_of(same_name_left, same_name_right)):
        # 名前だけを見る自明な一致は成り立つ（だから証明書が要る）。
        assert rewrite._rewritten_values_are_trivially_equal(
            strategy, ctx, _case(same_name_left), _case(same_name_right),
        )
        assert not certify_owner_free_identity(
            (_case(same_name_left),), (_case(same_name_right),), subject=subject,
        ).passed
    identity_left, identity_right = _raw("f", [_d("n", 0)], _p("n", 0)), _raw("g", [_d("n", 0)], _p("n", 0))
    with comparison_scope(comparison_binding_of(identity_left, identity_right)):
        assert certify_owner_free_identity((_case(identity_left),), (_case(identity_right),), subject=subject).passed
    # 名前の同じ入力 VARIABLE だけで閉じる構造の等価は、位置どおりの relation でも証明書を出さない。
    var_left = _raw("f", [_d("n", 0)], Expression.variable("in_stack_00000028", size=8))
    var_right = _raw("g", [_d("n", 0)], Expression.variable("in_stack_00000028", size=8))
    with comparison_scope(comparison_binding_of(var_left, var_right)):
        assert not certify_owner_free_identity((_case(var_left),), (_case(var_right),), subject=subject).passed


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


def test_final_gate_refuses_owner_free_sources_without_a_positional_relation_or_a_certificate():
    comparison = _positional_comparison_binding()
    identity = comparison.relation
    swapped = build_input_correspondence_set(*_swapped_pair())
    certificate = _certificate(("pair", "(0,0)"), comparison)
    assert final_equivalence_identity_gate((), swapped).passed
    assert final_equivalence_identity_gate((("pair(0, 0)", certificate),), identity).passed
    refused = final_equivalence_identity_gate((("pair(0, 0)", certificate),), swapped)
    assert not refused.passed
    assert refused.evidence_refs[0] == "cross_side_identity:owner_free_source:pair(0, 0)"
    # 位置どおりの relation でも、証明書の無い・別の relation の証明書の source は止める。
    other = _certificate(("pair", "(0,0)"), comparison_binding_of(
        _raw("f", [_d("n", 0)], _p("n", 0)), _raw("g", [_d("n", 0)], _p("n", 0)),
    ))
    assert other.relation_digest != identity.digest
    for missing in (None, "forged", other):
        verdict = final_equivalence_identity_gate((("pair(0, 0)", missing),), identity)
        assert not verdict.passed
        assert "cross_side_identity:certificate_missing:pair(0, 0)" in verdict.evidence_refs


def _ledger_with_owner_free_closure(monkeypatch):
    comparison = _positional_comparison_binding()
    binding = _binding(comparison)
    certificate = _certificate(("pair", "(0,0)"), comparison)
    artifact = _producer_artifact(binding, monkeypatch, certificate)
    ledger = PairDispositionLedger(binding, 1)
    ledger.close(PairClosureEvidence.validated(
        (0, 0), PairClosureKind.RECOVERY, binding, artifact,
        identification=CrossSideIdentification.OWNER_FREE, identity_certificate=certificate,
    ))
    return comparison, ledger


def test_the_preflight_final_gate_vetoes_an_owner_free_eq_under_a_swapped_relation(monkeypatch):
    from scripts.function_tracer_pcode.checker.preflight_gate import PreflightGateMixin

    comparison, ledger = _ledger_with_owner_free_closure(monkeypatch)
    for relation, expected in (
        (comparison.relation, True),
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


def test_the_compat_and_legacy_pairwise_path_applies_the_same_veto(monkeypatch):
    """dispatch frame を持たない pairwise（互換・``LEGACY_POST_PAIRWISE``）も同じ実装で止める。"""

    from scripts.function_tracer_pcode.proof.strategies.pairwise_services import orchestration

    comparison, ledger = _ledger_with_owner_free_closure(monkeypatch)
    emitted = []
    monkeypatch.setattr(
        "scripts.function_tracer_pcode.authority.lifecycle.production_signals.emit_cross_side_identity_signal",
        lambda signal, **kwargs: emitted.append((signal, kwargs)),
    )
    result = SimpleNamespace(is_equivalent=True, unknown_reasons=[])
    assert orchestration.veto_unproven_cross_side_identity(
        result, ledger, build_input_correspondence_set(*_swapped_pair()),
        comparison_session_id="s", branch_id="S_PAIRWISE", generation=1,
    ) is True
    assert result.is_equivalent is None
    assert result.unknown_reasons[0].reason_id == "cross_side_identity_unproven"
    ((signal, kwargs),) = emitted
    assert kwargs["producer_site_manifest_id"] == "pairwise-cross-side-identity-veto"
    assert signal.owner_free_sources == ("pair(0, 0)",)
    kept = SimpleNamespace(is_equivalent=True, unknown_reasons=[])
    assert orchestration.veto_unproven_cross_side_identity(
        kept, ledger, comparison.relation, comparison_session_id="s", branch_id="S_PAIRWISE", generation=1,
    ) is False
    assert kept.is_equivalent is True


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

    from scripts.function_tracer_pcode.proof.formula.input_correspondence import gate as gate_module

    # 証明書の発行で読む検査だけを開ける（証明書は relation の digest を持つので、最終 gate は比較の
    # relation を見て止める）。
    monkeypatch.setattr(
        gate_module, "_owner_free_reading",
        lambda _relation, left, right: ((), gate_module.checked_surface(left), gate_module.checked_surface(right)),
    )
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
        assertions = strategy._readonly_contract_pairwise_extra_assertions(
            case("l"), case("r"), None, None, pair_id="(0,0)",
        )
        assert assertions.lines[-1] == "(assert (= l r))"
        # 等式は pair の証明書と一緒にだけ渡る（登録が証明書を検査する）。
        assert assertions.identity_certificate.covers(("pair", "(0,0)"), comparison_digest=positional.digest)
    with comparison_scope(swapped):
        assert strategy._readonly_contract_pairwise_extra_assertions(
            case("l"), case("r"), None, None, pair_id="(0,0)",
        ) is None


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
    for declared in (CrossSideIdentification.CORRESPONDENCE,):
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

    monkeypatch.setattr(module, "certify_owner_free_identity", refuse)
    from scripts.function_tracer_pcode.authority.domains.loop_recurrence import LOOP_REASON_SPECS

    class Reached(Exception):
        pass

    class _Strategy:
        """証明書の検査の後の処理（strategy の他の method）に進んだら ``Reached``。"""

        enable_completed_recovery_proofs = True

        @staticmethod
        def _normalize_nested_tuple(value):
            return value

        def __getattr__(self, name):
            raise Reached(name)

    strategy = _Strategy()
    case1, case2 = object(), object()
    analysis = SimpleNamespace(completed_recovery_proof_evidence=())
    # recorder が記録まで進む reason と target の形（検査を外すと、記録の前の処理へ進む）。
    reason_id = "readonly_identity_missing" if module_name == "readonly_reduction" else next(iter(LOOP_REASON_SPECS))
    leading = (SimpleNamespace(reason_id=reason_id, object_target_key=("target", "a", "b", "c", "d")),) + (analysis,) * (arguments - 1)
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


# ---------------------------------------------------------------------------
# PR #253 review の反例: runtime ref の中の入力 VARIABLE・call effect の狭い引数
# ---------------------------------------------------------------------------


def _in_stack(name="in_stack_00000028"):
    return Expression.variable(name, size=8)


def test_an_input_variable_inside_a_runtime_ref_is_refused():
    """関数の入力の VARIABLE は、ref の中（loop の limit）でも左右を名前で同一視しない。"""

    left = _raw("f", [], _loop_value(_in_stack()))
    right = _raw("g", [], _loop_value(_in_stack()))
    with comparison_scope(comparison_binding_of(left, right)):
        verdict = owner_free_identity_gate((_case(left),), (_case(right),))
    assert not verdict.passed
    assert any("input_variable" in ref for ref in verdict.evidence_refs)
    constant_left = _raw("f", [], _loop_value(_c(5)))
    constant_right = _raw("g", [], _loop_value(_c(5)))
    with comparison_scope(comparison_binding_of(constant_left, constant_right)):
        assert owner_free_identity_gate((_case(constant_left),), (_case(constant_right),)).passed


def _placeholder(source):
    from scripts.function_tracer_pcode.analysis.recurrence.proof_utils import _impl__synthesized_loop_state_placeholder

    return _impl__synthesized_loop_state_placeholder(None, source, 8)


def _state_loop(binder, transition_leaf=None, limit=None):
    """状態遷移の loop: ``binder`` を宣言し、遷移 ``transition_leaf * 3``・上限 ``limit``。"""

    from scripts.function_tracer_pcode.core.runtime_refs import CountedStateTransitionLoopSummaryRef

    transition = Expression.binary_op("INT_MULT", binder if transition_leaf is None else transition_leaf, _c(3))
    limit = _c(5) if limit is None else limit
    ref = CountedStateTransitionLoopSummaryRef(
        initial_state=_c(1), start_expr=_c(1), limit_expr=limit, step_expr=_c(1),
        transition_expr=transition, state_placeholder=binder, state_size=8, result_size=8,
    )
    # operand には上限を置かない（上限は ref の field としてだけ届く: 束縛の範囲の規則だけを見る）。
    return Expression.intrinsic("COUNTED_STATE_TRANSITION_VALUE", [_c(1), _c(1), _c(5)], size=8, runtime_ref=ref, opcode=0xF001)


def _binder_gate(value_left, value_right=None):
    left = _raw("f", [], value_left)
    right = _raw("g", [], value_left if value_right is None else value_right)
    with comparison_scope(comparison_binding_of(left, right)):
        return owner_free_identity_gate((_case(left),), (_case(right),))


@pytest.mark.parametrize(("label", "build", "passes"), [
    # 正常な対照: loop 自身が宣言した状態の placeholder が、その遷移の中にある。
    ("own_binder_in_transition", lambda: _state_loop(_placeholder("s")), True),
    # review 3: 別の loop の状態の placeholder が、この loop の上限（束縛の外の field）にある。
    ("foreign_placeholder_in_limit", lambda: _loop_value(_placeholder("x")), False),
    ("own_binder_in_unscoped_limit", lambda: (lambda p: _state_loop(p, limit=p))(_placeholder("s")), False),
    # 別の binder（宣言と equals で一致しない placeholder）が遷移の中にある。
    ("other_binder_in_transition", lambda: _state_loop(_placeholder("s"), transition_leaf=_placeholder("t")), False),
    # 束縛の外へ漏れた placeholder（式の graph）。
    ("leaked_into_graph", lambda: Expression.binary_op("INT_ADD", _placeholder("s"), _state_loop(_placeholder("s"))), False),
    # 入れ子: 外側の遷移の中の内側の loop が、外側の binder を上限に使う（外側の束縛の中）。
    ("outer_binder_in_nested_limit", lambda: (lambda p: _state_loop(
        p, transition_leaf=Expression.binary_op("INT_ADD", p, _state_loop(_placeholder("i"), limit=p)),
    ))(_placeholder("o")), True),
    # shadowing: 内側が外側と同じ binder を宣言しても（内側の遷移の中で）束縛されたまま。
    ("shadowed_binder", lambda: (lambda p: _state_loop(
        p, transition_leaf=Expression.binary_op("INT_ADD", p, _state_loop(p)),
    ))(_placeholder("o")), True),
    # 外側の binder を、外側の束縛の外（上限）に置いた内側の loop が使う: 束縛の外。
    ("outer_binder_outside_its_scope", lambda: (lambda p: _state_loop(
        p, limit=_state_loop(_placeholder("i"), limit=p),
    ))(_placeholder("o")), False),
    # 入れ子: 内側の loop の遷移（内側の束縛の中）が外側の binder を使う（外側の束縛は内側でも有効）。
    ("outer_binder_in_nested_transition", lambda: (lambda p: _state_loop(
        p, transition_leaf=Expression.binary_op("INT_ADD", p, (lambda q: _state_loop(
            q, transition_leaf=Expression.binary_op("INT_ADD", q, p),
        ))(_placeholder("i"))),
    ))(_placeholder("o")), True),
    # review 3 r-c 1: 同じ合成の場所が別の loop に作った placeholder（別の loop）が、遷移の中にある。
    ("same_site_foreign_placeholder_in_transition", lambda: _state_loop(
        _placeholder("s"), transition_leaf=_placeholder("s"),
    ), False),
    # DAG: 同じ node が束縛の中（遷移）と外（上限）の両方から届く。
    ("shared_node_inside_and_outside", lambda: (lambda p: _state_loop(
        p, transition_leaf=p, limit=Expression.binary_op("INT_ADD", p, _c(0)),
    ))(_placeholder("s")), False),
])
def test_loop_variables_are_bound_only_where_their_ref_declares_them(label, build, passes):
    verdict = _binder_gate(build())
    assert verdict.passed is passes, (label, verdict.evidence_refs)
    if not passes:
        assert any("input_variable" in ref for ref in verdict.evidence_refs), verdict.evidence_refs


def test_loop_case_binders_cover_the_case_and_nothing_else():
    """counted loop の case が宣言した accumulator の placeholder は case の中でだけ束縛。"""

    from scripts.function_tracer_pcode.core.runtime_refs import LoopBodyEffectRef, LoopCaseRef

    def summed(case_binders, update_leaf):
        update = Expression.binary_op("INT_ADD", update_leaf, _c(1))
        case = LoopCaseRef(
            path_conditions=(),
            body_effect=LoopBodyEffectRef(kind="accumulator_update", source="pcode_summary", scope="loop", value_expr=update),
            term_expr=_c(1), case_kind="accumulator_delta", source="counted_loop_update_case",
            loop_binders=case_binders,
        )
        summary = LoopSummaryRef(
            start_expr=_c(0), limit_expr=_c(5), step_expr=_c(1),
            term_descriptor=LoopTermDescriptorRef(kind="constant", result_size=8, residue_cases=((1, 0, 0, 1),)),
            cases=(case,),
        )
        ref = CountedLoopSummaryRef(
            induction_step=1, result_size=8, signed_loop=True, residue_cases=((1, 0, 0, 1),), loop_summary=summary,
        )
        node = Expression(ExpressionType.INTRINSIC, name="counted_loop_sum", operands=[], size=8)
        node.runtime_ref = ref
        return node

    accumulator = _placeholder("acc")
    assert _binder_gate(summed((accumulator,), accumulator)).passed
    assert not _binder_gate(summed((), accumulator)).passed  # 宣言なし
    assert not _binder_gate(summed((accumulator,), _placeholder("other"))).passed  # 別の placeholder


def test_counterexample_1_an_input_variable_limit_is_not_equivalent_in_production():
    """修正前（42bc6b3c）は EQUIVALENT（RuntimeReductionClosureArtifact / OWNER_FREE を採用）。"""

    variable = _production(
        "prp-r3-variable-limit",
        _unpublished("f", [], _loop_value(_in_stack())),
        _unpublished("g", [], _loop_value(_in_stack())),
    )
    assert variable["final_outcome"] == "UNKNOWN"
    control = _production(
        "prp-r3-constant-limit",
        _unpublished("f", [], _loop_value(_c(5))),
        _unpublished("g", [], _loop_value(_c(5))),
    )
    assert control["final_outcome"] == "EQUIVALENT"


def _call_effect_check(argument_sizes):
    from unittest.mock import Mock

    from scripts.function_tracer_pcode.proof.strategies.pairwise import PairwiseStrategy
    from scripts.function_tracer_pcode.tests.unit import _sat_decisiveness_fixtures as fixtures
    from scripts.function_tracer_pcode.tests.unit._input_correspondence_support import echo_input_correspondence

    monkeypatch = pytest.MonkeyPatch()
    try:
        formula_builder = echo_input_correspondence(Mock())
        formula_builder.build_base_context.return_value = fixtures._base_context_for_single_int_param()
        runner = Mock()
        runner.timeout = 5
        strategy = PairwiseStrategy(formula_builder, runner, debug=False)
        left = fixtures._analysis_with_deferred_call_argument_blocker(function_name="func1", binary_id="B1", entry=0x1000)
        right = fixtures._analysis_with_deferred_call_argument_blocker(
            function_name="func2", binary_id="B14", entry=0x2000, argument_sizes=argument_sizes,
        )
        fixtures._patch_pairwise_single_unsat_case(monkeypatch, strategy, left, right)
        result = strategy.check(left, right)
    finally:
        monkeypatch.undo()
    evidence = [
        record for analysis in (left, right) for record in analysis.completed_recovery_proof_evidence
        if record.get("proof_source") == "matched_deferred_call_argument_evidence"
    ]
    return strategy, left, right, result, evidence


def test_counterexample_2_call_effect_evidence_is_not_recorded_for_narrow_call_arguments():
    """修正前は 32 bit と 16 bit で読む引数の照合を OWNER_FREE の証拠として記録・採用し、blocker を消した。"""

    _strategy, _left, _right, narrow, narrow_evidence = _call_effect_check({1: 2})
    assert narrow_evidence == []
    assert narrow.is_equivalent is not True
    _strategy, _left, _right, full, full_evidence = _call_effect_check(None)
    assert full.is_equivalent is True
    assert len(full_evidence) == 2
    for record in full_evidence:
        assert record[CROSS_SIDE_IDENTIFICATION_KEY] == CrossSideIdentification.OWNER_FREE.value
        assert issued_certificate(record[CROSS_SIDE_IDENTITY_CERTIFICATE_KEY]) is not None


def test_the_call_effect_certificate_reads_the_matched_call_surface_under_a_full_relation():
    """relation（pair 全体の述語）は満たしたまま、照合する call の引数だけを狭くする: 証明書は出ない。"""

    strategy, left, right, _result, _evidence = _call_effect_check(None)
    _strategy, _narrow_left, narrow_right, _narrow, _narrow_evidence = _call_effect_check({1: 2})
    subject = ("comparison_evidence", ("target",))
    with comparison_scope(comparison_binding_of(left, right)):
        assert positional_identity_gate(current_relation()).passed
        surface = strategy._call_effect_comparison_surface
        assert certify_owner_free_identity(surface(left), surface(right), subject=subject).passed
        refused = certify_owner_free_identity(surface(left), surface(narrow_right), subject=subject)
    assert not refused.passed and refused.certificate is None


def test_call_effect_evidence_with_a_borrowed_certificate_is_not_adopted():
    """記録を迂回して、別の対象の証明書を付けた OWNER_FREE の call effect 証拠は採用しない。"""

    _strategy, left, right, _result, evidence = _call_effect_check(None)
    comparison = comparison_binding_of(left, right)
    (record, *_rest) = evidence
    forged = dict(record)
    forged["object_target_key"] = ("another_call_target",)
    with comparison_scope(comparison):
        assert comparison_evidence((forged,)) == ()


def _state_transition_value(placeholder):
    from scripts.function_tracer_pcode.core.runtime_refs import CountedStateTransitionLoopSummaryRef

    transition = Expression.binary_op("INT_MULT", placeholder, _c(3))
    ref = CountedStateTransitionLoopSummaryRef(
        initial_state=_c(1), start_expr=_c(1), limit_expr=_c(5), step_expr=_c(1),
        transition_expr=transition, state_placeholder=placeholder, state_size=8, result_size=8,
    )
    return Expression.intrinsic("LOOP_STATE", (), size=8, runtime_ref=ref, opcode=0xF001)


def test_a_synthesized_loop_state_placeholder_is_bound_and_an_untagged_one_is_an_input():
    """summarizer が式から合成する状態の placeholder（乗算の漸化式など）も、ref の束縛を型で表す。
    名前（``__loop_state``）だけの placeholder は入力の VARIABLE と区別できないので拒否する。"""

    from scripts.function_tracer_pcode.analysis.recurrence import proof_utils

    tagged = proof_utils._impl__synthesized_loop_state_placeholder(None, "probe", 8)
    untagged = Expression.variable("__loop_state", size=8)
    left = _raw("f", [], _state_transition_value(tagged))
    right = _raw("g", [], _state_transition_value(proof_utils._impl__synthesized_loop_state_placeholder(None, "probe", 8)))
    with comparison_scope(comparison_binding_of(left, right)):
        assert owner_free_identity_gate((_case(left),), (_case(right),)).passed
    left_untagged = _raw("f", [], _state_transition_value(untagged))
    right_untagged = _raw("g", [], _state_transition_value(Expression.variable("__loop_state", size=8)))
    with comparison_scope(comparison_binding_of(left_untagged, right_untagged)):
        refused = owner_free_identity_gate((_case(left_untagged),), (_case(right_untagged),))
    assert not refused.passed
    assert any("input_variable" in ref and "__loop_state" in ref for ref in refused.evidence_refs)


def test_every_summarizer_placeholder_constructor_tags_its_binder():
    """``__loop_state`` の placeholder を作る全ての場所は、束縛の型を付ける helper を通る
    （名前だけの placeholder を新しく作ると、owner を含まない closure を全て拒否してしまう）。"""

    import ast

    from scripts.function_tracer_pcode.tests.unit._cross_binary_scan import PACKAGE_ROOT

    offenders = []
    for path in sorted((PACKAGE_ROOT / "analysis").rglob("*.py")):
        tree = ast.parse(path.read_text(encoding="utf-8"))
        for function in ast.walk(tree):
            if not isinstance(function, (ast.FunctionDef, ast.AsyncFunctionDef)):
                continue
            for node in ast.walk(function):
                if not isinstance(node, ast.Call) or getattr(node.func, "attr", None) != "variable":
                    continue
                if not (node.args and isinstance(node.args[0], ast.Constant) and node.args[0].value == "__loop_state"):
                    continue
                runtime_ref = next((keyword.value for keyword in node.keywords if keyword.arg == "runtime_ref"), None)
                if runtime_ref is None or (isinstance(runtime_ref, ast.Constant) and runtime_ref.value is None):
                    offenders.append((path.name, function.name))
    # 残るのは state_transition の entry guard の別名の置換（束縛の外に残った名前だけの別名を init へ
    # 戻す。placeholder を作らない）だけ。
    assert sorted(set(offenders)) == [("state_transition.py", "_impl__try_summarize_state_transition_loop")], offenders



def test_the_rewrite_proof_falls_back_to_the_solver_when_the_pair_is_not_certified(monkeypatch):
    """名前で比べる自明な一致は成り立つが、relation が入れ替えなので証明書が出ない: 構造の等価の receipt を
    作らず（作れず）、SMT の不等式 query（``rewrite-ineq``）へ戻る。"""

    from scripts.function_tracer_pcode.proof.strategies import pairwise_solver_proven_rewrite as rewrite
    from scripts.function_tracer_pcode.proof.strategies.pairwise_models import QueryResult

    left = _raw("f", [_d("n", 0), _d("m", 1)], _p("n", 0))
    right = _raw("g", [_d("m", 0), _d("n", 1)], _p("n", 1))
    monkeypatch.setattr(rewrite, "_build_rewrite_candidate", lambda expr, _settings: expr.clone_with())
    monkeypatch.setattr(rewrite, "_expr_signature", lambda expr: id(expr))
    monkeypatch.setattr(rewrite, "_prove_rewrite", lambda *_a, **_k: object())
    monkeypatch.setattr(rewrite, "build_pair_query", lambda *_a, **_k: "(check-sat)")
    solved = []
    strategy = SimpleNamespace(
        debug=False, solver_proven_rewrite_settings=None,
        _solve_query_internal=lambda query, pair_id, **_k: solved.append(pair_id) or QueryResult(None),
    )
    ctx = {"return_size1": 64, "return_size2": 64}
    with comparison_scope(comparison_binding_of(left, right)):
        assert rewrite._rewritten_values_are_trivially_equal(strategy, ctx, _case(left), _case(right))
        result = rewrite.try_solver_proven_rewrite_equivalence(
            strategy, ctx, _case(left), _case(right), None, None, "(0,0)",
        )
    assert result.pair_stage == "rewrite-ineq"
    assert solved == ["(0,0)"]
    assert getattr(result, "structural_equality_receipt", None) is None


def test_the_deferred_call_lowering_reads_the_call_surface_under_a_full_relation():
    """relation（pair 全体の述語）は満たしたまま、右の call の引数だけを狭く読む: lowering しない。"""

    from unittest.mock import Mock

    from scripts.function_tracer_pcode.proof.strategies.pairwise import PairwiseStrategy
    from scripts.function_tracer_pcode.tests.unit import _sat_decisiveness_fixtures as fixtures

    def analysis(name, binary_id, entry, sizes=None):
        return fixtures._analysis_with_deferred_call_argument_blocker(
            function_name=name, binary_id=binary_id, entry=entry, return_deferred_unknown=True,
            argument_indices=(1,), argument_sizes=sizes,
        )

    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    # production の analysis は公開済み（``publish_raw_function_analysis``）。証明書は不変の値だけを記録する。
    left, right, narrow = (
        publish_raw_function_analysis(analysis("func1", "B1", 0x1000)),
        publish_raw_function_analysis(analysis("func2", "B14", 0x2000)),
        publish_raw_function_analysis(analysis("func2", "B14", 0x2000, {1: 2})),
    )
    with comparison_scope(comparison_binding_of(left, right)):
        assert positional_identity_gate(current_relation()).passed

        def lowering(right_analysis):
            return strategy._try_build_unresolved_deferred_call_lowering(
                base_ctx={"analysis1": left, "analysis2": right_analysis},
                case1=extract_return_cases(left)[0], case2=extract_return_cases(right)[0], pair_id="(0,0)",
            )

        assert lowering(right) is not None
        assert lowering(narrow) is None


def test_record_pair_closed_refuses_query_assertions_whose_certificate_is_not_their_pair(monkeypatch):
    """artifact が自分の証明書を持っていても、等式の証明書がこの pair・この比較のものでなければ閉じない
    （``base_ctx`` に直接書いた等式・別の pair の証明書）。"""

    from scripts.function_tracer_pcode.proof.strategies.pairwise_services.orchestration import record_pair_closed

    comparison = _positional_comparison_binding()
    binding = _binding(comparison)
    artifact = _producer_artifact(binding, monkeypatch, _certificate(("pair", "(0,0)"), comparison))
    for foreign in (None, _certificate(("pair", "(0,1)"), comparison)):
        ledger = PairDispositionLedger(binding, 1)
        with pytest.raises(ValueError):
            record_pair_closed(
                ledger, {
                    "pairwise_extra_assertions_by_pair": {"(0,0)": ("(assert (= l r))",)},
                    "pairwise_extra_assertion_certificates_by_pair": {"(0,0)": foreign},
                },
                (0, 0), PairClosureKind.RECOVERY, binding, artifact,
            )
        assert (0, 0) not in ledger.closures


def test_a_hand_built_closure_with_a_recomputed_digest_does_not_validate(monkeypatch):
    """``validated`` を迂回して作った closure（digest は公開の値から計算し直せる）は、申告の下限と
    証明書の照合で検証を通らない。"""

    import hashlib

    comparison = _positional_comparison_binding()
    binding = _binding(comparison)
    certificate = _certificate(("pair", "(0,0)"), comparison)
    artifact = _producer_artifact(binding, monkeypatch, certificate)

    def forged(identification, identity_certificate):
        certificate_id = None if identity_certificate is None else identity_certificate.certificate_id
        digest = hashlib.sha256(repr((
            binding.stable_key(), artifact.stable_key(), (), (), (), identification.value, certificate_id,
        )).encode()).hexdigest()
        return PairClosureEvidence(
            (0, 0), ledger_module.PairDisposition.UNSAT, PairClosureKind.RECOVERY, binding.stable_key(),
            artifact, digest, (), (), (), identification, identity_certificate,
        )

    assert forged(CrossSideIdentification.OWNER_FREE, certificate).validates(binding)
    # owner を含まない種類の closure を CORRESPONDENCE と申告する
    assert not forged(CrossSideIdentification.CORRESPONDENCE, None).validates(binding)
    # 別の pair の証明書
    assert not forged(CrossSideIdentification.OWNER_FREE, _certificate(("pair", "(0,1)"), comparison)).validates(binding)


def test_a_direct_pairwise_check_without_a_dispatch_frame_applies_the_veto(monkeypatch):
    """互換の直接呼び出し（dispatch frame なし）: ledger に証明書の無い owner を含まない closure があれば
    ``strategy.check`` の結果が EQ にならず、reason が残る。"""

    result, _base_ctx = _lowering_check(monkeypatch, ("fp", "a", "b"))
    assert result.is_equivalent is True
    monkeypatch.setattr(PairDispositionLedger, "owner_free_closures", lambda _self: (((0, 0), None),))
    vetoed, _base_ctx = _lowering_check(monkeypatch, ("fp", "a", "b"))
    assert vetoed.is_equivalent is None
    assert "cross_side_identity_unproven" in {reason.reason_id for reason in vetoed.unknown_reasons}


# ---------------------------------------------------------------------------
# PR #253 review 3: 束縛の範囲・検査した値・証明書の寿命
# ---------------------------------------------------------------------------


def test_counterexample_3_certificates_are_released_with_their_session():
    """修正前（76538746）は発行した証明書を process 全体の台帳が強参照で持ち続けた（1,000 件発行・
    scope を抜けて GC しても 1,000 件残る）。今は session が持ち、いちばん外側の実行が終わると全て失効する。"""

    import gc

    from scripts.function_tracer_pcode.proof.formula.input_correspondence.certificates import (
        certificate_session,
        current_certificate_session,
        entered_certificate_session,
    )

    comparison = _positional_comparison_binding()
    with entered_certificate_session(None):
        with certificate_session() as session:
            certificates = [
                _certificate(("pair", f"({index},0)"), comparison) for index in range(1000)
            ]
            assert len(session) == 1000
            # 入れ子の実行（recurrence の再帰・retry・branch）は同じ session を使い、失効させない。
            with certificate_session() as nested:
                assert nested is session
            assert len(session) == 1000 and all(item.is_issued() for item in certificates)
        assert current_certificate_session() is None
        gc.collect()
        assert len(session) == 0
        with certificate_session():
            assert not any(item.is_issued() for item in certificates)


def test_counterexample_1_a_foreign_loop_placeholder_is_not_equivalent_in_production():
    """修正前（76538746）は、別の loop の状態の placeholder を上限に置いた loop の比較が EQUIVALENT。"""

    foreign = _production(
        "prp-r5-foreign-placeholder",
        _unpublished("f", [], _loop_value(_placeholder("x"))),
        _unpublished("g", [], _loop_value(_placeholder("x"))),
    )
    assert foreign["final_outcome"] == "UNKNOWN"
    own = _production(
        "prp-r5-own-binder",
        _unpublished("f", [], _state_loop(_placeholder("s"))),
        _unpublished("g", [], _state_loop(_placeholder("s"))),
    )
    assert own["final_outcome"] == "EQUIVALENT"


def test_an_evidence_backed_closure_reads_only_evidence_made_from_its_own_pair(monkeypatch):
    """同じ object_target_key の証拠でも、別の pair の値で作ったものでは closure を発行しない。"""

    from scripts.function_tracer_pcode.proof.obligations import pair_closure_producers as producers

    comparison = _positional_comparison_binding()
    binding = _binding(comparison)
    pair_x = _pair_values()
    pair_y = _pair_values()
    record, _certificate_value, _checked = _owner_free_record(comparison, checked=pair_x)
    analysis = SimpleNamespace(completed_recovery_proof_evidence=(record,))

    def proof(_reason, analysis1, _analysis2):
        return bool(comparison_evidence(analysis1.completed_recovery_proof_evidence))

    monkeypatch.setattr(producers, "_fixed_proof_implementation", lambda *_a: proof)
    with comparison_scope(comparison):
        for values, expected in ((pair_y, None), (pair_x, "issued")):
            candidate = producers.MethodBClosureCandidate.create(binding, "(0,0)", ("target",), ())
            artifact = producers.validate_method_b_candidate(
                None, binding, candidate, None, analysis, analysis, values[0][0], values[1][0],
            )
            assert (artifact is not None) == (expected == "issued")


def test_only_the_gate_issues_certificates_and_only_derive_builds_query_equalities():
    """発行の入口は 1 つずつ（新しい producer は共通の API を通る）。"""

    import ast

    from scripts.function_tracer_pcode.tests.unit._cross_binary_scan import PACKAGE_ROOT

    callers = {"issue_certificate": set(), "OwnerFreePairAssertions": set()}
    for path in PACKAGE_ROOT.rglob("*.py"):
        if "tests" in path.relative_to(PACKAGE_ROOT).parts:
            continue
        tree = ast.parse(path.read_text(encoding="utf-8"))
        for function in ast.walk(tree):
            if not isinstance(function, (ast.FunctionDef, ast.AsyncFunctionDef)):
                continue
            for node in ast.walk(function):
                if isinstance(node, ast.Call):
                    name = node.func.attr if isinstance(node.func, ast.Attribute) else getattr(node.func, "id", "")
                    if name in callers:
                        callers[name].add((path.name, function.name))
    assert callers["issue_certificate"] == {("gate.py", "certify_owner_free_identity")}
    assert callers["OwnerFreePairAssertions"] == {("certificates.py", "derive_owner_free_pair_assertions")}



def test_synthesized_placeholders_are_distinct_per_construction():
    """合成した状態の placeholder は 1 回ごとに別の binder（同じ場所・同じ幅でも ``equals`` で一致しない）。"""

    first, second = _placeholder("s"), _placeholder("s")
    assert not first.equals(second)
    assert first.equals(first)


def test_counted_loop_case_refs_declare_the_accumulator_binders():
    """counted loop の producer は case に accumulator の placeholder を binder として宣言する。"""

    from scripts.function_tracer_pcode.analysis.recurrence.counted_loop import _impl__build_counted_loop_case_refs
    from scripts.function_tracer_pcode.analysis.recurrence.models import CountedLoopUpdateCase

    accumulator = _placeholder("acc")
    update = CountedLoopUpdateCase(
        conditions=(), update_expr=Expression.binary_op("INT_ADD", accumulator, _c(1)), delta_expr=_c(1),
    )
    (case,) = _impl__build_counted_loop_case_refs(None, (update,), loop_binders=(accumulator,))
    assert case.loop_binders == (accumulator,)
    scope = case.loop_binder_scope()
    assert scope.binders == (accumulator,) and "body_effect" in scope.scoped_fields
    (undeclared,) = _impl__build_counted_loop_case_refs(None, (update,))
    assert undeclared.loop_binder_scope() is None


def test_a_certificate_is_not_issued_for_values_that_may_still_change():
    """証明書は読んだ値そのものを記録するので、不変でない（未検証の）値には発行しない。"""

    from scripts.function_tracer_pcode.core.semantic_lifecycle import is_validated

    left, right = _p("n", 0), _p("n", 0)  # 組み立て中（CONSTRUCTION）の値
    assert not is_validated(left)
    with comparison_scope(comparison_binding_of(_raw("f", [_d("n", 0)], _p("n", 0)), _raw("g", [_d("n", 0)], _p("n", 0)))):
        refused = certify_owner_free_identity((left,), (right,), subject=("pair", "(0,0)"))
    assert not refused.passed
    assert any("checked_value_not_frozen" in ref for ref in refused.evidence_refs)


def test_a_surface_records_the_binder_context_of_each_read():
    """同じ値でも、束縛された位置で読んだ証明書は、自由な位置で読む値には使えない。"""

    from scripts.function_tracer_pcode.core.runtime_refs import LoopBodyEffectRef, LoopCaseRef
    from scripts.function_tracer_pcode.core.semantic_freeze import publish_semantic_values

    accumulator = _placeholder("acc")
    case = LoopCaseRef(
        body_effect=LoopBodyEffectRef(kind="accumulator_update", source="t", scope="loop", value_expr=accumulator),
        term_expr=_c(1), loop_binders=(accumulator,),
    )
    publish_semantic_values(case)
    comparison = _positional_comparison_binding()
    certificate = _certificate(("pair", "(0,0)"), comparison, (case,), (case,))
    assert certificate.attests((case,), (case,))
    # 同じ placeholder を束縛の外で読む値（自由な入力）には使えない。
    assert not certificate.attests((accumulator,), (accumulator,))


def test_a_direct_checker_call_owns_its_certificate_session():
    """checker を直接呼ぶ経路（workflow の外）も、strategy の branch が証明書の session を持つ:
    閉じた closure の証明書を最終 gate が照合できる（session が早く閉じると EQ が UNKNOWN になる）。"""

    from scripts.function_tracer_pcode.checker.checker import EquivalenceChecker
    from scripts.function_tracer_pcode.proof.formula.input_correspondence.certificates import (
        entered_certificate_session,
    )

    left, right = _a04_cases()["identity_eq_control"]
    with entered_certificate_session(None):
        result = EquivalenceChecker(timeout=5).check(
            publish_raw_function_analysis(left), publish_raw_function_analysis(right), "left", "right",
        )
    assert result.is_equivalent is True, [getattr(r, "reason_id", None) for r in result.unknown_reasons]

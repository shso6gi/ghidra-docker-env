"""Issue #20 PR-D: ABI 引数抽出と fresh 引数の soundness を固定する。

M-20 で確認した blocker（引数は観測できるのに ``CallArgumentEvidence`` 行が
作られない callsite）が ABI 証拠で埋まること、そして

* identity correspondence
* value coupling
* proof irrelevance

の三つが混ざらないことを test で固定する。
"""

from __future__ import annotations

import pytest

from scripts.function_tracer_pcode.core import (
    AbiArgumentSlotRef,
    CallTargetRef,
    Expression,
    FreshCallArgumentRef,
    StorageInfo,
)
from scripts.function_tracer_pcode.core.runtime_refs import (
    fresh_call_argument_refs_are_side_distinct,
)
from scripts.function_tracer_pcode.core.runtime_refs.pcode import PcodeOpRef
from scripts.function_tracer_pcode.analysis.effects import call_argument_abi as abi
from scripts.function_tracer_pcode.analysis.effects.models import CallArgumentEvidence
from scripts.function_tracer_pcode.proof.call_effect.candidates import (
    CALLEE_PROOF_FIELDS_EXCLUDED_FROM_CANDIDATE_IDENTITY,
    CALLEE_RETURN_SUMMARY_UNPROVEN,
    CALLSITE_ARGUMENT_RELATION_MISSING,
    CALLSITE_CALLEE_CORRESPONDENCE_MISSING,
    CALLSITE_CANDIDATE_MISSING,
    CANDIDATE_SHAPE_AMBIGUOUS,
    build_internal_call_correspondence_candidates,
    confirm_internal_callsite_correspondence,
    internal_candidate_inputs,
)
from scripts.function_tracer_pcode.proof.call_effect.fresh_arguments import (
    FRESH_ARGUMENT_STATUS_INDEPENDENT,
    FreshArgumentIdentityCorrespondence,
    FreshArgumentIrrelevanceProof,
    RelationalEqualityProof,
    couple_fresh_arguments,
    discharge_fresh_argument_blockers,
    fresh_argument_correspondence_status,
    fresh_arguments_are_independent,
)
from scripts.function_tracer_pcode.proof.call_effect.obligations import CallSiteFact
from scripts.function_tracer_pcode.proof.call_effect.obligations import (
    ArtifactObjectIdentity,
)


# --------------------------------------------------------------------------
# fakes
# --------------------------------------------------------------------------


def _register_storage(name: str, offset: int, size: int = 8) -> StorageInfo:
    return StorageInfo(
        is_register=True,
        space_name="register",
        offset=offset,
        size=size,
        size_bits=size * 8,
        register_name=name,
        register_offset=offset,
        register_size=size,
        register_size_bits=size * 8,
        base_register_name=name,
        base_register_offset=offset,
        base_register_size=size,
        base_register_size_bits=size * 8,
    )


class _Varnode:
    def __init__(self, size: int, storage=None, expression=None):
        self._size = size
        self.storage = storage
        self.expression = expression

    def getSize(self):
        return self._size

    def getDef(self):
        return None

    def getHigh(self):
        return None


class _Seqnum:
    def __init__(self, offset, order):
        self._offset = offset
        self._order = order

    def getTarget(self):
        return None

    def getOrder(self):
        return self._order

    def getTime(self):
        return self._order


class _CallOp:
    def __init__(self, inputs, offset=0x1000):
        # input 0 is the call target; 1..n are the arguments.
        self._inputs = [_Varnode(8)] + list(inputs)
        self._seqnum = _Seqnum(offset, 1)

    def getMnemonic(self):
        return "CALL"

    def getNumInputs(self):
        return len(self._inputs)

    def getInput(self, index):
        return self._inputs[index]

    def getSeqnum(self):
        return self._seqnum


class _Tracer:
    def __init__(self, binary_id="binaryL", pcode_key=("pcode_op", "binaryL", 0x1000)):
        self._function_binary_id = binary_id
        self._pcode_key = pcode_key

    def _get_storage_info_from_varnode(self, varnode):
        return getattr(varnode, "storage", None)

    def trace_varnode(self, varnode, use_cache=False, depth=0):
        expression = getattr(varnode, "expression", None)
        if expression is not None:
            return expression
        return Expression.variable("opaque", size=varnode.getSize())

    def _make_pcode_op_ref(self, _op):
        return PcodeOpRef(
            binary_id=self._function_binary_id,
            address_offset=0x1000,
            seq_order=1,
            seq_time=1,
            mnemonic="CALL",
            opcode=7,
            function_entry_space="ram",
            function_entry_offset=0x100,
        )


def _callee_parameter(index, name, storage, data_type="double"):
    return {
        "index": index,
        "name": name,
        "data_type": data_type,
        "size": storage.size,
        "storage": storage,
        "owner_program_id": 4242,
        "owner_entry_offset": 0x2000,
    }


def _target_ref():
    return CallTargetRef.from_name(
        "callee",
        program_id=4242,
        entry_offset=0x2000,
        is_external=False,
    )


# --------------------------------------------------------------------------
# 1. ABI extraction recovers a call site whose evidence row was never created
# --------------------------------------------------------------------------


def test_abi_recovers_evidence_for_call_site_without_an_evidence_row():
    """M-20 の blocker: 引数は観測できるが evidence 行が無い callsite。

    ABI 証拠（宣言ストレージ + callsite 引数リスト）だけで
    ``CallArgumentEvidence`` を作れる。
    """

    tracer = _Tracer()
    argument = Expression.variable("x", size=8)
    call_op = _CallOp([_Varnode(8, storage=_register_storage("d1", 0x5020), expression=argument)])
    callee_parameters = [_callee_parameter(0, "__x", _register_storage("d0", 0x5000))]

    evidence, reason = abi._impl__recover_abi_call_argument_evidence(
        call_op,
        tracer,
        [],
        callee_parameters,
        _target_ref(),
        binary_id="binaryL",
    )

    assert reason is None
    assert evidence is not None
    assert len(evidence.arguments) == 1
    assert len(evidence.callee_param_identities) == 1
    assert evidence.coverage_complete is True
    assert evidence.recovery_status == CallArgumentEvidence.RECOVERY_COMPLETE
    # 宣言ストレージ(d0) と callsite 入力(d1) が違っても、arity と幅が一致する
    # 限り Ghidra の引数順契約を authority にする（tier B）。
    assert evidence.sources == (abi.ABI_AUTHORITY_CALLSITE_PROTOTYPE_SLOTS,)
    assert len(evidence.abi_argument_slots) == 1
    assert evidence.abi_argument_slots[0].ordinal == 0
    assert evidence.abi_argument_slots[0].width_bits == 64
    assert evidence.fresh_argument_refs == ()


def test_abi_uses_declared_storage_authority_when_the_callsite_keeps_abi_registers():
    tracer = _Tracer()
    storage = _register_storage("d0", 0x5000)
    call_op = _CallOp([_Varnode(8, storage=storage, expression=Expression.variable("x", size=8))])
    callee_parameters = [_callee_parameter(0, "__x", storage)]

    resolution, reason = abi._impl__resolve_abi_call_arguments(
        call_op,
        tracer,
        [],
        callee_parameters,
        binary_id="binaryL",
        call_site_key=("pcode_op", "binaryL", 0x1000),
    )

    assert reason is None
    assert resolution is not None
    assert resolution.authority_source == abi.ABI_AUTHORITY_CALLEE_DECLARED_STORAGE


def test_abi_evidence_does_not_claim_unconditional_execution():
    """guard が分からないときに空の guard group を積まない。

    空 group を 1 つ積むと「無条件で実行される」と読めてしまう。
    """

    tracer = _Tracer()
    call_op = _CallOp([_Varnode(8, storage=_register_storage("d1", 0x5020))])
    callee_parameters = [_callee_parameter(0, "__x", _register_storage("d0", 0x5000))]

    evidence, _reason = abi._impl__recover_abi_call_argument_evidence(
        call_op, tracer, [], callee_parameters, _target_ref(), binary_id="binaryL"
    )

    assert evidence is not None
    assert evidence.path_conditions == ()


# --------------------------------------------------------------------------
# 2. fail closed when the ABI cannot be determined
# --------------------------------------------------------------------------


def test_abi_fails_closed_when_the_callee_parameter_has_no_concrete_storage():
    tracer = _Tracer()
    call_op = _CallOp([_Varnode(8, storage=_register_storage("d0", 0x5000))])
    callee_parameters = [
        {
            "index": 0,
            "name": "__x",
            "data_type": "double",
            "size": 8,
            "storage": None,
            "owner_program_id": 4242,
            "owner_entry_offset": 0x2000,
        }
    ]

    evidence, reason = abi._impl__recover_abi_call_argument_evidence(
        call_op, tracer, [], callee_parameters, _target_ref(), binary_id="binaryL"
    )

    assert evidence is None
    assert reason == abi.ABI_PARAMETER_STORAGE_MISSING


def test_abi_fails_closed_on_argument_arity_mismatch():
    """宣言 2 引数に対し callsite が 1 引数。位置で埋めない。"""

    tracer = _Tracer()
    call_op = _CallOp([_Varnode(8, storage=_register_storage("d7", 0x5070))])
    callee_parameters = [
        _callee_parameter(0, "a", _register_storage("d0", 0x5000)),
        _callee_parameter(1, "b", _register_storage("d1", 0x5020)),
    ]

    evidence, reason = abi._impl__recover_abi_call_argument_evidence(
        call_op, tracer, [], callee_parameters, _target_ref(), binary_id="binaryL"
    )

    assert evidence is None
    assert reason == abi.ABI_CALLSITE_ARITY_MISMATCH


def test_abi_fails_closed_on_argument_width_mismatch():
    tracer = _Tracer()
    call_op = _CallOp([_Varnode(4, storage=_register_storage("w1", 0x5020, size=4))])
    callee_parameters = [_callee_parameter(0, "__x", _register_storage("d0", 0x5000))]

    evidence, reason = abi._impl__recover_abi_call_argument_evidence(
        call_op, tracer, [], callee_parameters, _target_ref(), binary_id="binaryL"
    )

    assert evidence is None
    assert reason == abi.ABI_CALLSITE_WIDTH_MISMATCH


def test_abi_fails_closed_when_the_call_target_is_unresolved():
    tracer = _Tracer()
    call_op = _CallOp([_Varnode(8, storage=_register_storage("d0", 0x5000))])
    callee_parameters = [_callee_parameter(0, "__x", _register_storage("d0", 0x5000))]

    evidence, reason = abi._impl__recover_abi_call_argument_evidence(
        call_op, tracer, [], callee_parameters, CallTargetRef.unknown(), binary_id="binaryL"
    )

    assert evidence is None
    assert reason == abi.ABI_UNRESOLVED_TARGET


def test_abi_fails_closed_without_any_callee_parameters():
    tracer = _Tracer()
    call_op = _CallOp([_Varnode(8, storage=_register_storage("d0", 0x5000))])

    evidence, reason = abi._impl__recover_abi_call_argument_evidence(
        call_op, tracer, [], [], _target_ref(), binary_id="binaryL"
    )

    assert evidence is None
    assert reason == abi.ABI_NO_CALLEE_PARAMETERS


# --------------------------------------------------------------------------
# 3. fresh arguments: identity correspondence != value coupling
# --------------------------------------------------------------------------


def _fresh_pair(ordinal=0, width_bits=64):
    slot = AbiArgumentSlotRef(
        ordinal=ordinal,
        storage_class="register",
        width_bits=width_bits,
        storage_identity_key=("register", "d0", 8),
        declared_type_name="double",
    )
    left = FreshCallArgumentRef(binary_id="binaryL", slot=slot, call_site_key=("op", 1))
    right = FreshCallArgumentRef(binary_id="binaryR", slot=slot, call_site_key=("op", 1))
    return left, right


def test_matching_abi_slot_does_not_couple_fresh_values():
    """``log(x)`` と ``log(x + 1)`` 相当。

    ordinal / storage / 幅が完全に一致しても、それは対応候補であって
    値の一致ではない。証明が無ければ左右は別シンボルのまま。
    """

    left, right = _fresh_pair()

    assert left.identity_correspondence_key() == right.identity_correspondence_key()
    assert FreshArgumentIdentityCorrespondence(left=left, right=right).is_valid() is True
    assert fresh_call_argument_refs_are_side_distinct(left, right) is True
    assert left.stable_key() != right.stable_key()

    assert couple_fresh_arguments(left, right) is None
    assert couple_fresh_arguments(left, right, proof=None) is None
    assert fresh_arguments_are_independent(left, right) is True


def test_undischarged_relational_proof_does_not_couple():
    left, right = _fresh_pair()
    proof = RelationalEqualityProof(
        proof_id="p1",
        left_key=left.stable_key(),
        right_key=right.stable_key(),
        premise_digest="digest",
        discharged=False,
    )

    assert couple_fresh_arguments(left, right, proof) is None


def test_relational_equality_proof_enables_coupling():
    left, right = _fresh_pair()
    proof = RelationalEqualityProof(
        proof_id="p1",
        left_key=left.stable_key(),
        right_key=right.stable_key(),
        premise_digest="digest",
        obligation_id="ob1",
        discharged=True,
    )

    coupling = couple_fresh_arguments(left, right, proof)

    assert coupling is not None
    assert coupling.coupled_symbol_key() is not None
    assert fresh_arguments_are_independent(left, right, coupling) is False


def test_relational_proof_for_other_values_does_not_couple():
    left, right = _fresh_pair()
    other_left, _other_right = _fresh_pair(ordinal=1)
    proof = RelationalEqualityProof(
        proof_id="p1",
        left_key=other_left.stable_key(),
        right_key=right.stable_key(),
        premise_digest="digest",
        discharged=True,
    )

    assert couple_fresh_arguments(left, right, proof) is None


# --------------------------------------------------------------------------
# 4. proof irrelevance: discharge the blocker, keep the symbols apart
# --------------------------------------------------------------------------


def test_irrelevant_fresh_value_discharges_a_blocker_without_coupling():
    left, right = _fresh_pair()
    predicate = ("decisive", "return_relation")
    proofs = [
        FreshArgumentIrrelevanceProof(
            proof_id="irr-left",
            fresh_key=left.stable_key(),
            decisive_predicate_key=predicate,
            discharged=True,
        )
    ]

    discharged, undischarged = discharge_fresh_argument_blockers([left], predicate, proofs)

    assert discharged is True
    assert undischarged == ()
    # irrelevance は coupling ではない: シンボルは独立のまま。
    assert couple_fresh_arguments(left, right) is None
    assert fresh_arguments_are_independent(left, right) is True
    assert left.stable_key() != right.stable_key()


def test_irrelevance_proof_does_not_cover_a_different_predicate():
    left, _right = _fresh_pair()
    proofs = [
        FreshArgumentIrrelevanceProof(
            proof_id="irr-left",
            fresh_key=left.stable_key(),
            decisive_predicate_key=("decisive", "return_relation"),
            discharged=True,
        )
    ]

    discharged, undischarged = discharge_fresh_argument_blockers(
        [left], ("decisive", "memory_relation"), proofs
    )

    assert discharged is False
    assert undischarged == (tuple(left.stable_key()),)


def test_partial_irrelevance_cover_leaves_the_blocker_in_place():
    left, _right = _fresh_pair(ordinal=0)
    second, _ = _fresh_pair(ordinal=1)
    predicate = ("decisive", "return_relation")
    proofs = [
        FreshArgumentIrrelevanceProof(
            proof_id="irr-0",
            fresh_key=left.stable_key(),
            decisive_predicate_key=predicate,
            discharged=True,
        )
    ]

    discharged, undischarged = discharge_fresh_argument_blockers(
        [left, second], predicate, proofs
    )

    assert discharged is False
    assert undischarged == (tuple(second.stable_key()),)


def test_fresh_argument_status_reports_independence():
    left, right = _fresh_pair()

    assert (
        fresh_argument_correspondence_status([left.stable_key()], [right.stable_key()])
        == FRESH_ARGUMENT_STATUS_INDEPENDENT
    )


# --------------------------------------------------------------------------
# 5. internal call-site candidate matching
# --------------------------------------------------------------------------


def _internal_call_fact(fact_id, binary_id, argument_shape, pcode_offset, **overrides):
    fields = dict(
        fact_id=fact_id,
        identity=ArtifactObjectIdentity(
            binary_id=binary_id,
            function_key=("function", binary_id, 0x100),
            pcode_op_key=("pcode_op", binary_id, pcode_offset),
        ),
        operation_kind="direct_call",
        target_candidates=(("function", binary_id, 0x2000),),
        target_categories=("internal_function",),
        target_resolution_status="resolved",
        argument_keys=(("expression", "arg"),),
        argument_shape_keys=(argument_shape,),
        callee_parameter_keys=((("parameter_storage", "d0"),),),
        abi_argument_slot_keys=((("abi_argument_slot", 0, "register", 64),),),
        extraction_status="complete",
    )
    fields.update(overrides)
    return CallSiteFact(**fields)


def test_internal_candidate_forms_without_any_callee_return_or_effect_proof():
    left = _internal_call_fact("L1", "binaryL", ("shape", "a"), 0x1000)
    right = _internal_call_fact("R1", "binaryR", ("shape", "a"), 0x2000)

    result = build_internal_call_correspondence_candidates([left], [right])

    assert len(result.candidates) == 1
    candidate = result.candidates[0]
    assert candidate.left_fact_id == "L1"
    assert candidate.right_fact_id == "R1"
    # 候補形成の入力に callee return / effect の事実は含まれない。
    projection = internal_candidate_inputs(left)
    for field_name in CALLEE_PROOF_FIELDS_EXCLUDED_FROM_CANDIDATE_IDENTITY:
        assert field_name not in projection


def test_internal_candidate_identity_ignores_callee_return_and_effect_facts():
    left = _internal_call_fact("L1", "binaryL", ("shape", "a"), 0x1000)
    right = _internal_call_fact("R1", "binaryR", ("shape", "a"), 0x2000)
    baseline = build_internal_call_correspondence_candidates([left], [right]).candidates[0]

    enriched_left = _internal_call_fact(
        "L1",
        "binaryL",
        ("shape", "a"),
        0x1000,
        callee_return_shape_keys=((("return", "int32"),),),
        callee_return_summary_statuses=("complete",),
        callee_effect_summary_statuses=("complete",),
        callee_memory_effect_counts=(3,),
        callee_has_unsupported_nested_call=True,
    )
    enriched = build_internal_call_correspondence_candidates([enriched_left], [right]).candidates[0]

    assert enriched.stable_key() == baseline.stable_key()


def test_ambiguous_internal_candidates_fail_closed():
    left_a = _internal_call_fact("L1", "binaryL", ("shape", "a"), 0x1000)
    left_b = _internal_call_fact("L2", "binaryL", ("shape", "a"), 0x1010)
    right_a = _internal_call_fact("R1", "binaryR", ("shape", "a"), 0x2000)
    right_b = _internal_call_fact("R2", "binaryR", ("shape", "a"), 0x2010)

    result = build_internal_call_correspondence_candidates(
        [left_a, left_b], [right_a, right_b]
    )

    assert result.candidates == ()
    assert {reason for _fact_id, reason in result.unmatched_reasons} == {CANDIDATE_SHAPE_AMBIGUOUS}


def test_external_call_sites_are_not_internal_candidates():
    left = _internal_call_fact(
        "L1", "binaryL", ("shape", "a"), 0x1000, target_categories=("external_function",)
    )
    right = _internal_call_fact(
        "R1", "binaryR", ("shape", "a"), 0x2000, target_categories=("external_function",)
    )

    result = build_internal_call_correspondence_candidates([left], [right])

    assert result.candidates == ()


def test_candidate_slot_keys_are_only_carried_when_both_sides_agree():
    left = _internal_call_fact("L1", "binaryL", ("shape", "a"), 0x1000)
    right = _internal_call_fact(
        "R1",
        "binaryR",
        ("shape", "a"),
        0x2000,
        abi_argument_slot_keys=((("abi_argument_slot", 0, "stack", 64),),),
    )

    candidate = build_internal_call_correspondence_candidates([left], [right]).candidates[0]

    assert candidate.abi_argument_slot_keys == ()


# --------------------------------------------------------------------------
# 6. the fresh-argument DTO invariant itself
# --------------------------------------------------------------------------


def test_fresh_call_argument_requires_a_typed_slot():
    with pytest.raises(TypeError):
        FreshCallArgumentRef(binary_id="binaryL", slot=("abi", 0))


def test_fresh_call_argument_expression_symbols_differ_between_sides():
    from scripts.function_tracer_pcode.core.render_smt.unknowns import (
        collect_unknown_smt_declarations,
    )

    left, right = _fresh_pair()
    left_expr = abi._impl__fresh_call_argument_expression(left)
    right_expr = abi._impl__fresh_call_argument_expression(right)

    left_declarations = collect_unknown_smt_declarations(left_expr)
    right_declarations = collect_unknown_smt_declarations(right_expr)

    assert left_declarations and right_declarations
    # 同じ ABI スロットでも SMT シンボルは別物でなければならない。
    assert left_declarations[0][0] != right_declarations[0][0]
    assert left_declarations[0][1] == right_declarations[0][1] == 64


def test_collect_fresh_call_argument_refs_walks_operands():
    left, _right = _fresh_pair()
    fresh_expr = abi._impl__fresh_call_argument_expression(left)
    composite = Expression.binary_op("FLOAT_ADD", fresh_expr, Expression.variable("y", size=8))

    found = abi._impl__collect_fresh_call_argument_refs(composite)

    assert [ref.stable_key() for ref in found] == [left.stable_key()]


# --------------------------------------------------------------------------
# 7. the recovery pass inside the effect summary
# --------------------------------------------------------------------------


class _Block:
    def __init__(self, pcode_ops):
        self.pcode_ops = pcode_ops


def _recovery_pass(call_op, tracer, callee_parameters, evidence, target_ref=None):
    from scripts.function_tracer_pcode.analysis.effects import store_effect

    return store_effect._impl__recover_uncovered_call_argument_evidence(
        [_Block([call_op])],
        tracer,
        [],
        lambda _target: callee_parameters,
        evidence,
    ), evidence


def test_recovery_pass_creates_evidence_for_an_uncovered_call_site(monkeypatch):
    """効果レーンが届かなかった callsite を、ABI 証拠だけで拾い直す。"""

    from scripts.function_tracer_pcode.analysis.effects import store_effect

    target_ref = _target_ref()
    monkeypatch.setattr(store_effect, "_resolve_call_target_ref", lambda _t, _o: target_ref)

    tracer = _Tracer()
    call_op = _CallOp([_Varnode(8, storage=_register_storage("d1", 0x5020))])
    callee_parameters = [_callee_parameter(0, "__x", _register_storage("d0", 0x5000))]
    evidence: dict = {}

    outcomes, evidence = _recovery_pass(call_op, tracer, callee_parameters, evidence)

    assert [outcome for _key, outcome in outcomes] == ["abi_evidence_recovered"]
    assert len(evidence) == 1
    recovered = next(iter(evidence.values()))
    assert recovered.recovery_status == CallArgumentEvidence.RECOVERY_COMPLETE
    assert len(recovered.callee_param_identities) == 1


def test_recovery_pass_leaves_existing_evidence_untouched(monkeypatch):
    from scripts.function_tracer_pcode.analysis.effects import store_effect

    target_ref = _target_ref()
    monkeypatch.setattr(store_effect, "_resolve_call_target_ref", lambda _t, _o: target_ref)

    tracer = _Tracer()
    call_op = _CallOp([_Varnode(8, storage=_register_storage("d1", 0x5020))])
    callee_parameters = [_callee_parameter(0, "__x", _register_storage("d0", 0x5000))]

    existing = CallArgumentEvidence(
        pcode_op_ref=tracer._make_pcode_op_ref(call_op),
        target_ref=target_ref,
        callee_param_identities=((("parameter", 0),),),
        arguments=(Expression.variable("already", size=8),),
        sources=("reaching_def",),
        coverage_complete=True,
        recovery_status=CallArgumentEvidence.RECOVERY_COMPLETE,
    )
    evidence = {tracer._make_pcode_op_ref(call_op).stable_key(): existing}

    outcomes, evidence = _recovery_pass(call_op, tracer, callee_parameters, evidence)

    assert outcomes == []
    assert len(evidence) == 1
    assert next(iter(evidence.values())) is existing


def test_recovery_pass_records_the_failure_reason_without_writing_evidence(monkeypatch):
    from scripts.function_tracer_pcode.analysis.effects import store_effect

    target_ref = _target_ref()
    monkeypatch.setattr(store_effect, "_resolve_call_target_ref", lambda _t, _o: target_ref)

    tracer = _Tracer()
    # 宣言 2 引数 / callsite 1 引数: 位置で埋めずに何も書かない。
    call_op = _CallOp([_Varnode(8, storage=_register_storage("d7", 0x5070))])
    callee_parameters = [
        _callee_parameter(0, "a", _register_storage("d0", 0x5000)),
        _callee_parameter(1, "b", _register_storage("d1", 0x5020)),
    ]
    evidence: dict = {}

    outcomes, evidence = _recovery_pass(call_op, tracer, callee_parameters, evidence)

    assert [outcome for _key, outcome in outcomes] == [abi.ABI_CALLSITE_ARITY_MISMATCH]
    assert evidence == {}


# --------------------------------------------------------------------------
# 8. log(x) vs log(x + 1): the same ABI slot with different values
# --------------------------------------------------------------------------


def test_same_abi_slot_with_different_argument_values_does_not_correspond():
    """``log(x)`` と ``log(x + 1)``。

    ABI スロット identity は一致する（どちらも第 0 引数・register・64bit）が、
    引数式が違うので callsite の semantic shape は一致せず、対応候補にならない。
    identity correspondence だけで値を同一視しないことの確認。
    """

    slot_key = (("abi_argument_slot", 0, "register", 64),)
    left = _internal_call_fact(
        "L1", "binaryL", ("expression", ("variable", "x")), 0x1000,
        abi_argument_slot_keys=slot_key,
    )
    right = _internal_call_fact(
        "R1", "binaryR", ("expression", ("binary", "INT_ADD", "x", 1)), 0x2000,
        abi_argument_slot_keys=slot_key,
    )

    # スロット identity は一致している。
    assert left.abi_argument_slot_keys == right.abi_argument_slot_keys
    # それでも候補は成立しない。
    result = build_internal_call_correspondence_candidates([left], [right])
    assert result.candidates == ()
    assert left.semantic_shape_key() != right.semantic_shape_key()


def test_obligations_do_not_claim_independence_they_did_not_evaluate():
    """評価していない obligation に ``independent`` を書かない。"""

    from scripts.function_tracer_pcode.proof.call_effect.fresh_arguments import (
        FRESH_ARGUMENT_STATUS_NOT_EVALUATED,
    )
    from scripts.function_tracer_pcode.proof.call_effect.obligations import (
        RelationalCallEffectObligation,
    )

    obligation = RelationalCallEffectObligation(
        obligation_id="ob1",
        relation_kind="call_to_region",
        observation_contract_id="contract",
        left_fact_id="L1",
        right_fact_id="R1",
    )

    assert obligation.fresh_argument_status == FRESH_ARGUMENT_STATUS_NOT_EVALUATED
    assert obligation.internal_candidate_id is None


# --------------------------------------------------------------------------
# 9. tier A also requires arity agreement
# --------------------------------------------------------------------------


def test_tier_a_does_not_ignore_extra_callsite_arguments():
    """callee=1 引数(d0) / callsite=2 引数(d0,d1)。

    d0 が完全一致しても、余分な実引数を黙って無視して ``complete`` を名乗って
    はいけない。arity は両 tier の前提。
    """

    tracer = _Tracer()
    d0 = _register_storage("d0", 0x5000)
    call_op = _CallOp(
        [
            _Varnode(8, storage=d0, expression=Expression.variable("x", size=8)),
            _Varnode(8, storage=_register_storage("d1", 0x5020), expression=Expression.variable("y", size=8)),
        ]
    )
    callee_parameters = [_callee_parameter(0, "__x", d0)]

    authority, assignment, reason = abi._impl__abi_slot_input_assignment(
        call_op, tracer, callee_parameters
    )

    assert authority is None
    assert assignment is None
    assert reason == abi.ABI_CALLSITE_ARITY_MISMATCH

    evidence, evidence_reason = abi._impl__recover_abi_call_argument_evidence(
        call_op, tracer, [], callee_parameters, _target_ref(), binary_id="binaryL"
    )
    assert evidence is None
    assert evidence_reason == abi.ABI_CALLSITE_ARITY_MISMATCH


def test_tier_a_still_succeeds_when_arity_agrees():
    tracer = _Tracer()
    d0 = _register_storage("d0", 0x5000)
    call_op = _CallOp([_Varnode(8, storage=d0, expression=Expression.variable("x", size=8))])

    authority, assignment, reason = abi._impl__abi_slot_input_assignment(
        call_op, tracer, [_callee_parameter(0, "__x", d0)]
    )

    assert reason is None
    assert authority == abi.ABI_AUTHORITY_CALLEE_DECLARED_STORAGE
    assert assignment == [0]


# --------------------------------------------------------------------------
# 10. fresh argument side identity is fail-closed
# --------------------------------------------------------------------------


def test_fresh_call_argument_requires_a_side_discriminator():
    from scripts.function_tracer_pcode.core.runtime_refs.call_arguments import (
        MissingSideDiscriminator,
    )

    slot = AbiArgumentSlotRef(
        ordinal=0, storage_class="register", width_bits=64,
        storage_identity_key=("register", "d0", 8),
    )
    for missing in (None, "", "   "):
        with pytest.raises(MissingSideDiscriminator):
            FreshCallArgumentRef(binary_id=missing, slot=slot)


def test_abi_recovery_fails_closed_without_a_side_discriminator():
    """discriminator が無いなら fresh を発行せず証拠行ごと諦める。"""

    tracer = _Tracer(binary_id=None)
    # 追跡できない入力にして fresh 経路へ入れる。
    call_op = _CallOp([_Varnode(8, storage=_register_storage("d1", 0x5020))])
    callee_parameters = [_callee_parameter(0, "__x", _register_storage("d0", 0x5000))]

    def _untraceable(_varnode, *_args, **_kwargs):
        return None

    tracer.trace_varnode = _untraceable

    resolution, reason = abi._impl__resolve_abi_call_arguments(
        call_op, tracer, [], callee_parameters,
        binary_id=None, call_site_key=("op", 1),
    )

    assert resolution is None
    assert reason == abi.ABI_SIDE_DISCRIMINATOR_UNAVAILABLE


# --------------------------------------------------------------------------
# 11. candidate -> callee correspondence -> callsite correspondence
# --------------------------------------------------------------------------


def _internal_fact_with_callee_proof(fact_id, binary_id, offset, **overrides):
    fields = dict(
        callee_return_summary_statuses=("complete",),
        callee_return_shape_keys=((("return", "int32"),),),
        callee_effect_summary_statuses=("complete",),
        callee_memory_effect_counts=(1,),
        callee_control_profile_keys=((("profile", "total_scalar"),),),
        callee_parameter_width_bits=(32,),
        callee_return_width_bits=(32,),
    )
    fields.update(overrides)
    return _internal_call_fact(fact_id, binary_id, ("shape", "a"), offset, **fields)


def _proof_for(left_facts, right_facts):
    from scripts.function_tracer_pcode.proof.call_effect.candidates import (
        build_callee_correspondence_proof,
    )

    candidates = build_internal_call_correspondence_candidates(left_facts, right_facts).candidates
    proof = build_callee_correspondence_proof(
        candidates,
        {f.fact_id: f for f in left_facts},
        {f.fact_id: f for f in right_facts},
    )
    return candidates, proof


def test_callee_correspondence_proof_issues_the_id_and_completes_the_correspondence():
    left = _internal_fact_with_callee_proof("L1", "binaryL", 0x1000)
    right = _internal_fact_with_callee_proof("R1", "binaryR", 0x2000)
    candidates, proof = _proof_for([left], [right])

    assert proof.verification_failure() is None
    assert len(proof.pairs) == 1

    correspondence, blockers = confirm_internal_callsite_correspondence(
        candidates[0], proof, left, right
    )

    assert blockers == ()
    assert correspondence is not None
    # ID は proof digest に bind されている。
    assert correspondence.callee_correspondence.proof_id == proof.proof_id
    assert correspondence.argument_relation_key[0] == "relational_argument"


def test_correspondence_id_cannot_be_issued_without_a_proof():
    """proof 無しでは ``RelationalCalleeCorrespondenceId`` を発行できない。"""

    from scripts.function_tracer_pcode.proof.call_effect.candidates import (
        issue_relational_callee_correspondence,
    )

    left = _internal_fact_with_callee_proof("L1", "binaryL", 0x1000)
    right = _internal_fact_with_callee_proof("R1", "binaryR", 0x2000)
    candidates, _proof = _proof_for([left], [right])

    issued, blockers = issue_relational_callee_correspondence(None, candidates[0])

    assert issued is None
    assert CALLSITE_CALLEE_CORRESPONDENCE_MISSING in blockers

    correspondence, blockers = confirm_internal_callsite_correspondence(
        candidates[0], None, left, right
    )
    assert correspondence is None
    assert CALLSITE_CALLEE_CORRESPONDENCE_MISSING in blockers


def test_tampered_proof_receipt_is_rejected():
    """digest と payload が食い違う receipt は拒否する。"""

    import dataclasses

    from scripts.function_tracer_pcode.proof.call_effect.candidates import (
        CALLEE_CORRESPONDENCE_PROOF_INVALID,
        issue_relational_callee_correspondence,
    )

    left = _internal_fact_with_callee_proof("L1", "binaryL", 0x1000)
    right = _internal_fact_with_callee_proof("R1", "binaryR", 0x2000)
    candidates, proof = _proof_for([left], [right])

    tampered = dataclasses.replace(proof, proof_id="0" * 64)
    assert tampered.verification_failure() == "proof_digest_mismatch"

    issued, blockers = issue_relational_callee_correspondence(tampered, candidates[0])
    assert issued is None
    assert CALLEE_CORRESPONDENCE_PROOF_INVALID in blockers


def test_foreign_proof_does_not_cover_another_pairs_candidate():
    """他の関数対の proof は候補を覆わない。"""

    from scripts.function_tracer_pcode.proof.call_effect.candidates import (
        issue_relational_callee_correspondence,
    )

    left = _internal_fact_with_callee_proof("L1", "binaryL", 0x1000)
    right = _internal_fact_with_callee_proof("R1", "binaryR", 0x2000)
    candidates, _proof = _proof_for([left], [right])

    other_left = _internal_fact_with_callee_proof(
        "L9", "binaryL", 0x9000, argument_shape_keys=(("shape", "z"),)
    )
    other_right = _internal_fact_with_callee_proof(
        "R9", "binaryR", 0x9100, argument_shape_keys=(("shape", "z"),)
    )
    _other_candidates, foreign_proof = _proof_for([other_left], [other_right])

    issued, blockers = issue_relational_callee_correspondence(foreign_proof, candidates[0])

    assert issued is None
    assert CALLSITE_CALLEE_CORRESPONDENCE_MISSING in blockers


def test_ambiguous_callee_mapping_blocks_the_correspondence():
    """同じ左 callee が 2 つの異なる右 callee に対応するなら曖昧。

    候補集合が誘導する callee 対応が双方向に一意でなければ ID を発行しない。
    """

    from scripts.function_tracer_pcode.proof.call_effect.candidates import (
        CALLEE_CORRESPONDENCE_AMBIGUOUS,
    )

    same_left_callee = (("function", 111, 0x2000),)
    left_a = _internal_fact_with_callee_proof(
        "L1", "binaryL", 0x1000, argument_shape_keys=(("shape", "a"),),
        target_candidates=same_left_callee,
    )
    left_b = _internal_fact_with_callee_proof(
        "L2", "binaryL", 0x1010, argument_shape_keys=(("shape", "b"),),
        target_candidates=same_left_callee,
    )
    right_a = _internal_fact_with_callee_proof(
        "R1", "binaryR", 0x2000, argument_shape_keys=(("shape", "a"),),
        target_candidates=(("function", 222, 0x4000),),
    )
    right_b = _internal_fact_with_callee_proof(
        "R2", "binaryR", 0x2010, argument_shape_keys=(("shape", "b"),),
        target_candidates=(("function", 222, 0x5000),),
    )

    _candidates, proof = _proof_for([left_a, left_b], [right_a, right_b])

    assert proof.pairs == ()
    assert CALLEE_CORRESPONDENCE_AMBIGUOUS in {reason for _key, reason in proof.rejected}


def test_consistent_callee_mapping_is_proven():
    same_left_callee = (("function", 111, 0x2000),)
    same_right_callee = (("function", 222, 0x4000),)
    left_a = _internal_fact_with_callee_proof(
        "L1", "binaryL", 0x1000, argument_shape_keys=(("shape", "a"),),
        target_candidates=same_left_callee,
    )
    left_b = _internal_fact_with_callee_proof(
        "L2", "binaryL", 0x1010, argument_shape_keys=(("shape", "b"),),
        target_candidates=same_left_callee,
    )
    right_a = _internal_fact_with_callee_proof(
        "R1", "binaryR", 0x2000, argument_shape_keys=(("shape", "a"),),
        target_candidates=same_right_callee,
    )
    right_b = _internal_fact_with_callee_proof(
        "R2", "binaryR", 0x2010, argument_shape_keys=(("shape", "b"),),
        target_candidates=same_right_callee,
    )

    _candidates, proof = _proof_for([left_a, left_b], [right_a, right_b])

    assert proof.verification_failure() is None
    assert len(proof.pairs) == 2


def test_unresolved_callee_target_blocks_the_correspondence():
    """候補成立後に callee target が解決不能になった場合も ID を出さない。

    target が最初から未解決なら `correspondence_operation_class()` が
    internal candidate にならないので候補すら立たない。ここで守るのは、
    候補と proof が別々の事実を見てしまう drift のケース。
    """

    from scripts.function_tracer_pcode.proof.call_effect.candidates import (
        CALLEE_TARGET_UNRESOLVED,
        build_callee_correspondence_proof,
    )

    left = _internal_fact_with_callee_proof("L1", "binaryL", 0x1000)
    right = _internal_fact_with_callee_proof("R1", "binaryR", 0x2000)
    candidates, _proof = _proof_for([left], [right])

    drifted_right = _internal_fact_with_callee_proof(
        "R1", "binaryR", 0x2000, target_resolution_status="ambiguous",
    )
    proof = build_callee_correspondence_proof(
        candidates, {"L1": left}, {"R1": drifted_right}
    )

    assert proof.pairs == ()
    assert CALLEE_TARGET_UNRESOLVED in {reason for _key, reason in proof.rejected}

    correspondence, blockers = confirm_internal_callsite_correspondence(
        candidates[0], proof, left, drifted_right
    )
    assert correspondence is None
    assert CALLEE_TARGET_UNRESOLVED in blockers


def test_incomplete_callee_summary_blocks_the_correspondence():
    left = _internal_fact_with_callee_proof("L1", "binaryL", 0x1000)
    right = _internal_fact_with_callee_proof(
        "R1", "binaryR", 0x2000, callee_return_summary_statuses=("inconclusive",),
    )
    candidates, proof = _proof_for([left], [right])

    assert proof.pairs == ()
    correspondence, blockers = confirm_internal_callsite_correspondence(
        candidates[0], proof, left, right
    )
    assert correspondence is None
    assert CALLEE_RETURN_SUMMARY_UNPROVEN in blockers
    assert CALLSITE_CALLEE_CORRESPONDENCE_MISSING in blockers


def test_callee_correspondence_does_not_require_structural_agreement():
    """左右で効果数が違っても correspondence は成立する。

    同じ番地を 2 回上書きする callee と 1 回だけ書く callee は最終状態が同じなら
    等価であり、等価性は後段 ``memory_relation`` が証明する。ここで構造一致を
    要求すると、証明できるはずの等価を先回りして潰してしまう。
    """

    left = _internal_fact_with_callee_proof("L1", "binaryL", 0x1000, callee_memory_effect_counts=(2,))
    right = _internal_fact_with_callee_proof("R1", "binaryR", 0x2000, callee_memory_effect_counts=(1,))
    candidates, proof = _proof_for([left], [right])

    correspondence, blockers = confirm_internal_callsite_correspondence(
        candidates[0], proof, left, right
    )

    assert blockers == ()
    assert correspondence is not None
    pair = proof.pairs[0]
    assert pair.left_inputs_key != pair.right_inputs_key


def test_without_a_candidate_the_callsite_correspondence_fails_closed():
    left = _internal_fact_with_callee_proof("L1", "binaryL", 0x1000)
    right = _internal_fact_with_callee_proof("R1", "binaryR", 0x2000)
    _candidates, proof = _proof_for([left], [right])

    correspondence, blockers = confirm_internal_callsite_correspondence(
        None, proof, left, right
    )

    assert correspondence is None
    assert blockers == (CALLSITE_CANDIDATE_MISSING,)


# --------------------------------------------------------------------------
# candidate binding: schema / obligation / staleness / tampering
# --------------------------------------------------------------------------


def test_candidate_binding_accepts_a_matching_persisted_key():
    from scripts.function_tracer_pcode.proof.call_effect.candidates import (
        verify_internal_candidate_binding,
    )

    left = _internal_fact_with_callee_proof("L1", "binaryL", 0x1000)
    right = _internal_fact_with_callee_proof("R1", "binaryR", 0x2000)
    candidates, _proof = _proof_for([left], [right])

    bound, blockers = verify_internal_candidate_binding(
        candidates[0].stable_key(), "L1", "R1", left, right
    )

    assert blockers == ()
    assert bound is not None
    assert bound.stable_key() == candidates[0].stable_key()


def test_candidate_binding_rejects_a_malformed_key():
    from scripts.function_tracer_pcode.proof.call_effect.candidates import (
        CANDIDATE_SCHEMA_INVALID,
        verify_internal_candidate_binding,
    )

    left = _internal_fact_with_callee_proof("L1", "binaryL", 0x1000)
    right = _internal_fact_with_callee_proof("R1", "binaryR", 0x2000)

    for bad in (
        ("wrong_kind", "L1", "R1", ("shape",), ()),
        ("internal_call_correspondence_candidate", "L1", "R1"),
        ("internal_call_correspondence_candidate", 1, "R1", ("shape",), ()),
    ):
        bound, blockers = verify_internal_candidate_binding(bad, "L1", "R1", left, right)
        assert bound is None
        assert blockers == (CANDIDATE_SCHEMA_INVALID,)


def test_candidate_binding_rejects_a_key_from_another_obligation():
    """obligation の値でキーを作り直して辻褄を合わせない。"""

    from scripts.function_tracer_pcode.proof.call_effect.candidates import (
        CANDIDATE_OBLIGATION_MISMATCH,
        verify_internal_candidate_binding,
    )

    left = _internal_fact_with_callee_proof("L1", "binaryL", 0x1000)
    right = _internal_fact_with_callee_proof("R1", "binaryR", 0x2000)
    candidates, _proof = _proof_for([left], [right])
    foreign_key = ("internal_call_correspondence_candidate", "L9", "R9") + tuple(
        candidates[0].stable_key()[3:]
    )

    bound, blockers = verify_internal_candidate_binding(
        foreign_key, "L1", "R1", left, right
    )

    assert bound is None
    assert blockers == (CANDIDATE_OBLIGATION_MISMATCH,)


def test_candidate_binding_rejects_a_stale_shape():
    """fact が変わったのに古い shape を運んでいるキーは拒否する。"""

    from scripts.function_tracer_pcode.proof.call_effect.candidates import (
        CANDIDATE_STALE,
        verify_internal_candidate_binding,
    )

    left = _internal_fact_with_callee_proof("L1", "binaryL", 0x1000)
    right = _internal_fact_with_callee_proof("R1", "binaryR", 0x2000)
    candidates, _proof = _proof_for([left], [right])
    stale_key = tuple(candidates[0].stable_key()[:3]) + (("shape", "stale"), ())

    bound, blockers = verify_internal_candidate_binding(
        stale_key, "L1", "R1", left, right
    )

    assert bound is None
    assert blockers == (CANDIDATE_STALE,)


def test_phase2_rejects_a_stale_callee_correspondence_proof_id():
    from scripts.function_tracer_pcode.proof.call_effect.candidates import (
        CALLEE_CORRESPONDENCE_PROOF_STALE,
    )
    from scripts.function_tracer_pcode.proof.call_effect.obligations import (
        RelationalCallEffectObligation,
        _phase2_direct_call_eligibility,
    )

    left = _internal_fact_with_callee_proof("L1", "binaryL", 0x1000)
    right = _internal_fact_with_callee_proof("R1", "binaryR", 0x2000)
    candidates, _proof = _proof_for([left], [right])

    obligation = RelationalCallEffectObligation(
        obligation_id="ob1",
        relation_kind="call_to_call",
        observation_contract_id="contract",
        left_fact_id="L1",
        right_fact_id="R1",
        internal_candidate_id=candidates[0].stable_key(),
        callee_correspondence_proof_id="deadbeef",
    )

    eligibility = _phase2_direct_call_eligibility(
        obligation, {"L1": left}, {"R1": right}
    )

    assert CALLEE_CORRESPONDENCE_PROOF_STALE in eligibility.blockers


def test_external_call_pairs_do_not_get_the_internal_correspondence_blocker():
    """internal 用の correspondence 要件を external callee の pair に課さない。

    external の pair は `not_resolved_internal_call_candidate` /
    `noninternal_call_target` が既に塞いでいる。そこへ internal 用の blocker を
    重ねると、internal でない pair に `callsite_correspondence_unproven` という
    別の reason が付いてしまう。
    """

    from scripts.function_tracer_pcode.proof.call_effect.obligations import (
        RelationalCallEffectObligation,
        _phase2_direct_call_eligibility,
    )

    left = _internal_call_fact(
        "L1", "binaryL", ("shape", "a"), 0x1000, target_categories=("external_function",)
    )
    right = _internal_call_fact(
        "R1", "binaryR", ("shape", "a"), 0x2000, target_categories=("external_function",)
    )
    obligation = RelationalCallEffectObligation(
        obligation_id="ob1",
        relation_kind="call_to_call",
        observation_contract_id="contract",
        left_fact_id="L1",
        right_fact_id="R1",
    )

    eligibility = _phase2_direct_call_eligibility(
        obligation, {"L1": left}, {"R1": right}
    )

    assert eligibility.status == "ineligible"
    assert CALLSITE_CANDIDATE_MISSING not in eligibility.blockers
    assert CALLSITE_CALLEE_CORRESPONDENCE_MISSING not in eligibility.blockers
    assert CALLSITE_ARGUMENT_RELATION_MISSING not in eligibility.blockers
    # external であることは従来どおり別の blocker で塞がれている。
    assert "left_noninternal_call_target" in eligibility.blockers


def test_internal_pairs_still_require_the_callee_correspondence():
    from scripts.function_tracer_pcode.proof.call_effect.obligations import (
        RelationalCallEffectObligation,
        _phase2_direct_call_eligibility,
    )

    left = _internal_fact_with_callee_proof("L1", "binaryL", 0x1000)
    right = _internal_fact_with_callee_proof(
        "R1", "binaryR", 0x2000, callee_return_summary_statuses=("inconclusive",),
    )
    obligation = RelationalCallEffectObligation(
        obligation_id="ob1",
        relation_kind="call_to_call",
        observation_contract_id="contract",
        left_fact_id="L1",
        right_fact_id="R1",
        internal_candidate_id=build_internal_call_correspondence_candidates(
            [left], [right]
        ).candidates[0].stable_key(),
    )

    eligibility = _phase2_direct_call_eligibility(
        obligation, {"L1": left}, {"R1": right}
    )

    assert eligibility.status == "ineligible"
    assert CALLSITE_CALLEE_CORRESPONDENCE_MISSING in eligibility.blockers


# --------------------------------------------------------------------------
# 13. end-to-end: a SAT over side-specific fresh arguments is not decisive
# --------------------------------------------------------------------------


def _fresh_return_analysis(function_name, entry_point, binary_id, constant):
    """A return value that carries a side-specific fresh call argument."""

    from scripts.function_tracer_pcode.core import FunctionReturnAnalysis, ReturnInfo

    fresh = FreshCallArgumentRef(
        binary_id=binary_id,
        slot=AbiArgumentSlotRef(
            ordinal=0,
            storage_class="register",
            width_bits=32,
            storage_identity_key=("register", "w0", 4),
        ),
        call_site_key=("pcode_op", binary_id, 0x1000),
    )
    fresh_expr = abi._impl__fresh_call_argument_expression(fresh)
    fresh_expr.size = 4
    value = Expression.binary_op("INT_ADD", fresh_expr, Expression.constant(constant, size=4))
    return (
        FunctionReturnAnalysis(
            function_name=function_name,
            entry_point=entry_point,
            parameters=[{"name": "x", "index": 0, "size": 4, "data_type": "int", "storage": None}],
            returns=[ReturnInfo(address=entry_point, value=value, conditions=[])],
            return_type="int",
        ),
        fresh,
        fresh_expr,
    )


def test_sat_over_side_specific_fresh_arguments_is_not_decisive(monkeypatch):
    """左右で対応する ABI slot / 値は side-specific fresh / SMT symbol は別。

    その状態で SAT（counterexample 候補）を実際に構成し、production の
    decisive-SAT authority を通しても無条件 `NOT_EQ` にならないことを固定する。
    反例は左右で独立な自由シンボルに異なる値を割り当てただけで成立するため、
    非等価の証拠にならない。
    """

    from unittest.mock import Mock

    from scripts.function_tracer_pcode.core.render_smt.unknowns import (
        collect_unknown_smt_declarations,
    )
    from scripts.function_tracer_pcode.proof.strategies.pairwise import PairwiseStrategy
    from scripts.function_tracer_pcode.tests.unit._sat_decisiveness_fixtures import (
        ReturnCase,
        _base_context_for_single_int_param,
        _solver_bound_query_result,
    )

    analysis1, left_fresh, left_expr = _fresh_return_analysis("same_func", "0x1000", "binaryL", 1)
    analysis2, right_fresh, right_expr = _fresh_return_analysis("same_func", "0x2000", "binaryR", 2)

    # (a) 対応する ABI slot。
    assert left_fresh.identity_correspondence_key() == right_fresh.identity_correspondence_key()
    # (b) 値は side-specific fresh。
    assert fresh_call_argument_refs_are_side_distinct(left_fresh, right_fresh)
    # (c) SMT symbol は別。
    left_symbols = collect_unknown_smt_declarations(left_expr)
    right_symbols = collect_unknown_smt_declarations(right_expr)
    assert left_symbols[0][0] != right_symbols[0][0]
    # (d) relational equality proof も irrelevance proof も無い。
    assert couple_fresh_arguments(left_fresh, right_fresh) is None
    assert fresh_arguments_are_independent(left_fresh, right_fresh) is True
    discharged, undischarged = discharge_fresh_argument_blockers(
        [left_fresh], ("decisive", "return_relation"), []
    )
    assert discharged is False and undischarged

    # (e) authority 層の decisive-SAT gate が両 side で発火している。
    for analysis in (analysis1, analysis2):
        assert "unresolved_return_value" in analysis.get_decisive_sat_unsafety_reasons()

    # (f) SAT を実際に構成して production path を通す。
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    cases = {
        id(analysis1): ReturnCase(
            index=0, conditions=[], value_expr=analysis1.returns[0].value,
            return_info=analysis1.returns[0], return_type="int",
            parameters=analysis1.parameters,
        ),
        id(analysis2): ReturnCase(
            index=0, conditions=[], value_expr=analysis2.returns[0].value,
            return_info=analysis2.returns[0], return_type="int",
            parameters=analysis2.parameters,
        ),
    }
    monkeypatch.setattr(
        strategy, "_extract_return_cases", lambda analysis: [cases[id(analysis)]]
    )
    monkeypatch.setattr(strategy, "_prune_unreachable_cases", lambda c, *_a, **_k: c)
    monkeypatch.setattr(strategy, "_cases_are_contradictory", lambda *_a, **_k: False)
    # counterexample の検証は通ったことにする。それでも fresh 由来の SAT は
    # 決め手にならない、というのがここで固定したい不変条件。
    monkeypatch.setattr(
        "scripts.function_tracer_pcode.proof.strategies.pairwise.validate_counterexample_across_cases",
        lambda *_a, **_k: True,
    )
    strategy._solve_query_after_guard = Mock(
        return_value=_solver_bound_query_result(
            False,
            model={left_symbols[0][0]: 0, right_symbols[0][0]: 7},
            query="(assert (distinct a b))\n(check-sat)",
        )
    )

    result = strategy.check(analysis1, analysis2)

    # (g) 無条件 NOT_EQ にならず、UNKNOWN / blocker へ倒れる。
    assert result.is_equivalent is not False
    assert result.is_equivalent is None
    assert result.unknown_reasons


def test_positive_control_same_harness_reaches_unconditional_not_eq(monkeypatch):
    """対照実験。同じ harness で fresh を使わなければ SAT は決め手になる。

    これが `NOT_EQ` に到達することで、直前の test が「fresh のせいで止まった」
    ことを示せる（harness の別要因で止まったのではない）。
    """

    from unittest.mock import Mock

    from scripts.function_tracer_pcode.core import FunctionReturnAnalysis, ReturnInfo
    from scripts.function_tracer_pcode.proof.strategies.pairwise import PairwiseStrategy
    from scripts.function_tracer_pcode.tests.unit._sat_decisiveness_fixtures import (
        ReturnCase,
        _base_context_for_single_int_param,
        _solver_bound_query_result,
    )

    def _plain(entry_point, constant):
        return FunctionReturnAnalysis(
            function_name="same_func",
            entry_point=entry_point,
            parameters=[{"name": "x", "index": 0, "size": 4, "data_type": "int", "storage": None}],
            returns=[ReturnInfo(address=entry_point, value=Expression.constant(constant, size=4), conditions=[])],
            return_type="int",
        )

    analysis1, analysis2 = _plain("0x1000", 1), _plain("0x2000", 2)
    for analysis in (analysis1, analysis2):
        assert "unresolved_return_value" not in analysis.get_decisive_sat_unsafety_reasons()

    formula_builder = Mock()
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    cases = {
        id(analysis1): ReturnCase(
            index=0, conditions=[], value_expr=analysis1.returns[0].value,
            return_info=analysis1.returns[0], return_type="int",
            parameters=analysis1.parameters,
        ),
        id(analysis2): ReturnCase(
            index=0, conditions=[], value_expr=analysis2.returns[0].value,
            return_info=analysis2.returns[0], return_type="int",
            parameters=analysis2.parameters,
        ),
    }
    monkeypatch.setattr(strategy, "_extract_return_cases", lambda a: [cases[id(a)]])
    monkeypatch.setattr(strategy, "_prune_unreachable_cases", lambda c, *_a, **_k: c)
    monkeypatch.setattr(strategy, "_cases_are_contradictory", lambda *_a, **_k: False)
    monkeypatch.setattr(
        "scripts.function_tracer_pcode.proof.strategies.pairwise.validate_counterexample_across_cases",
        lambda *_a, **_k: True,
    )
    strategy._solve_query_after_guard = Mock(
        return_value=_solver_bound_query_result(
            False,
            model={"x_1": 0, "x_2": 0},
            query="(assert (distinct (_ bv1 32) (_ bv2 32)))\n(check-sat)",
        )
    )

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is False
    assert result.sat_pairs == 1


def test_phase2_rejects_a_substituted_relational_callee_correspondence_id():
    from scripts.function_tracer_pcode.proof.call_effect.candidates import (
        CALLEE_CORRESPONDENCE_PROOF_STALE,
    )
    from scripts.function_tracer_pcode.proof.call_effect.obligations import (
        RelationalCallEffectObligation,
        _phase2_direct_call_eligibility,
    )

    left = _internal_fact_with_callee_proof("L1", "binaryL", 0x1000)
    right = _internal_fact_with_callee_proof("R1", "binaryR", 0x2000)
    candidates, proof = _proof_for([left], [right])

    obligation = RelationalCallEffectObligation(
        obligation_id="ob1",
        relation_kind="call_to_call",
        observation_contract_id="contract",
        left_fact_id="L1",
        right_fact_id="R1",
        internal_candidate_id=candidates[0].stable_key(),
        callee_correspondence_proof_id=proof.proof_id,
        relational_callee_correspondence_id=("relational_callee_correspondence", "forged"),
    )

    eligibility = _phase2_direct_call_eligibility(
        obligation, {"L1": left}, {"R1": right}
    )

    assert CALLEE_CORRESPONDENCE_PROOF_STALE in eligibility.blockers


def test_phase2_accepts_a_correctly_bound_internal_correspondence():
    """正しく bind されていれば correspondence 由来の blocker は付かない。"""

    from scripts.function_tracer_pcode.proof.call_effect import candidates as k
    from scripts.function_tracer_pcode.proof.call_effect.obligations import (
        RelationalCallEffectObligation,
        _phase2_direct_call_eligibility,
    )

    left = _internal_fact_with_callee_proof("L1", "binaryL", 0x1000)
    right = _internal_fact_with_callee_proof("R1", "binaryR", 0x2000)
    candidates, proof = _proof_for([left], [right])
    issued, _b = k.issue_relational_callee_correspondence(proof, candidates[0])

    obligation = RelationalCallEffectObligation(
        obligation_id="ob1",
        relation_kind="call_to_call",
        observation_contract_id="contract",
        left_fact_id="L1",
        right_fact_id="R1",
        internal_candidate_id=candidates[0].stable_key(),
        callee_correspondence_proof_id=proof.proof_id,
        relational_callee_correspondence_id=issued.stable_key(),
    )

    eligibility = _phase2_direct_call_eligibility(
        obligation, {"L1": left}, {"R1": right}
    )

    correspondence_codes = {
        k.CALLSITE_CANDIDATE_MISSING,
        k.CALLSITE_CALLEE_CORRESPONDENCE_MISSING,
        k.CALLSITE_ARGUMENT_RELATION_MISSING,
        k.CANDIDATE_SCHEMA_INVALID,
        k.CANDIDATE_OBLIGATION_MISMATCH,
        k.CANDIDATE_STALE,
        k.CALLEE_CORRESPONDENCE_PROOF_STALE,
        k.CALLEE_CORRESPONDENCE_PROOF_INVALID,
    }
    assert set(eligibility.blockers) & correspondence_codes == set()


# --------------------------------------------------------------------------
# 14. proof issuance authority (token) and the callee interface relation
# --------------------------------------------------------------------------


def test_hand_built_proof_with_a_matching_digest_is_not_authorized():
    """digest 整合性は「改竄されていない」ことしか言わない。

    factory を通さず payload を組み立てて digest を合わせても authorized に
    ならないことを固定する。
    """

    import dataclasses

    from scripts.function_tracer_pcode.proof.call_effect import candidates as k

    left = _internal_fact_with_callee_proof("L1", "binaryL", 0x1000)
    right = _internal_fact_with_callee_proof("R1", "binaryR", 0x2000)
    candidates, genuine = _proof_for([left], [right])
    assert genuine.verification_failure() is None

    forged = dataclasses.replace(genuine, issuer_token=None)
    # payload も digest も本物と同一。違うのは発行元だけ。
    assert forged.payload() == genuine.payload()
    assert forged.proof_id == genuine.proof_id
    assert forged.verification_failure() == "untrusted_issuer_token"

    issued, blockers = k.issue_relational_callee_correspondence(forged, candidates[0])
    assert issued is None
    assert k.CALLEE_CORRESPONDENCE_PROOF_INVALID in blockers


def test_callee_parameter_arity_relation_is_rechecked_against_drift():
    """arity は `semantic_shape_key` に含まれるので候補段で既に効いている。

    proof 側の arity 検査は、候補形成後に fact が変わった場合の drift guard。
    候補と proof が別々の事実を見て通ってしまわないことを固定する。
    """

    from scripts.function_tracer_pcode.proof.call_effect.candidates import (
        CALLEE_PARAMETER_ARITY_RELATION_MISSING,
        build_callee_correspondence_proof,
    )

    left = _internal_fact_with_callee_proof("L1", "binaryL", 0x1000)
    right = _internal_fact_with_callee_proof("R1", "binaryR", 0x2000)
    candidates, _proof = _proof_for([left], [right])
    # arity が違えば候補自体が立たない（上流で既に塞がれている）。
    mismatched = _internal_fact_with_callee_proof(
        "R1", "binaryR", 0x2000,
        callee_parameter_keys=((("parameter_storage", "d0"),), (("parameter_storage", "d1"),)),
        callee_parameter_width_bits=(32, 32),
    )
    assert build_internal_call_correspondence_candidates([left], [mismatched]).candidates == ()

    # 候補成立後に arity が変わった場合は proof 側で捕まえる。
    proof = build_callee_correspondence_proof(candidates, {"L1": left}, {"R1": mismatched})

    assert proof.pairs == ()
    assert CALLEE_PARAMETER_ARITY_RELATION_MISSING in {r for _k, r in proof.rejected}


def test_callee_parameter_width_mismatch_fails_closed():
    from scripts.function_tracer_pcode.proof.call_effect.candidates import (
        CALLEE_PARAMETER_WIDTH_RELATION_MISSING,
    )

    left = _internal_fact_with_callee_proof("L1", "binaryL", 0x1000, callee_parameter_width_bits=(64,))
    right = _internal_fact_with_callee_proof("R1", "binaryR", 0x2000, callee_parameter_width_bits=(32,))
    _candidates, proof = _proof_for([left], [right])

    assert proof.pairs == ()
    assert CALLEE_PARAMETER_WIDTH_RELATION_MISSING in {r for _k, r in proof.rejected}


def test_asymmetric_width_evidence_fails_closed():
    """片側だけ観測できる状態を「一致した」とも「無関係」とも扱わない。"""

    from scripts.function_tracer_pcode.proof.call_effect.candidates import (
        CALLEE_PARAMETER_WIDTH_RELATION_MISSING,
    )

    left = _internal_fact_with_callee_proof("L1", "binaryL", 0x1000, callee_parameter_width_bits=(64,))
    right = _internal_fact_with_callee_proof("R1", "binaryR", 0x2000, callee_parameter_width_bits=())
    _candidates, proof = _proof_for([left], [right])

    assert proof.pairs == ()
    assert CALLEE_PARAMETER_WIDTH_RELATION_MISSING in {r for _k, r in proof.rejected}


def test_callee_return_width_mismatch_fails_closed():
    from scripts.function_tracer_pcode.proof.call_effect.candidates import (
        CALLEE_RETURN_WIDTH_RELATION_MISSING,
    )

    left = _internal_fact_with_callee_proof("L1", "binaryL", 0x1000, callee_return_width_bits=(64,))
    right = _internal_fact_with_callee_proof("R1", "binaryR", 0x2000, callee_return_width_bits=(32,))
    _candidates, proof = _proof_for([left], [right])

    assert proof.pairs == ()
    assert CALLEE_RETURN_WIDTH_RELATION_MISSING in {r for _k, r in proof.rejected}


def test_unavailable_width_fails_closed_on_both_sides():
    """どちらでも幅が回収できないなら correspondence は成立しない。

    「両側とも不明だから一致扱い」は fail-open であって証明ではない。
    """

    from scripts.function_tracer_pcode.proof.call_effect.candidates import (
        CALLEE_PARAMETER_WIDTH_RELATION_MISSING,
        CALLEE_RETURN_WIDTH_RELATION_MISSING,
    )

    left = _internal_fact_with_callee_proof(
        "L1", "binaryL", 0x1000, callee_parameter_width_bits=(), callee_return_width_bits=(),
    )
    right = _internal_fact_with_callee_proof(
        "R1", "binaryR", 0x2000, callee_parameter_width_bits=(), callee_return_width_bits=(),
    )
    candidates, proof = _proof_for([left], [right])

    assert proof.pairs == ()
    rejected = {r for _k, r in proof.rejected}
    assert CALLEE_PARAMETER_WIDTH_RELATION_MISSING in rejected
    assert CALLEE_RETURN_WIDTH_RELATION_MISSING in rejected

    correspondence, blockers = confirm_internal_callsite_correspondence(
        candidates[0], proof, left, right
    )
    assert correspondence is None
    assert CALLSITE_CALLEE_CORRESPONDENCE_MISSING in blockers


def test_partially_recovered_parameter_widths_fail_closed():
    """一部の ordinal しか回収できていない状態を関係の根拠にしない。"""

    from scripts.function_tracer_pcode.proof.call_effect.candidates import (
        CALLEE_PARAMETER_WIDTH_RELATION_MISSING,
    )

    two_params = ((("parameter_storage", "a"),), (("parameter_storage", "b"),))
    left = _internal_fact_with_callee_proof(
        "L1", "binaryL", 0x1000,
        callee_parameter_keys=two_params, callee_parameter_width_bits=(32, None),
    )
    right = _internal_fact_with_callee_proof(
        "R1", "binaryR", 0x2000,
        callee_parameter_keys=two_params, callee_parameter_width_bits=(32, 32),
    )
    _candidates, proof = _proof_for([left], [right])

    assert proof.pairs == ()
    assert CALLEE_PARAMETER_WIDTH_RELATION_MISSING in {r for _k, r in proof.rejected}


def test_callee_return_semantic_shape_must_correspond():
    """戻り値 semantic shape が左右で対応しなければ ID を出さない。"""

    from scripts.function_tracer_pcode.proof.call_effect.candidates import (
        CALLEE_RETURN_SHAPE_RELATION_MISSING,
    )

    left = _internal_fact_with_callee_proof("L1", "binaryL", 0x1000)
    right = _internal_fact_with_callee_proof(
        "R1", "binaryR", 0x2000, callee_return_shape_keys=((("return", "other"),),),
    )
    candidates, proof = _proof_for([left], [right])

    assert proof.pairs == ()
    assert CALLEE_RETURN_SHAPE_RELATION_MISSING in {r for _k, r in proof.rejected}

    correspondence, blockers = confirm_internal_callsite_correspondence(
        candidates[0], proof, left, right
    )
    assert correspondence is None
    assert CALLEE_RETURN_SHAPE_RELATION_MISSING in blockers


def test_matching_callee_return_semantic_shape_is_bound_into_the_id():
    left = _internal_fact_with_callee_proof("L1", "binaryL", 0x1000)
    right = _internal_fact_with_callee_proof("R1", "binaryR", 0x2000)
    candidates, proof = _proof_for([left], [right])

    correspondence, blockers = confirm_internal_callsite_correspondence(
        candidates[0], proof, left, right
    )

    assert blockers == ()
    relation = correspondence.callee_correspondence.interface_relation_key
    assert ("return_semantic_shape", ((("return", "int32"),),)) in relation


def test_interface_relation_is_bound_into_the_correspondence_id():
    left = _internal_fact_with_callee_proof("L1", "binaryL", 0x1000)
    right = _internal_fact_with_callee_proof("R1", "binaryR", 0x2000)
    candidates, proof = _proof_for([left], [right])

    correspondence, blockers = confirm_internal_callsite_correspondence(
        candidates[0], proof, left, right
    )

    assert blockers == ()
    relation = correspondence.callee_correspondence.interface_relation_key
    assert ("parameter_arity", 1) in relation
    assert ("parameter_width", (32,)) in relation
    assert ("return_width", 32) in relation
    assert ("return_semantic_shape", ((("return", "int32"),),)) in relation
    # ID は proof digest と interface relation の両方に bind される。
    assert correspondence.callee_correspondence.proof_id == proof.proof_id
    assert relation in correspondence.callee_correspondence.stable_key()


# --------------------------------------------------------------------------
# 15. correspondence authority survives to the solver-proof stage
# --------------------------------------------------------------------------


def test_solver_proof_rebuild_preserves_the_correspondence_authority():
    """manifest 生成時に検証しただけで authority を捨てない。

    `apply_solver_proof_artifacts_to_manifest()` は manifest の dict から
    obligation を組み直すので、PR-D の binding field が落ちないことを固定する。
    """

    from scripts.function_tracer_pcode.proof.call_effect.obligations import (
        RelationalCallEffectObligation,
        apply_solver_proof_artifacts_to_manifest,
    )

    left = _internal_fact_with_callee_proof("L1", "binaryL", 0x1000)
    right = _internal_fact_with_callee_proof("R1", "binaryR", 0x2000)
    candidates, proof = _proof_for([left], [right])
    correspondence, _b = confirm_internal_callsite_correspondence(
        candidates[0], proof, left, right
    )

    obligation = RelationalCallEffectObligation(
        obligation_id="ob1",
        relation_kind="call_to_call",
        observation_contract_id="contract",
        left_fact_id="L1",
        right_fact_id="R1",
        internal_candidate_id=candidates[0].stable_key(),
        callee_correspondence_proof_id=proof.proof_id,
        relational_callee_correspondence_id=correspondence.callee_correspondence.stable_key(),
        fresh_argument_status="independent",
    )
    manifest = {
        "relational_obligations": [obligation.to_dict()],
        "phase2_direct_call_eligibility": [
            {
                "obligation_id": "ob1",
                "status": "ineligible",
                "blockers": ["left_callee_dependency_closure_missing"],
                "required_solver_stages": [],
            }
        ],
        "coupling": {},
        "legacy_blocker_mapping": [],
    }

    apply_solver_proof_artifacts_to_manifest(manifest, ())

    readiness = manifest["proof_readiness"][0]
    assert readiness["obligation_id"] == "ob1"
    # 再構築された obligation に authority が残っている。
    rebuilt = manifest["relational_obligations"][0]
    assert rebuilt["internal_candidate_id"]
    assert rebuilt["callee_correspondence_proof_id"] == proof.proof_id
    assert rebuilt["relational_callee_correspondence_id"]
    assert rebuilt["fresh_argument_status"] == "independent"


def test_readiness_refuses_an_internal_candidate_without_correspondence_authority():
    """internal candidate なのに correspondence id が無い obligation を通さない。"""

    from scripts.function_tracer_pcode.proof.call_effect.obligations import (
        Phase2DirectCallEligibility,
        RelationalCallEffectObligation,
        evaluate_obligation_proof_readiness,
    )

    left = _internal_fact_with_callee_proof("L1", "binaryL", 0x1000)
    right = _internal_fact_with_callee_proof("R1", "binaryR", 0x2000)
    candidates, _proof = _proof_for([left], [right])

    obligation = RelationalCallEffectObligation(
        obligation_id="ob1",
        relation_kind="call_to_call",
        observation_contract_id="contract",
        left_fact_id="L1",
        right_fact_id="R1",
        internal_candidate_id=candidates[0].stable_key(),
        relational_callee_correspondence_id=None,
    )
    eligibility = Phase2DirectCallEligibility(
        obligation_id="ob1", status="candidate", blockers=(), required_solver_stages=(),
    )

    readiness = evaluate_obligation_proof_readiness(obligation, eligibility, ())

    assert "internal_callee_correspondence_authority_missing" in readiness.blockers
    assert readiness.to_dict().get("decision_eligible") is not True


# --------------------------------------------------------------------------
# 16. readiness layer: receipt-to-receipt binding
# --------------------------------------------------------------------------


def _readiness_obligation(**overrides):
    from scripts.function_tracer_pcode.proof.call_effect.obligations import (
        RelationalCallEffectObligation,
    )

    left = _internal_fact_with_callee_proof("L1", "binaryL", 0x1000)
    right = _internal_fact_with_callee_proof("R1", "binaryR", 0x2000)
    candidates, proof = _proof_for([left], [right])
    correspondence, _b = confirm_internal_callsite_correspondence(
        candidates[0], proof, left, right
    )
    fields = dict(
        obligation_id="ob1",
        relation_kind="call_to_call",
        observation_contract_id="contract",
        left_fact_id="L1",
        right_fact_id="R1",
        internal_candidate_id=candidates[0].stable_key(),
        callee_correspondence_proof_id=proof.proof_id,
        relational_callee_correspondence_id=correspondence.callee_correspondence.stable_key(),
    )
    fields.update(overrides)
    return RelationalCallEffectObligation(**fields), proof, candidates[0]


def _readiness_blockers(obligation):
    from scripts.function_tracer_pcode.proof.call_effect.obligations import (
        Phase2DirectCallEligibility,
        evaluate_obligation_proof_readiness,
    )

    eligibility = Phase2DirectCallEligibility(
        obligation_id=obligation.obligation_id,
        status="candidate",
        blockers=(),
        required_solver_stages=(),
    )
    return evaluate_obligation_proof_readiness(obligation, eligibility, ()).blockers


def test_readiness_accepts_a_fully_bound_authority_triple():
    from scripts.function_tracer_pcode.proof.call_effect import obligations as O

    obligation, _proof, _candidate = _readiness_obligation()

    blockers = _readiness_blockers(obligation)

    assert O.INTERNAL_AUTHORITY_MISSING not in blockers
    assert O.INTERNAL_AUTHORITY_MALFORMED not in blockers
    assert O.INTERNAL_AUTHORITY_UNBOUND not in blockers


def test_readiness_rejects_a_missing_relational_id():
    from scripts.function_tracer_pcode.proof.call_effect import obligations as O

    obligation, _p, _c = _readiness_obligation(relational_callee_correspondence_id=None)

    assert O.INTERNAL_AUTHORITY_MISSING in _readiness_blockers(obligation)


def test_readiness_rejects_a_malformed_relational_id():
    from scripts.function_tracer_pcode.proof.call_effect import obligations as O

    for bad in (
        ("wrong_kind", "p", (), (), (), ()),
        ("relational_callee_correspondence", "p", ()),
        ("relational_callee_correspondence", 1, (), (), (), ()),
    ):
        obligation, _p, _c = _readiness_obligation(relational_callee_correspondence_id=bad)
        assert O.INTERNAL_AUTHORITY_MALFORMED in _readiness_blockers(obligation)


def test_readiness_rejects_an_id_bound_to_another_proof():
    """embedded proof_id が運ばれた proof id と食い違えば通さない。"""

    from scripts.function_tracer_pcode.proof.call_effect import obligations as O

    obligation, _p, _c = _readiness_obligation(callee_correspondence_proof_id="deadbeef")

    assert O.INTERNAL_AUTHORITY_UNBOUND in _readiness_blockers(obligation)


def test_readiness_rejects_an_id_bound_to_another_candidate():
    """embedded candidate_key が運ばれた candidate id と食い違えば通さない。"""

    from scripts.function_tracer_pcode.proof.call_effect import obligations as O

    obligation, _p, candidate = _readiness_obligation()
    substituted = ("internal_call_correspondence_candidate", "L9", "R9", ("shape",), ())
    obligation, _p, _c = _readiness_obligation(internal_candidate_id=substituted)

    assert O.INTERNAL_AUTHORITY_UNBOUND in _readiness_blockers(obligation)


def test_readiness_ignores_non_internal_obligations():
    from scripts.function_tracer_pcode.proof.call_effect import obligations as O
    from scripts.function_tracer_pcode.proof.call_effect.obligations import (
        RelationalCallEffectObligation,
    )

    obligation = RelationalCallEffectObligation(
        obligation_id="ob1",
        relation_kind="call_to_region",
        observation_contract_id="contract",
        left_fact_id="L1",
        right_fact_id="R1",
    )

    blockers = _readiness_blockers(obligation)
    for code in (O.INTERNAL_AUTHORITY_MISSING, O.INTERNAL_AUTHORITY_MALFORMED, O.INTERNAL_AUTHORITY_UNBOUND):
        assert code not in blockers

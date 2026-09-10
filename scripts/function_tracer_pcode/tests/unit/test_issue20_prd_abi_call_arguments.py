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
    CALLEE_CONTROL_PROFILE_RELATION_MISSING,
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
    )
    fields.update(overrides)
    return _internal_call_fact(fact_id, binary_id, ("shape", "a"), offset, **fields)


def test_callee_correspondence_completes_the_callsite_correspondence():
    from scripts.function_tracer_pcode.proof.call_effect.candidates import (
        build_relational_callee_correspondence,
    )

    left = _internal_fact_with_callee_proof("L1", "binaryL", 0x1000)
    right = _internal_fact_with_callee_proof("R1", "binaryR", 0x2000)
    candidate = build_internal_call_correspondence_candidates([left], [right]).candidates[0]

    callee_id, callee_blockers = build_relational_callee_correspondence(candidate, left, right)
    assert callee_blockers == ()
    assert callee_id is not None
    assert callee_id.candidate_key == candidate.stable_key()

    correspondence, blockers = confirm_internal_callsite_correspondence(candidate, left, right)
    assert blockers == ()
    assert correspondence is not None
    assert correspondence.callee_correspondence.stable_key() == callee_id.stable_key()
    assert correspondence.argument_relation_key[0] == "relational_argument"


def test_without_a_callee_correspondence_the_callsite_correspondence_fails_closed():
    """``RelationalCalleeCorrespondenceId`` が無ければ correspondence は成立しない。"""

    left = _internal_fact_with_callee_proof("L1", "binaryL", 0x1000)
    right = _internal_fact_with_callee_proof(
        "R1", "binaryR", 0x2000, callee_return_summary_statuses=("inconclusive",),
    )
    candidate = build_internal_call_correspondence_candidates([left], [right]).candidates[0]

    correspondence, blockers = confirm_internal_callsite_correspondence(candidate, left, right)

    assert correspondence is None
    assert CALLEE_RETURN_SUMMARY_UNPROVEN in blockers
    assert CALLSITE_CALLEE_CORRESPONDENCE_MISSING in blockers


def test_without_a_candidate_the_callsite_correspondence_fails_closed():
    left = _internal_fact_with_callee_proof("L1", "binaryL", 0x1000)
    right = _internal_fact_with_callee_proof("R1", "binaryR", 0x2000)

    correspondence, blockers = confirm_internal_callsite_correspondence(None, left, right)

    assert correspondence is None
    assert blockers == (CALLSITE_CANDIDATE_MISSING,)


def test_callee_correspondence_does_not_require_structural_agreement():
    """左右で効果数が違っても correspondence の identity は成立する。

    同じ番地を 2 回上書きする callee と 1 回だけ書く callee は最終状態が同じなら
    等価であり、等価性は後段 ``memory_relation`` が証明する。ここで構造一致を
    要求すると、証明できるはずの等価を先回りして潰してしまう。
    """

    from scripts.function_tracer_pcode.proof.call_effect.candidates import (
        build_relational_callee_correspondence,
    )

    left = _internal_fact_with_callee_proof("L1", "binaryL", 0x1000, callee_memory_effect_counts=(2,))
    right = _internal_fact_with_callee_proof("R1", "binaryR", 0x2000, callee_memory_effect_counts=(1,))
    candidate = build_internal_call_correspondence_candidates([left], [right]).candidates[0]

    callee_id, blockers = build_relational_callee_correspondence(candidate, left, right)

    assert blockers == ()
    assert callee_id is not None
    assert callee_id.left_callee_effect_key != callee_id.right_callee_effect_key


def test_ambiguous_callee_summary_blocks_the_callee_correspondence():
    from scripts.function_tracer_pcode.proof.call_effect.candidates import (
        build_relational_callee_correspondence,
    )

    left = _internal_fact_with_callee_proof("L1", "binaryL", 0x1000, callee_control_profile_keys=())
    right = _internal_fact_with_callee_proof("R1", "binaryR", 0x2000)
    candidate = build_internal_call_correspondence_candidates([left], [right]).candidates[0]

    callee_id, blockers = build_relational_callee_correspondence(candidate, left, right)

    assert callee_id is None
    assert CALLEE_CONTROL_PROFILE_RELATION_MISSING in blockers


# --------------------------------------------------------------------------
# 12. integration: corresponding ABI slots, side-specific fresh values
# --------------------------------------------------------------------------


def _abi_evidence_with_fresh_slot(binary_id, offset):
    """Both sides resolve the same ABI slot but cannot observe the value."""

    tracer = _Tracer(binary_id=binary_id)
    tracer.trace_varnode = lambda *_a, **_k: None
    call_op = _CallOp([_Varnode(8, storage=_register_storage("d1", 0x5020))], offset=offset)
    callee_parameters = [_callee_parameter(0, "__x", _register_storage("d0", 0x5000))]
    evidence, reason = abi._impl__recover_abi_call_argument_evidence(
        call_op, tracer, [], callee_parameters, _target_ref(), binary_id=binary_id
    )
    assert reason is None, reason
    return evidence


def test_corresponding_abi_slots_keep_side_specific_fresh_values():
    """左右で対応する ABI slot / 値は side-specific fresh / SMT symbol は別物。

    そのうえで、relational equality proof が無い限り無条件 `NOT_EQ` に到達
    できないことを authority 層まで通して確認する。
    """

    from scripts.function_tracer_pcode.core.render_smt.unknowns import (
        collect_unknown_smt_declarations,
    )
    from scripts.function_tracer_pcode.proof.call_effect.obligations import (
        RelationalCallEffectObligation,
        _phase2_direct_call_eligibility,
    )
    from scripts.function_tracer_pcode.authority.domains.call_effect import (
        classify_call_eligibility_blocker,
    )

    left_evidence = _abi_evidence_with_fresh_slot("binaryL", 0x1000)
    right_evidence = _abi_evidence_with_fresh_slot("binaryR", 0x2000)

    # (a) ABI スロットの identity correspondence は成立している。
    left_slot = left_evidence.abi_argument_slots[0]
    right_slot = right_evidence.abi_argument_slots[0]
    assert left_slot.stable_key() == right_slot.stable_key()

    # (b) 値は side-specific fresh のまま。
    left_fresh = left_evidence.fresh_argument_refs[0]
    right_fresh = right_evidence.fresh_argument_refs[0]
    assert fresh_call_argument_refs_are_side_distinct(left_fresh, right_fresh)
    assert left_fresh.identity_correspondence_key() == right_fresh.identity_correspondence_key()
    assert left_fresh.stable_key() != right_fresh.stable_key()

    # (c) SMT シンボルが別物。
    left_symbols = collect_unknown_smt_declarations(left_evidence.arguments[0])
    right_symbols = collect_unknown_smt_declarations(right_evidence.arguments[0])
    assert left_symbols and right_symbols
    assert left_symbols[0][0] != right_symbols[0][0]
    assert left_symbols[0][1] == right_symbols[0][1] == 64

    # (d) 証明が無ければ coupling しない。irrelevance も coupling ではない。
    assert couple_fresh_arguments(left_fresh, right_fresh) is None
    assert fresh_arguments_are_independent(left_fresh, right_fresh) is True
    assert (
        fresh_argument_correspondence_status(
            [left_fresh.stable_key()], [right_fresh.stable_key()]
        )
        == FRESH_ARGUMENT_STATUS_INDEPENDENT
    )

    # (e) 値が観測できていないので証拠は complete を名乗らない。
    for evidence in (left_evidence, right_evidence):
        assert evidence.coverage_complete is False
        assert evidence.recovery_status == CallArgumentEvidence.RECOVERY_RECOVERABLE_PARTIAL

    # (f) SAT が得られても無条件 NOT_EQ には到達できない: 引数証拠が
    #     complete でない以上、pair は relational stage の候補にならない。
    left_fact = _internal_fact_with_callee_proof(
        "L1", "binaryL", 0x1000,
        extraction_status="inconclusive",
        extraction_failure_causes=("argument_coverage_incomplete",),
        fresh_argument_keys=(tuple(left_fresh.stable_key()),),
        abi_argument_slot_keys=(tuple(left_slot.stable_key()),),
    )
    right_fact = _internal_fact_with_callee_proof(
        "R1", "binaryR", 0x2000,
        extraction_status="inconclusive",
        extraction_failure_causes=("argument_coverage_incomplete",),
        fresh_argument_keys=(tuple(right_fresh.stable_key()),),
        abi_argument_slot_keys=(tuple(right_slot.stable_key()),),
    )
    obligation = RelationalCallEffectObligation(
        obligation_id="ob1",
        relation_kind="call_to_call",
        observation_contract_id="contract",
        left_fact_id="L1",
        right_fact_id="R1",
    )
    eligibility = _phase2_direct_call_eligibility(
        obligation, {"L1": left_fact}, {"R1": right_fact}
    )

    assert eligibility.status == "ineligible"
    assert eligibility.required_solver_stages == ()
    assert "left_extraction_argument_coverage_incomplete" in eligibility.blockers
    assert "right_extraction_argument_coverage_incomplete" in eligibility.blockers
    # 左右 fresh は別シンボルのままなので、その値の食い違いを根拠に
    # 無条件の非等価を主張することはできない。
    assert set(left_fact.fresh_argument_keys) & set(right_fact.fresh_argument_keys) == set()
    classified = {
        classify_call_eligibility_blocker(b).reason_id for b in eligibility.blockers
    }
    assert "abi_argument_relation_unproven" in classified


def test_relational_equality_proof_is_the_only_way_to_couple_fresh_arguments():
    left_evidence = _abi_evidence_with_fresh_slot("binaryL", 0x1000)
    right_evidence = _abi_evidence_with_fresh_slot("binaryR", 0x2000)
    left_fresh = left_evidence.fresh_argument_refs[0]
    right_fresh = right_evidence.fresh_argument_refs[0]

    assert couple_fresh_arguments(left_fresh, right_fresh) is None

    proof = RelationalEqualityProof(
        proof_id="rel-1",
        left_key=left_fresh.stable_key(),
        right_key=right_fresh.stable_key(),
        premise_digest="digest",
        obligation_id="ob1",
        discharged=True,
    )
    coupling = couple_fresh_arguments(left_fresh, right_fresh, proof)

    assert coupling is not None
    assert coupling.coupled_symbol_key() is not None
    # coupling されても DTO の identity は side-specific のまま（記録が残る）。
    assert left_fresh.stable_key() != right_fresh.stable_key()


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

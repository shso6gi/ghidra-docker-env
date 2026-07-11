from scripts.function_tracer_pcode.tests.unit._memory_model_fixtures import *

def test_recoverable_partial_call_argument_evidence_does_not_become_incomplete_blocker():
    pcode_ref = PcodeOpRef(address_offset=0x1008, seq_time=1, seq_order=0, mnemonic="CALL")
    deferred = DeferredCallInfo(
        placeholder_name="call_out_of_scope:callee#0",
        target_ref=CallTargetRef.from_name("callee", entry_offset=0x2000),
        arguments=[Expression.parameter("existing_arg", 0, size=4)],
        deferred_call_ref=DeferredCallRef(
            pcode_op_ref=pcode_ref,
            target_ref=CallTargetRef.from_name("callee", entry_offset=0x2000),
            sequence=0,
        ),
    )
    analysis = FunctionReturnAnalysis(
        function_name="caller",
        entry_point="0x1000",
        returns=[],
        parameters=[{"name": "param_1", "index": 0, "size": 4}],
    )
    analysis.deferred_calls = {deferred.deferred_call_ref.stable_key(): deferred}
    analysis.effect_summary = EffectSummary(
        parameter_names=["param_1"],
        effects=[],
        call_argument_evidence={
            pcode_ref.stable_key(): CallArgumentEvidence(
                pcode_op_ref=pcode_ref,
                target_ref=CallTargetRef.from_name("callee", entry_offset=0x2000),
                callee_param_identities=(("parameter", 0), ("parameter", 1)),
                arguments=(Expression.parameter("param_1", 0, size=4),),
                sources=("explicit_input",),
                path_conditions=((),),
                coverage_complete=False,
                recovery_status=CallArgumentEvidence.RECOVERY_RECOVERABLE_PARTIAL,
                reason="argument_recovery_recoverable_partial",
            )
        },
    )

    ReturnAnalyzer(program=None, debug=False)._apply_effect_call_argument_evidence_to_deferred_calls(analysis)

    assert len(deferred.arguments) == 1
    assert deferred.arguments[0].to_dict() == Expression.parameter("existing_arg", 0, size=4).to_dict()
    assert deferred.call_argument_recovery_status == CallArgumentEvidence.RECOVERY_RECOVERABLE_PARTIAL
    assert deferred.call_argument_recovery_reason == "argument_recovery_recoverable_partial"
    assert "effect_call_argument_evidence_incomplete" not in analysis.analysis_notes
    assert "effect_call_argument_evidence" not in analysis.analysis_notes

def test_clear_resolved_call_effect_blockers_preserves_call_argument_evidence_note():
    pcode_ref = PcodeOpRef(address_offset=0x1010, seq_time=1, seq_order=0, mnemonic="CALL")
    analysis = FunctionReturnAnalysis(
        function_name="caller",
        entry_point="0x1000",
        returns=[ReturnInfo(address="0x1000", value=Expression.constant(0, size=4), conditions=[])],
        parameters=[{"name": "param_1", "index": 0, "size": 4}],
        analysis_notes=["effect_call_argument_evidence"],
        effect_summary=EffectSummary(
            parameter_names=["param_1"],
            effects=[],
            call_argument_evidence={
                pcode_ref.stable_key(): CallArgumentEvidence(
                    pcode_op_ref=pcode_ref,
                    target_ref=CallTargetRef.from_name("callee", entry_offset=0x2000),
                    callee_param_identities=(("parameter", 0),),
                    arguments=(Expression.parameter("param_1", 0, size=4),),
                    sources=("explicit_input",),
                    path_conditions=((),),
                    coverage_complete=True,
                    recovery_status=CallArgumentEvidence.RECOVERY_COMPLETE,
                )
            },
        ),
    )

    ReturnAnalyzer(program=None, debug=False)._clear_resolved_call_effect_blockers(analysis)

    assert "effect_call_argument_evidence" in analysis.analysis_notes
    assert "bounded_call_effect_resolved" not in analysis.analysis_notes
    assert analysis.effect_summary.call_argument_evidence

def test_clear_resolved_call_effect_blockers_clears_empty_bounded_call_notes():
    analysis = FunctionReturnAnalysis(
        function_name="caller",
        entry_point="0x1000",
        returns=[ReturnInfo(address="0x1000", value=Expression.constant(0, size=4), conditions=[])],
        parameters=[{"name": "param_1", "index": 0, "size": 4}],
        analysis_notes=[
            "effect_call_argument_evidence",
            "effect_call_argument_evidence_incomplete",
            "bounded_call_refinement",
        ],
        effect_summary=EffectSummary(parameter_names=["param_1"], effects=[]),
    )

    ReturnAnalyzer(program=None, debug=False)._clear_resolved_call_effect_blockers(analysis)

    assert "effect_call_argument_evidence" not in analysis.analysis_notes
    assert "effect_call_argument_evidence_incomplete" not in analysis.analysis_notes
    assert "bounded_call_effect_resolved" in analysis.analysis_notes

def test_inconclusive_call_argument_evidence_marks_existing_recovered_args_inconclusive():
    pcode_ref = PcodeOpRef(address_offset=0x1011, seq_time=1, seq_order=1, mnemonic="CALL")
    deferred = DeferredCallInfo(
        placeholder_name="call_out_of_scope:callee#0",
        target_ref=CallTargetRef.from_name("callee"),
        arguments=[Expression.parameter("param_1", 0, size=4)],
        deferred_call_ref=DeferredCallRef(
            pcode_op_ref=pcode_ref,
            target_ref=CallTargetRef.from_name("callee"),
            sequence=0,
        ),
        call_argument_recovery_status=CallArgumentEvidence.RECOVERY_COMPLETE,
    )
    analysis = FunctionReturnAnalysis(
        function_name="caller",
        entry_point="0x1000",
        returns=[],
        parameters=[{"name": "param_1", "index": 0, "size": 4}],
    )
    analysis.deferred_calls = {deferred.deferred_call_ref.stable_key(): deferred}
    analysis.effect_summary = EffectSummary(
        parameter_names=["param_1"],
        effects=[],
        call_argument_evidence={
            pcode_ref.stable_key(): CallArgumentEvidence(
                pcode_op_ref=pcode_ref,
                target_ref=CallTargetRef.from_name("callee"),
                callee_param_identities=(("parameter", 0),),
                arguments=(),
                sources=(),
                path_conditions=((),),
                coverage_complete=False,
                reason="argument_recovery_incomplete",
            )
        },
    )

    ReturnAnalyzer(program=None, debug=False)._apply_effect_call_argument_evidence_to_deferred_calls(analysis)

    assert len(deferred.arguments) == 1
    assert deferred.arguments[0].to_dict() == Expression.parameter("param_1", 0, size=4).to_dict()
    assert deferred.call_argument_recovery_status == CallArgumentEvidence.RECOVERY_INCONCLUSIVE
    assert deferred.call_argument_recovery_reason == "argument_recovery_incomplete"
    assert "effect_call_argument_evidence_incomplete" in analysis.analysis_notes

def test_complete_call_argument_evidence_is_applied_to_deferred_call_and_marked_complete():
    pcode_ref = PcodeOpRef(address_offset=0x1018, seq_time=1, seq_order=0, mnemonic="CALL")
    deferred = DeferredCallInfo(
        placeholder_name="call_out_of_scope:callee#0",
        target_ref=CallTargetRef.from_name("callee", entry_offset=0x2000),
        deferred_call_ref=DeferredCallRef(
            pcode_op_ref=pcode_ref,
            target_ref=CallTargetRef.from_name("callee", entry_offset=0x2000),
            sequence=0,
        ),
    )
    analysis = FunctionReturnAnalysis(
        function_name="caller",
        entry_point="0x1000",
        returns=[],
        parameters=[{"name": "param_1", "index": 0, "size": 4}],
    )
    analysis.deferred_calls = {deferred.deferred_call_ref.stable_key(): deferred}
    analysis.effect_summary = EffectSummary(
        parameter_names=["param_1"],
        effects=[],
        call_argument_evidence={
            pcode_ref.stable_key(): CallArgumentEvidence(
                pcode_op_ref=pcode_ref,
                target_ref=CallTargetRef.from_name("callee", entry_offset=0x2000),
                callee_param_identities=(("parameter", 0),),
                arguments=(Expression.parameter("param_1", 0, size=4),),
                sources=("explicit_input",),
                path_conditions=((),),
                coverage_complete=True,
            )
        },
    )

    ReturnAnalyzer(program=None, debug=False)._apply_effect_call_argument_evidence_to_deferred_calls(analysis)

    assert len(deferred.arguments) == 1
    assert deferred.arguments[0].to_dict() == Expression.parameter("param_1", 0, size=4).to_dict()
    assert deferred.call_argument_recovery_status == CallArgumentEvidence.RECOVERY_COMPLETE
    assert deferred.call_argument_recovery_reason is None
    assert "effect_call_argument_evidence" in analysis.analysis_notes
    assert "effect_call_argument_evidence_incomplete" not in analysis.analysis_notes

def test_deferred_call_default_recovery_status_is_inconclusive_without_proof():
    deferred_with_args = DeferredCallInfo(
        placeholder_name="call_out_of_scope:callee#0",
        target_ref=CallTargetRef.from_name("callee"),
        arguments=[Expression.parameter("param_1", 0, size=4)],
    )
    assert deferred_with_args.call_argument_recovery_status == CallArgumentEvidence.RECOVERY_INCONCLUSIVE

    deferred_without_args = DeferredCallInfo(
        placeholder_name="call_out_of_scope:callee#1",
        target_ref=CallTargetRef.from_name("callee"),
        arguments=[],
    )
    assert deferred_without_args.call_argument_recovery_status == CallArgumentEvidence.RECOVERY_INCONCLUSIVE

    deferred_unknown_args = DeferredCallInfo(
        placeholder_name="call_out_of_scope:callee#2",
        target_ref=CallTargetRef.from_name("callee"),
    )
    assert deferred_unknown_args.call_argument_recovery_status == CallArgumentEvidence.RECOVERY_INCONCLUSIVE

def test_recoverable_partial_call_argument_evidence_state_is_not_decisive():
    pcode_ref = PcodeOpRef(address_offset=0x1010, seq_time=1, seq_order=0, mnemonic="CALL")
    deferred = DeferredCallInfo(
        placeholder_name="call_out_of_scope:callee#0",
        target_ref=CallTargetRef.from_name("callee", entry_offset=0x2000),
        deferred_call_ref=DeferredCallRef(
            pcode_op_ref=pcode_ref,
            target_ref=CallTargetRef.from_name("callee", entry_offset=0x2000),
            sequence=0,
        ),
    )
    analysis = FunctionReturnAnalysis(
        function_name="caller",
        entry_point="0x1000",
        returns=[],
        parameters=[{"name": "param_1", "index": 0, "size": 4}],
    )
    analysis.deferred_calls = {deferred.deferred_call_ref.stable_key(): deferred}
    analysis.effect_summary = EffectSummary(
        parameter_names=["param_1"],
        effects=[],
        call_argument_evidence={
            pcode_ref.stable_key(): CallArgumentEvidence(
                pcode_op_ref=pcode_ref,
                target_ref=CallTargetRef.from_name("callee", entry_offset=0x2000),
                callee_param_identities=(("parameter", 0), ("parameter", 1)),
                arguments=(Expression.parameter("param_1", 0, size=4),),
                sources=("explicit_input",),
                path_conditions=((),),
                coverage_complete=False,
                recovery_status=CallArgumentEvidence.RECOVERY_RECOVERABLE_PARTIAL,
                reason="argument_recovery_recoverable_partial",
            )
        },
    )

    ReturnAnalyzer(program=None, debug=False)._apply_effect_call_argument_evidence_to_deferred_calls(analysis)

    assert "effect_call_argument_evidence_incomplete" not in analysis.get_decisive_sat_unsafety_reasons()
    assert deferred.call_argument_recovery_status == CallArgumentEvidence.RECOVERY_RECOVERABLE_PARTIAL
    assert deferred.call_argument_recovery_reason == "argument_recovery_recoverable_partial"

def test_call_argument_recovery_state_survives_specialize_and_merge_deferred_call_flow():
    analyzer = ReturnAnalyzer(program=None, debug=False)
    deferred = DeferredCallInfo(
        placeholder_name="call_out_of_scope:callee#0",
        target_ref=CallTargetRef.from_name("callee"),
        arguments=[Expression.parameter("param_1", 0, size=4)],
        call_argument_recovery_status=CallArgumentEvidence.RECOVERY_RECOVERABLE_PARTIAL,
        call_argument_recovery_reason="argument_recovery_recoverable_partial",
    )
    analysis = FunctionReturnAnalysis(
        function_name="callee",
        entry_point="0x2000",
        parameters=[{"name": "param_1", "index": 0, "size": 4}],
        returns=[],
    )
    analysis.deferred_calls = {deferred.deferred_call_ref.stable_key(): deferred}

    specialized = analyzer._specialize_call_analysis(
        analysis,
        [Expression.parameter("specialized_param_1", 0, size=4)],
    )
    specialized_deferred = next(iter(specialized.deferred_calls.values()))
    assert specialized_deferred.call_argument_recovery_status == CallArgumentEvidence.RECOVERY_RECOVERABLE_PARTIAL
    assert (
        specialized_deferred.call_argument_recovery_reason
        == "argument_recovery_recoverable_partial"
    )

    analyzer._current_deferred_calls = {}
    analyzer._merge_deferred_calls_into_current_analysis(specialized.deferred_calls)
    merged = next(iter(analyzer._current_deferred_calls.values()))
    assert merged.call_argument_recovery_status == CallArgumentEvidence.RECOVERY_RECOVERABLE_PARTIAL
    assert merged.call_argument_recovery_reason == "argument_recovery_recoverable_partial"

def test_specialize_call_analysis_preserves_summary_proof_metadata():
    analyzer = ReturnAnalyzer(program=None, debug=False)
    proof_target = ("return_region_summary_target", ("value", "x"), ("guards",), ("witness",), ("coverage",))
    proof_id = ("proof_obligation_id", "return_region_summary", proof_target)
    proof_ref = ("return_region_summary_proof_ref", proof_id, proof_target)
    analysis = FunctionReturnAnalysis(
        function_name="callee",
        entry_point="0x2000",
        parameters=[{"name": "param_1", "index": 0, "size": 4}],
        returns=[
            ReturnInfo(
                address="0x2000",
                value=Expression.parameter("param_1", 0, size=4),
                conditions=[],
                return_kind="summary_derived",
                acceptance_status="accepted",
                summary_candidate_id=("candidate", 1),
                summary_candidate_source_key=("source", "recurrence"),
                summary_transition_evidence_key=proof_ref,
            )
        ],
        completed_recovery_proof_evidence=(
            {
                "proof_obligation_id": proof_id,
                "proof_stage": "return_region_summary",
                "object_target_key": proof_target,
                "proof_content": {"object_target_key": proof_target},
            },
        ),
        analysis_view_identity=("accepted_return_partition_view", ("partition", 1)),
        partition_revision=1,
    )

    specialized = analyzer._specialize_call_analysis(
        analysis,
        [Expression.parameter("caller_arg", 0, size=4)],
    )

    specialized_return = specialized.returns[0]
    assert specialized_return.return_kind == "summary_derived"
    assert specialized_return.summary_candidate_id == ("candidate", 1)
    assert specialized_return.summary_candidate_source_key == ("source", "recurrence")
    assert specialized_return.summary_transition_evidence_key == proof_ref
    assert specialized.completed_recovery_proof_evidence == analysis.completed_recovery_proof_evidence
    assert specialized.analysis_view_identity == analysis.analysis_view_identity
    assert specialized.partition_revision == 1

def test_merge_deferred_calls_into_current_analysis_preserves_most_conservative_state():
    analyzer = ReturnAnalyzer(program=None, debug=False)
    pcode_ref = PcodeOpRef(address_offset=0x2020, seq_time=1, seq_order=0, mnemonic="CALL")
    deferred_ref = DeferredCallRef(
        pcode_op_ref=pcode_ref,
        target_ref=CallTargetRef.from_name("callee"),
        sequence=0,
    )
    analyzer._current_deferred_calls = {
        deferred_ref.stable_key(): DeferredCallInfo(
            placeholder_name="call_out_of_scope:callee#0",
            target_ref=CallTargetRef.from_name("callee"),
            arguments=[Expression.parameter("known", 0, size=4)],
            deferred_call_ref=deferred_ref,
            call_argument_recovery_status=CallArgumentEvidence.RECOVERY_COMPLETE,
        )
    }
    analyzer._merge_deferred_calls_into_current_analysis(
        {
            deferred_ref.stable_key(): DeferredCallInfo(
                placeholder_name="call_out_of_scope:callee#0",
                target_ref=CallTargetRef.from_name("callee"),
                arguments=[],
                deferred_call_ref=deferred_ref,
                call_argument_recovery_status=CallArgumentEvidence.RECOVERY_INCONCLUSIVE,
                call_argument_recovery_reason="argument_recovery_inconclusive",
            )
        }
    )

    merged = next(iter(analyzer._current_deferred_calls.values()))
    assert merged.call_argument_recovery_status == CallArgumentEvidence.RECOVERY_INCONCLUSIVE
    assert merged.call_argument_recovery_reason == "argument_recovery_inconclusive"

def test_tri_state_call_argument_evidence_merge_preserves_usable_evidence():
    pcode_ref = PcodeOpRef(address_offset=0x1010, seq_time=2, seq_order=0, mnemonic="CALL")
    arg0 = Expression.parameter("param_1", 0, size=4)
    arg1 = Expression.parameter("param_2", 1, size=4)
    complete = CallArgumentEvidence(
        pcode_op_ref=pcode_ref,
        target_ref=CallTargetRef.from_name("callee", entry_offset=0x2000),
        callee_param_identities=(("parameter", 0), ("parameter", 1)),
        arguments=(arg0, arg1),
        sources=("explicit_input", "explicit_input"),
        path_conditions=((),),
        coverage_complete=True,
    )
    recoverable_partial = CallArgumentEvidence(
        pcode_op_ref=pcode_ref,
        target_ref=CallTargetRef.from_name("callee", entry_offset=0x2000),
        callee_param_identities=(("parameter", 0), ("parameter", 1)),
        arguments=(arg0,),
        sources=("explicit_input",),
        path_conditions=((),),
        coverage_complete=False,
        recovery_status=CallArgumentEvidence.RECOVERY_RECOVERABLE_PARTIAL,
        reason="argument_recovery_recoverable_partial",
    )

    merged = _merge_call_argument_evidence(complete, recoverable_partial)
    reverse_merged = _merge_call_argument_evidence(recoverable_partial, complete)

    assert merged.is_usable() is True
    assert merged.recovery_status == CallArgumentEvidence.RECOVERY_COMPLETE
    assert merged.arguments == (arg0, arg1)
    assert len(merged.path_conditions) == 2
    assert reverse_merged.is_usable() is True
    assert reverse_merged.arguments == (arg0, arg1)

def test_zero_argument_call_evidence_is_usable_for_true_no_arg_callee():
    class FakeTracer:
        def __init__(self, ref):
            self.ref = ref

        def _make_pcode_op_ref(self, _op):
            return self.ref

    pcode_ref = PcodeOpRef(address_offset=0x1100, seq_time=2, seq_order=0, mnemonic="CALL")
    evidence_map = {}

    _record_call_argument_evidence(
        evidence_map,
        FakeTracer(pcode_ref),
        object(),
        CallTargetRef.from_name("callee", entry_offset=0x2000),
        [],
        [],
        [],
        coverage_complete=True,
    )

    evidence = evidence_map[pcode_ref.stable_key()]
    assert evidence.is_usable() is True
    assert evidence.coverage_complete is True
    assert evidence.arguments == ()

def test_call_argument_evidence_keeps_multiple_targets_for_same_callsite_separate():
    class FakeTracer:
        def __init__(self, ref):
            self.ref = ref

        def _make_pcode_op_ref(self, _op):
            return self.ref

    pcode_ref = PcodeOpRef(address_offset=0x1110, seq_time=2, seq_order=1, mnemonic="CALLIND")
    tracer = FakeTracer(pcode_ref)
    target_a = CallTargetRef.from_name("callee_a", entry_offset=0x2000)
    target_b = CallTargetRef.from_name("callee_b", entry_offset=0x3000)
    evidence_map = {}

    _record_call_argument_evidence(
        evidence_map,
        tracer,
        object(),
        target_a,
        [{"name": "arg", "index": 0}],
        [Expression.parameter("arg_a", 0, size=4)],
        [],
        coverage_complete=True,
    )
    _record_call_argument_evidence(
        evidence_map,
        tracer,
        object(),
        target_b,
        [{"name": "arg", "index": 0}],
        [Expression.parameter("arg_b", 0, size=4)],
        [],
        coverage_complete=True,
    )

    base_key = pcode_ref.stable_key()
    target_a_key = _call_argument_evidence_storage_key(base_key, target_a)
    target_b_key = _call_argument_evidence_storage_key(base_key, target_b)

    assert base_key not in evidence_map
    assert set(evidence_map) == {target_a_key, target_b_key}
    assert evidence_map[target_a_key].is_usable() is True
    assert evidence_map[target_b_key].is_usable() is True
    assert evidence_map[target_a_key].arguments[0].name == "arg_a"
    assert evidence_map[target_b_key].arguments[0].name == "arg_b"

def test_call_argument_evidence_merges_reappearing_target_after_target_specific_split():
    class FakeTracer:
        def __init__(self, ref):
            self.ref = ref

        def _make_pcode_op_ref(self, _op):
            return self.ref

    pcode_ref = PcodeOpRef(address_offset=0x1114, seq_time=2, seq_order=1, mnemonic="CALLIND")
    tracer = FakeTracer(pcode_ref)
    target_a = CallTargetRef.from_name("callee_a", entry_offset=0x2000)
    target_b = CallTargetRef.from_name("callee_b", entry_offset=0x3000)
    arg_a = Expression.parameter("arg_a", 0, size=4)
    arg_b = Expression.parameter("arg_b", 0, size=4)
    condition_a0 = Condition(
        Expression.binary_op("INT_EQUAL", Expression.parameter("mode", 1, size=4), Expression.constant(0, 4))
    )
    condition_a1 = Condition(
        Expression.binary_op("INT_EQUAL", Expression.parameter("mode", 1, size=4), Expression.constant(2, 4))
    )
    condition_b = Condition(
        Expression.binary_op("INT_EQUAL", Expression.parameter("mode", 1, size=4), Expression.constant(1, 4))
    )
    evidence_map = {}

    _record_call_argument_evidence(
        evidence_map,
        tracer,
        object(),
        target_a,
        [{"name": "arg", "index": 0}],
        [arg_a],
        [condition_a0],
        coverage_complete=True,
    )
    _record_call_argument_evidence(
        evidence_map,
        tracer,
        object(),
        target_b,
        [{"name": "arg", "index": 0}],
        [arg_b],
        [condition_b],
        coverage_complete=True,
    )
    _record_call_argument_evidence(
        evidence_map,
        tracer,
        object(),
        target_a,
        [{"name": "arg", "index": 0}],
        [arg_a],
        [condition_a1],
        coverage_complete=True,
    )

    base_key = pcode_ref.stable_key()
    target_a_key = _call_argument_evidence_storage_key(base_key, target_a)
    target_b_key = _call_argument_evidence_storage_key(base_key, target_b)

    assert base_key not in evidence_map
    assert set(evidence_map) == {target_a_key, target_b_key}
    assert evidence_map[target_a_key].is_usable() is True
    assert evidence_map[target_a_key].arguments == (arg_a,)
    assert len(evidence_map[target_a_key].path_conditions) == 2
    assert evidence_map[target_b_key].arguments == (arg_b,)

def test_target_specific_call_argument_evidence_is_applied_to_matching_deferred_call():
    pcode_ref = PcodeOpRef(address_offset=0x1118, seq_time=3, seq_order=0, mnemonic="CALLIND")
    target_a = CallTargetRef.from_name("callee_a", entry_offset=0x2000)
    target_b = CallTargetRef.from_name("callee_b", entry_offset=0x3000)
    target_a_key = _call_argument_evidence_storage_key(pcode_ref.stable_key(), target_a)
    target_b_key = _call_argument_evidence_storage_key(pcode_ref.stable_key(), target_b)
    deferred_a = DeferredCallInfo(
        placeholder_name="call_out_of_scope:callee_a#0",
        target_ref=target_a,
        deferred_call_ref=DeferredCallRef(
            pcode_op_ref=pcode_ref,
            target_ref=target_a,
            sequence=0,
        ),
    )
    deferred_b = DeferredCallInfo(
        placeholder_name="call_out_of_scope:callee_b#0",
        target_ref=target_b,
        deferred_call_ref=DeferredCallRef(
            pcode_op_ref=pcode_ref,
            target_ref=target_b,
            sequence=1,
        ),
    )
    analysis = FunctionReturnAnalysis(
        function_name="caller",
        entry_point="0x1000",
        returns=[],
        parameters=[{"name": "arg", "index": 0, "size": 4}],
    )
    analysis.deferred_calls = {
        deferred_a.deferred_call_ref.stable_key(): deferred_a,
        deferred_b.deferred_call_ref.stable_key(): deferred_b,
    }
    analysis.effect_summary = EffectSummary(
        parameter_names=["arg"],
        effects=[],
        call_argument_evidence={
            target_a_key: CallArgumentEvidence(
                pcode_op_ref=pcode_ref,
                target_ref=target_a,
                callee_param_identities=(("parameter", 0),),
                arguments=(Expression.parameter("arg_a", 0, size=4),),
                sources=("explicit_input",),
                path_conditions=((),),
                coverage_complete=True,
            ),
            target_b_key: CallArgumentEvidence(
                pcode_op_ref=pcode_ref,
                target_ref=target_b,
                callee_param_identities=(("parameter", 0),),
                arguments=(Expression.parameter("arg_b", 0, size=4),),
                sources=("explicit_input",),
                path_conditions=((),),
                coverage_complete=True,
            ),
        },
    )

    ReturnAnalyzer(program=None, debug=False)._apply_effect_call_argument_evidence_to_deferred_calls(analysis)

    assert deferred_a.call_argument_recovery_status == CallArgumentEvidence.RECOVERY_COMPLETE
    assert deferred_b.call_argument_recovery_status == CallArgumentEvidence.RECOVERY_COMPLETE
    assert deferred_a.arguments[0].name == "arg_a"
    assert deferred_b.arguments[0].name == "arg_b"
    assert "effect_call_argument_evidence" in analysis.analysis_notes
    assert "effect_call_argument_evidence_incomplete" not in analysis.analysis_notes

def test_callee_parameter_ref_refuses_positional_identity_without_index_or_storage():
    assert _coerce_callee_parameter_ref({"name": "param_1"}, 0) is None
    assert _coerce_callee_parameter_ref("param_1", 0) is None

    explicit = _coerce_callee_parameter_ref({"name": "param_1", "index": 0}, 7)
    assert explicit is not None
    assert explicit.parameter_index == 0

    storage_only = _coerce_callee_parameter_ref(
        {"name": "param_1", "storage": _reg_storage("a0", size_bytes=8)},
        7,
    )
    assert storage_only is not None
    assert storage_only.is_storage()
    assert storage_only.storage_identity_key[0] == "register_storage"

def test_build_parameter_replacements_refuses_name_or_string_only_callee_params():
    arg = Expression.parameter("arg_1", 0, size=4)

    assert _build_parameter_replacements([{"name": "param_1"}], [arg]) == {}
    assert _build_parameter_replacements(["param_1"], [arg]) == {}

def test_build_parameter_replacements_accepts_storage_only_callee_identity():
    arg = Expression.parameter("arg_1", 0, size=4)
    replacements = _build_parameter_replacements(
        [
            {
                "name": "param_1",
                "size": 4,
                "storage": _reg_storage("a0", size_bytes=4),
            }
        ],
        [arg],
    )

    assert any(key and key[0] == "register_storage" for key in replacements)

def test_call_evidence_callee_param_identities_reject_unproven_ordinals():
    assert _call_evidence_callee_param_identities([{"name": "param_1"}]) == ()

    storage_identity = _call_evidence_callee_param_identities(
        [{"name": "param_1", "storage": _reg_storage("a0", size_bytes=8)}]
    )
    assert len(storage_identity) == 1
    assert storage_identity[0][0][0] == "register_storage"

def test_unresolved_target_call_argument_evidence_is_not_usable():
    class FakeTracer:
        def __init__(self, ref):
            self.ref = ref

        def _make_pcode_op_ref(self, _op):
            return self.ref

    pcode_ref = PcodeOpRef(address_offset=0x1200, seq_time=3, seq_order=0, mnemonic="CALL")
    evidence_map = {}

    _record_call_argument_evidence(
        evidence_map,
        FakeTracer(pcode_ref),
        object(),
        CallTargetRef.unknown(),
        [{"name": "param_1", "index": 0}],
        [Expression.parameter("param_1", 0, size=4)],
        [],
        coverage_complete=True,
    )

    evidence = evidence_map[pcode_ref.stable_key()]
    assert evidence.is_usable() is False
    assert evidence.coverage_complete is False
    assert evidence.arguments == ()
    assert evidence.reason == "call_target_unresolved"

def test_call_argument_evidence_target_match_requires_resolved_targets():
    evidence = CallArgumentEvidence(
        pcode_op_ref=PcodeOpRef(address_offset=0x1220, seq_time=5, seq_order=0, mnemonic="CALL"),
        target_ref=None,
        callee_param_identities=((("parameter", 0),),),
        arguments=(Expression.parameter("param_1", 0, size=4),),
        sources=("explicit_input",),
        coverage_complete=True,
    )

    assert evidence.is_usable() is False
    assert evidence.target_matches(CallTargetRef.from_name("callee")) is False

    unscoped_external = CallTargetRef.from_name("puts", is_external=True)
    scoped_external = CallTargetRef.from_name("puts", is_external=True, library_name="libc")
    scoped_evidence = CallArgumentEvidence(
        pcode_op_ref=PcodeOpRef(address_offset=0x1224, seq_time=6, seq_order=0, mnemonic="CALL"),
        target_ref=scoped_external,
        callee_param_identities=((("parameter", 0),),),
        arguments=(Expression.parameter("param_1", 0, size=4),),
        sources=("explicit_input",),
        coverage_complete=True,
    )

    assert scoped_evidence.is_usable() is True
    assert scoped_evidence.target_matches(scoped_external) is True
    assert scoped_evidence.target_matches(unscoped_external) is False

    local_name_only_evidence = CallArgumentEvidence(
        pcode_op_ref=PcodeOpRef(address_offset=0x1228, seq_time=7, seq_order=0, mnemonic="CALL"),
        target_ref=CallTargetRef.from_name("a"),
        callee_param_identities=((("parameter", 0),),),
        arguments=(Expression.parameter("param_1", 0, size=4),),
        sources=("explicit_input",),
        coverage_complete=True,
    )

    assert local_name_only_evidence.is_usable() is False
    assert local_name_only_evidence.target_matches(CallTargetRef.from_name("b")) is False

def test_missing_callee_parameter_identity_keeps_call_evidence_incomplete():
    class FakeTracer:
        def __init__(self, ref):
            self.ref = ref

        def _make_pcode_op_ref(self, _op):
            return self.ref

    pcode_ref = PcodeOpRef(address_offset=0x1210, seq_time=4, seq_order=0, mnemonic="CALL")
    evidence_map = {}

    _record_call_argument_evidence(
        evidence_map,
        FakeTracer(pcode_ref),
        object(),
        CallTargetRef.from_name("callee", entry_offset=0x2000),
        [{"name": "param_1"}],
        [Expression.parameter("param_1", 0, size=4)],
        [],
        coverage_complete=True,
    )

    evidence = evidence_map[pcode_ref.stable_key()]
    assert evidence.is_usable() is False
    assert evidence.coverage_complete is False
    assert evidence.arguments == ()
    assert evidence.reason == "callee_parameter_identity_unproven"

def test_recover_call_argument_expressions_prefers_explicit_stack_local_address_over_storage_guess():
    class FakeAddress:
        def __init__(self, offset, space_name="register"):
            self._offset = offset
            self._space_name = space_name

        def getOffset(self):
            return self._offset

        def getAddressSpace(self):
            return self

        def getName(self):
            return self._space_name

    class FakeSeqnum:
        def __init__(self, offset, order):
            self._target = FakeAddress(offset, "ram")
            self._order = order

        def getTarget(self):
            return self._target

        def getOrder(self):
            return self._order

    class FakeVarnode:
        def __init__(self, storage=None, size=8):
            self.storage = storage
            self._size = size

        def getSize(self):
            return self._size

        def getAddress(self):
            if self.storage is None:
                return None
            return FakeAddress(self.storage.offset, self.storage.space_name)

        def getOffset(self):
            return 0 if self.storage is None else self.storage.offset

        def getDef(self):
            return None

        def getHigh(self):
            return None

    class FakeOp:
        def __init__(self, output):
            self._output = output
            self._seqnum = FakeSeqnum(0x1000, 3)

        def getSeqnum(self):
            return self._seqnum

        def getOutput(self):
            return self._output

        def getMnemonic(self):
            return "COPY"

        def getNumInputs(self):
            return 0

    class FakeTracer:
        def __init__(self, ops):
            self._ops = ops

        def get_all_pcode_ops(self):
            return self._ops

        def _get_storage_info_from_varnode(self, varnode):
            return getattr(varnode, "storage", None)

        def trace_varnode(self, _varnode, use_cache=False, depth=0):
            return Expression.variable("opaque", size=8)

    misleading_output = FakeVarnode(StorageInfo(**_reg_storage("a2")), size=8)
    tracer = FakeTracer([FakeOp(misleading_output)])
    call_op = FakeOp(None)
    local_addr = Expression.binary_op(
        "INT_ADD",
        Expression.variable(
            "sp",
            size=8,
            storage_info=StorageInfo(
                is_register=True,
                space_name="register",
                register_name="sp",
                base_register_name="sp",
                size=8,
                size_bits=64,
                base_register_size=8,
                base_register_size_bits=64,
                bit_offset_in_base=0,
            ),
        ),
        Expression.constant(-0x30, 8),
    )

    recovered = _recover_call_argument_expressions(
        call_op,
        tracer,
        [
            _param("param_1", size=4, is_signed=False, index=0),
            _param("param_2", size=4, is_signed=False, index=1),
        ],
        [
            {"name": "param_1", "size": 4, "storage": _reg_storage("a0_lo", size_bytes=4, register_name="a0_lo")},
            {"name": "param_2", "size": 4, "storage": _reg_storage("a1_lo", size_bytes=4, register_name="a1_lo")},
            {"name": "param_3", "size": 8, "storage": _reg_storage("a2")},
        ],
        [
            Expression.parameter("param_1", 0, size=4),
            Expression.parameter("param_2", 1, size=4),
            local_addr,
        ],
    )

    assert recovered[2].to_string() == "(sp + (-48))"

def test_recover_call_argument_expressions_refuses_unresolved_positional_arguments():
    class FakeTracer:
        def get_all_pcode_ops(self):
            return []

    recovered = _recover_call_argument_expressions(
        call_op=object(),
        tracer=FakeTracer(),
        caller_parameters=[
            _param("caller_a", size=8, is_signed=False, index=0),
            _param("caller_b", size=8, is_signed=False, index=1),
        ],
        callee_parameters=[
            {"name": "callee_a", "size": 8},
            {"name": "callee_b", "size": 8},
        ],
        explicit_args=[],
    )

    assert recovered == []

def test_recover_call_argument_expressions_collapses_identical_duplicate_inputs():
    class FakeTracer:
        def get_all_pcode_ops(self):
            return []

    parameter = Expression.parameter("param_1", 0, size=4)
    recovered = _recover_call_argument_expressions(
        call_op=object(),
        tracer=FakeTracer(),
        caller_parameters=[
            _param("param_1", size=4, is_signed=True, index=0),
        ],
        callee_parameters=[
            {"name": "callee_x", "size": 4},
        ],
        explicit_args=[parameter, parameter],
    )

    assert recovered == [parameter]

def test_recover_call_argument_expressions_keeps_distinct_duplicate_slots_ambiguous():
    class FakeCallOp:
        def getNumInputs(self):
            return 0

        def getOutput(self):
            return None

        def getMnemonic(self):
            return "CALL"

    class FakeTracer:
        def get_all_pcode_ops(self):
            return []

    recovered = _recover_call_argument_expressions(
        call_op=FakeCallOp(),
        tracer=FakeTracer(),
        caller_parameters=[
            _param("param_1", size=4, is_signed=True, index=0),
            _param("param_2", size=4, is_signed=True, index=1),
        ],
        callee_parameters=[
            {"name": "callee_x", "size": 4},
        ],
        explicit_args=[
            Expression.parameter("param_1", 0, size=4),
            Expression.parameter("param_2", 1, size=4),
        ],
    )

    assert recovered == []

def test_recover_call_argument_expressions_preserves_explicit_phi_function_pointer():
    class FakeAddress:
        def __init__(self, offset, space_name="ram"):
            self._offset = offset
            self._space_name = space_name

        def getOffset(self):
            return self._offset

        def getAddressSpace(self):
            return self

        def getName(self):
            return self._space_name

    class FakeSeqnum:
        def __init__(self, offset, order):
            self._target = FakeAddress(offset)
            self._order = order

        def getTarget(self):
            return self._target

        def getOrder(self):
            return self._order

    class FakeOp:
        def __init__(self):
            self._seqnum = FakeSeqnum(0x1000, 3)

        def getSeqnum(self):
            return self._seqnum

        def getOutput(self):
            return None

        def getMnemonic(self):
            return "CALL"

        def getNumInputs(self):
            return 0

    class FakeTracer:
        def get_all_pcode_ops(self):
            return []

        def _get_storage_info_from_varnode(self, _varnode):
            return None

        def trace_varnode(self, _varnode, use_cache=False, depth=0):
            return Expression.variable("opaque", size=8)

    call_op = FakeOp()
    explicit_target = Expression.phi(
        [
            (
                Condition(
                    Expression.binary_op(
                        "INT_EQUAL",
                        Expression.parameter("selector", 0, size=4),
                        Expression.constant(0, 4),
                    ),
                    False,
                ),
                Expression.binary_op(
                    "INT_ADD",
                    Expression.constant(0, 8),
                    Expression.constant(0x100814, 8),
                ),
            ),
            (
                Condition(
                    Expression.binary_op(
                        "INT_NOTEQUAL",
                        Expression.parameter("selector", 0, size=4),
                        Expression.constant(0, 4),
                    ),
                    False,
                ),
                Expression.binary_op(
                    "INT_ADD",
                    Expression.constant(0, 8),
                    Expression.constant(0x10081C, 8),
                ),
            ),
        ]
    )

    recovered = _recover_call_argument_expressions(
        call_op,
        FakeTracer(),
        [
            _param("param_1", size=8, is_signed=False, index=0, storage=_reg_storage("x0")),
        ],
        [
            {"name": "param_1", "size": 8, "data_type": "code *", "storage": _reg_storage("x0")},
        ],
        [explicit_target],
    )

    assert len(recovered) == 1
    assert recovered[0].expr_type.name == "PHI"
    assert recovered[0].to_string() == explicit_target.to_string()

def test_recover_call_argument_expressions_refuses_unproven_explicit_subsequence_alignment():
    class FakeAddress:
        def __init__(self, offset, space_name="ram"):
            self._offset = offset
            self._space_name = space_name

        def getOffset(self):
            return self._offset

        def getAddressSpace(self):
            return self

        def getName(self):
            return self._space_name

    class FakeSeqnum:
        def __init__(self, offset, order):
            self._target = FakeAddress(offset)
            self._order = order

        def getTarget(self):
            return self._target

        def getOrder(self):
            return self._order

    class FakeCallOp:
        def __init__(self):
            self._seqnum = FakeSeqnum(0x2000, 10)

        def getSeqnum(self):
            return self._seqnum

        def getOutput(self):
            return None

        def getMnemonic(self):
            return "CALL"

        def getNumInputs(self):
            return 0

    class FakeTracer:
        def get_all_pcode_ops(self):
            return []

        def _get_storage_info_from_varnode(self, _varnode):
            return None

        def trace_varnode(self, _varnode, use_cache=False, depth=0):
            return Expression.variable("opaque", size=4)

    recovered = _recover_call_argument_expressions(
        FakeCallOp(),
        FakeTracer(),
        [
            _param("param_1", size=4, is_signed=False, index=0, storage=_reg_storage("a0", size_bytes=4)),
            _param("param_2", size=4, is_signed=False, index=1, storage=_reg_storage("a1", size_bytes=4)),
            _param("param_3", size=4, is_signed=False, index=2, storage=_reg_storage("a2", size_bytes=4)),
        ],
        [
            _param("lhs", size=4, is_signed=False, index=0, storage=_reg_storage("a0", size_bytes=4)),
            _param("rhs", size=4, is_signed=False, index=1, storage=_reg_storage("a1", size_bytes=4)),
            _param("bias", size=4, is_signed=False, index=2, storage=_reg_storage("a2", size_bytes=4)),
        ],
        [
            Expression.binary_op(
                "INT_SUB",
                Expression.parameter("param_1", 0, size=4),
                Expression.parameter("param_2", 1, size=4),
            ),
            Expression.parameter("param_1", 0, size=4),
            Expression.parameter("param_2", 1, size=4),
            Expression.constant(1, 4),
        ],
    )

    assert recovered == []

def test_recover_call_argument_expressions_aligns_extra_explicit_args_by_call_input_storage():
    class FakeAddress:
        def __init__(self, offset, space_name="ram"):
            self._offset = offset
            self._space_name = space_name

        def getOffset(self):
            return self._offset

        def getAddressSpace(self):
            return self

        def getName(self):
            return self._space_name

    class FakeSeqnum:
        def __init__(self, offset, order):
            self._target = FakeAddress(offset)
            self._order = order

        def getTarget(self):
            return self._target

        def getOrder(self):
            return self._order

    class FakeVarnode:
        def __init__(self, storage):
            self.storage = StorageInfo(**storage)

    class FakeCallOp:
        def __init__(self, inputs):
            self._seqnum = FakeSeqnum(0x2000, 10)
            self._inputs = list(inputs)

        def getSeqnum(self):
            return self._seqnum

        def getOutput(self):
            return None

        def getMnemonic(self):
            return "CALL"

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

    class FakeTracer:
        def get_all_pcode_ops(self):
            return []

        def _get_storage_info_from_varnode(self, varnode):
            return getattr(varnode, "storage", None)

        def trace_varnode(self, _varnode, use_cache=False, depth=0):
            return Expression.variable("opaque", size=4)

    target = FakeVarnode(_reg_storage("target", size_bytes=8))
    input_a0 = FakeVarnode(_reg_storage("a0", size_bytes=4))
    input_a1 = FakeVarnode(_reg_storage("a1", size_bytes=4))
    input_a2 = FakeVarnode(_reg_storage("a2", size_bytes=4))
    input_a3 = FakeVarnode(_reg_storage("a3", size_bytes=4))
    recovered = _recover_call_argument_expressions(
        FakeCallOp([target, input_a0, input_a1, input_a2, input_a3]),
        FakeTracer(),
        [
            _param("param_1", size=4, is_signed=False, index=0, storage=_reg_storage("a0", size_bytes=4)),
            _param("param_2", size=4, is_signed=False, index=1, storage=_reg_storage("a1", size_bytes=4)),
            _param("param_3", size=4, is_signed=False, index=2, storage=_reg_storage("a2", size_bytes=4)),
        ],
        [
            _param("lhs", size=4, is_signed=False, index=0, storage=_reg_storage("a0", size_bytes=4)),
            _param("rhs", size=4, is_signed=False, index=1, storage=_reg_storage("a1", size_bytes=4)),
            _param("bias", size=4, is_signed=False, index=2, storage=_reg_storage("a2", size_bytes=4)),
        ],
        [
            Expression.binary_op(
                "INT_SUB",
                Expression.parameter("param_1", 0, size=4),
                Expression.parameter("param_2", 1, size=4),
            ),
            Expression.parameter("param_1", 0, size=4),
            Expression.parameter("param_2", 1, size=4),
            Expression.constant(1, 4),
        ],
    )

    assert len(recovered) == 3
    assert recovered[0].to_string() == "(param_1 - param_2)"
    assert recovered[1].to_string() == "param_1"
    assert recovered[2].to_string() == "param_2"

def test_recover_call_argument_expressions_rejects_ambiguous_call_input_storage_alignment():
    class FakeAddress:
        def __init__(self, offset, space_name="ram"):
            self._offset = offset
            self._space_name = space_name

        def getOffset(self):
            return self._offset

        def getAddressSpace(self):
            return self

        def getName(self):
            return self._space_name

    class FakeSeqnum:
        def __init__(self, offset, order):
            self._target = FakeAddress(offset)
            self._order = order

        def getTarget(self):
            return self._target

        def getOrder(self):
            return self._order

    class FakeVarnode:
        def __init__(self, storage):
            self.storage = StorageInfo(**storage)

    class FakeCallOp:
        def __init__(self, inputs):
            self._seqnum = FakeSeqnum(0x2000, 10)
            self._inputs = list(inputs)

        def getSeqnum(self):
            return self._seqnum

        def getOutput(self):
            return None

        def getMnemonic(self):
            return "CALL"

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

    class FakeTracer:
        def get_all_pcode_ops(self):
            return []

        def _get_storage_info_from_varnode(self, varnode):
            return getattr(varnode, "storage", None)

        def trace_varnode(self, _varnode, use_cache=False, depth=0):
            return Expression.variable("opaque", size=4)

    target = FakeVarnode(_reg_storage("target", size_bytes=8))
    input_a0_first = FakeVarnode(_reg_storage("a0", size_bytes=4))
    input_a0_second = FakeVarnode(_reg_storage("a0", size_bytes=4))

    recovered = _recover_call_argument_expressions(
        FakeCallOp([target, input_a0_first, input_a0_second]),
        FakeTracer(),
        [
            _param("param_1", size=4, is_signed=False, index=0, storage=_reg_storage("a0", size_bytes=4)),
        ],
        [
            _param("lhs", size=4, is_signed=False, index=0, storage=_reg_storage("a0", size_bytes=4)),
        ],
        [
            Expression.parameter("param_1", 0, size=4),
            Expression.constant(1, 4),
        ],
    )

    assert recovered == []

def test_recover_call_argument_expressions_rejects_tail_with_unproven_immediate_storage():
    class FakeAddress:
        def __init__(self, offset, space_name="ram"):
            self._offset = offset
            self._space_name = space_name

        def getOffset(self):
            return self._offset

        def getAddressSpace(self):
            return self

        def getName(self):
            return self._space_name

    class FakeSeqnum:
        def __init__(self, offset, order):
            self._target = FakeAddress(offset)
            self._order = order

        def getTarget(self):
            return self._target

        def getOrder(self):
            return self._order

    class FakeVarnode:
        def __init__(self, storage=None):
            self.storage = StorageInfo(**storage) if storage is not None else None

    class FakeCallOp:
        def __init__(self, inputs):
            self._seqnum = FakeSeqnum(0x2000, 10)
            self._inputs = list(inputs)

        def getSeqnum(self):
            return self._seqnum

        def getOutput(self):
            return None

        def getMnemonic(self):
            return "CALL"

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

    class FakeTracer:
        def get_all_pcode_ops(self):
            return []

        def _get_storage_info_from_varnode(self, varnode):
            return getattr(varnode, "storage", None)

        def trace_varnode(self, _varnode, use_cache=False, depth=0):
            return Expression.variable("opaque", size=4)

    target = FakeVarnode(_reg_storage("target", size_bytes=8))
    hidden_condition_input = FakeVarnode(_reg_storage("a2", size_bytes=4))
    first_arg = FakeVarnode(_reg_storage("a0", size_bytes=4))
    immediate_arg = FakeVarnode(None)

    recovered = _recover_call_argument_expressions(
        FakeCallOp([target, hidden_condition_input, first_arg, immediate_arg]),
        FakeTracer(),
        [
            _param("param_1", size=4, is_signed=False, index=0, storage=_reg_storage("a0", size_bytes=4)),
            _param("param_3", size=4, is_signed=False, index=2, storage=_reg_storage("a2", size_bytes=4)),
        ],
        [
            _param("value", size=4, is_signed=False, index=0, storage=_reg_storage("a0", size_bytes=4)),
            _param("bias", size=4, is_signed=False, index=1, storage=_reg_storage("a1", size_bytes=4)),
        ],
        [
            Expression.parameter("param_3", 2, size=4),
            Expression.parameter("param_3", 2, size=4),
            Expression.constant(0xFFFFFFFD, 4),
        ],
    )

    assert recovered == []

def test_recover_call_argument_expressions_selects_storage_window_with_const_storage():
    class FakeAddress:
        def __init__(self, offset, space_name="ram"):
            self._offset = offset
            self._space_name = space_name

        def getOffset(self):
            return self._offset

        def getAddressSpace(self):
            return self

        def getName(self):
            return self._space_name

    class FakeSeqnum:
        def __init__(self, offset, order):
            self._target = FakeAddress(offset)
            self._order = order

        def getTarget(self):
            return self._target

        def getOrder(self):
            return self._order

    class FakeVarnode:
        def __init__(self, storage=None):
            self.storage = StorageInfo(**storage) if storage is not None else None

    class FakeCallOp:
        def __init__(self, inputs):
            self._seqnum = FakeSeqnum(0x2000, 10)
            self._inputs = list(inputs)

        def getSeqnum(self):
            return self._seqnum

        def getOutput(self):
            return None

        def getMnemonic(self):
            return "CALL"

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

    class FakeTracer:
        def get_all_pcode_ops(self):
            return []

        def _get_storage_info_from_varnode(self, varnode):
            return getattr(varnode, "storage", None)

        def trace_varnode(self, _varnode, use_cache=False, depth=0):
            return Expression.variable("opaque", size=4)

    target = FakeVarnode(_reg_storage("target", size_bytes=8))
    hidden_condition_input = FakeVarnode(None)
    first_arg = FakeVarnode(_reg_storage("a0", size_bytes=4))
    second_arg = FakeVarnode(_reg_storage("a1", size_bytes=4))
    immediate_arg = FakeVarnode(_const_storage(size_bytes=8))

    recovered = _recover_call_argument_expressions(
        FakeCallOp([target, hidden_condition_input, first_arg, second_arg, immediate_arg]),
        FakeTracer(),
        [
            _param("param_1", size=4, is_signed=False, index=0, storage=_reg_storage("a0", size_bytes=4)),
            _param("param_2", size=4, is_signed=False, index=1, storage=_reg_storage("a1", size_bytes=4)),
        ],
        [
            _param("value", size=4, is_signed=False, index=0, storage=_reg_storage("a0", size_bytes=4)),
            _param("delta", size=4, is_signed=False, index=1, storage=_reg_storage("a1", size_bytes=4)),
            _param("bias", size=4, is_signed=False, index=2, storage=_reg_storage("a2", size_bytes=4)),
        ],
        [
            Expression.binary_op(
                "INT_SUB",
                Expression.parameter("param_1", 0, size=4),
                Expression.parameter("param_2", 1, size=4),
            ),
            Expression.parameter("param_1", 0, size=4),
            Expression.parameter("param_2", 1, size=4),
            Expression.constant(1, 4),
        ],
    )

    assert len(recovered) == 3
    assert [arg.to_string() for arg in recovered] == ["param_1", "param_2", "1"]

def test_recover_call_argument_expressions_selects_fixed_prefix_for_variadic_call():
    class FakeAddress:
        def __init__(self, offset, space_name="ram"):
            self._offset = offset
            self._space_name = space_name

        def getOffset(self):
            return self._offset

        def getAddressSpace(self):
            return self

        def getName(self):
            return self._space_name

    class FakeSeqnum:
        def __init__(self, offset, order):
            self._target = FakeAddress(offset)
            self._order = order

        def getTarget(self):
            return self._target

        def getOrder(self):
            return self._order

    class FakeVarnode:
        def __init__(self, storage=None):
            self.storage = StorageInfo(**storage) if storage is not None else None

    class FakeCallOp:
        def __init__(self, inputs):
            self._seqnum = FakeSeqnum(0x2000, 10)
            self._inputs = list(inputs)

        def getSeqnum(self):
            return self._seqnum

        def getOutput(self):
            return None

        def getMnemonic(self):
            return "CALL"

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

    class FakeTracer:
        def resolve_call_target_ref(self, _target_varnode, **_kwargs):
            return CallTargetRef(kind="function", function_name="printf", display_hint="printf")

        def get_all_pcode_ops(self):
            return []

        def _get_storage_info_from_varnode(self, varnode):
            return getattr(varnode, "storage", None)

        def trace_varnode(self, _varnode, use_cache=False, depth=0):
            return Expression.variable("opaque", size=8)

    recovered = _recover_call_argument_expressions(
        FakeCallOp(
            [
                FakeVarnode(_reg_storage("target", size_bytes=8)),
                FakeVarnode(None),
                FakeVarnode(None),
            ]
        ),
        FakeTracer(),
        [],
        [
            _param(
                "__format",
                size=8,
                is_signed=False,
                index=0,
                data_type="char *",
                storage=_reg_storage("x0", size_bytes=8),
            ),
        ],
        [
            _readonly_format_string_expr(0x1004D0),
            Expression.constant(0x1004F5, 8),
        ],
    )

    assert len(recovered) == 1
    assert recovered[0].to_string() == "1049808"

def test_recover_call_argument_expressions_rejects_fixed_prefix_for_non_variadic_pointer_call():
    class FakeAddress:
        def __init__(self, offset, space_name="ram"):
            self._offset = offset
            self._space_name = space_name

        def getOffset(self):
            return self._offset

        def getAddressSpace(self):
            return self

        def getName(self):
            return self._space_name

    class FakeSeqnum:
        def __init__(self, offset, order):
            self._target = FakeAddress(offset)
            self._order = order

        def getTarget(self):
            return self._target

        def getOrder(self):
            return self._order

    class FakeVarnode:
        def __init__(self, storage=None):
            self.storage = StorageInfo(**storage) if storage is not None else None

    class FakeCallOp:
        def __init__(self, inputs):
            self._seqnum = FakeSeqnum(0x2000, 10)
            self._inputs = list(inputs)

        def getSeqnum(self):
            return self._seqnum

        def getOutput(self):
            return None

        def getMnemonic(self):
            return "CALL"

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

    class FakeTracer:
        def resolve_call_target_ref(self, _target_varnode, **_kwargs):
            return CallTargetRef(
                kind="function",
                function_name="consume_ptr",
                display_hint="consume_ptr",
            )

        def get_all_pcode_ops(self):
            return []

        def _get_storage_info_from_varnode(self, varnode):
            return getattr(varnode, "storage", None)

        def trace_varnode(self, _varnode, use_cache=False, depth=0):
            return Expression.variable("opaque", size=8)

    recovered = _recover_call_argument_expressions(
        FakeCallOp(
            [
                FakeVarnode(_reg_storage("target", size_bytes=8)),
                FakeVarnode(None),
                FakeVarnode(None),
            ]
        ),
        FakeTracer(),
        [],
        [
            _param(
                "ptr",
                size=8,
                is_signed=False,
                index=0,
                data_type="char *",
                storage=_reg_storage("x0", size_bytes=8),
            ),
        ],
        [
            Expression.constant(0x1004D0, 8),
            Expression.constant(0x1004F5, 8),
        ],
    )

    assert recovered == []

import pytest

from scripts.function_tracer_pcode.equivalence.cause_identity import (
    ProofRequirementContract,
    ProofRequirementId,
    RelationalCauseKey,
)
from scripts.function_tracer_pcode.equivalence.unknown_reason import make_unknown_reason
from scripts.function_tracer_pcode.equivalence.checker import EquivalenceChecker
from scripts.function_tracer_pcode.equivalence.result import EquivalenceResult
from scripts.function_tracer_pcode.smt import ParallelResult
from scripts.function_tracer_pcode.validation.root_blocker_summary import (
    AggregationSnapshot,
    summarize_root_blockers,
    compare_root_blocker_summaries,
)


def _requirement():
    return ProofRequirementId.create(
        "call_effect_summary_proof",
        ("callsite", "left", "right"),
        ProofRequirementContract(
            "equal observable call effects",
            observation_surface=("return", "memory:global"),
        ),
    )


def _typed_cause():
    return RelationalCauseKey(
        cause_kind="call_effect_relation",
        comparison_domain=("left-sha", "right-sha", "abi-v1"),
        left_semantic_object=("pcode_op", 0x1000, 7, "CALL"),
        right_semantic_object=("pcode_op", 0x2000, 9, "CALL"),
        correspondence_contract=("callee", "arg-storage", "observable-effect"),
    )


def _reason(reason_id, *, status="pending_proof"):
    return make_unknown_reason(
        reason_id,
        decision_effect="blocks_equivalence",
        object_target_key=("legacy-call", "left", "right"),
        proof_obligation_id=(reason_id, "stage", "call-proof", "evidence", ("legacy-call",)),
        typed_cause_key=_typed_cause().to_dict(),
        proof_requirement_ids=(_requirement().to_dict(),),
        action_status=status,
    ).to_dict()


def _attempt(attempt_id, reasons, *, transition="UNKNOWN", statuses=None):
    identity = {
        "trace_schema_version": 1,
        "strategy_identity": "pairwise",
        "attempt_ordinal": attempt_id,
    }
    occurrences = []
    for ordinal, reason in enumerate(reasons):
        occurrences.append(
            {
                "occurrence_id": {
                    "occurrence_schema_version": 1,
                    "attempt_identity": identity,
                    "reason_ordinal": ordinal,
                },
                "attempt_identity": identity,
                "reason_record": reason,
                "initial_causal_status": (statuses or {}).get(
                    ordinal, "active_final_blocker"
                ),
            }
        )
    return {
        "attempt_id": attempt_id,
        "strategy": "pairwise",
        "result": None,
        "transition_reason": transition,
        "unknown_reasons": reasons,
        "reason_occurrences": occurrences,
    }


def _attempt_identity(ordinal):
    return {
        "trace_schema_version": 1,
        "strategy_identity": "pairwise",
        "attempt_ordinal": ordinal,
    }


def _payload(*, run="run-1", result=None, attempts=None, case="f", with_content=True):
    payload = {
        "is_equivalent": result,
        "case_id": case,
        "function1_name": case,
        "function2_name": case,
        "function1_identity": ("function", "left", case, 0x1000, "sig-left"),
        "function2_identity": ("function", "right", case, 0x2000, "sig-right"),
        "run_identity": run,
        "artifact_identity": (run, case),
        "debug_trace": {
            "final_result": result,
            "attempts": attempts or [],
            "causal_transitions": [],
            "proof_completion_events": [],
            "reason_completion_events": [],
        },
    }
    if with_content:
        payload["binary1_content_identity"] = ("sha256", "left")
        payload["binary2_content_identity"] = ("sha256", "right")
    return payload


def test_reason_scoped_legacy_ids_collapse_to_one_unique_proof_requirement():
    payload = _payload(
        attempts=[
            _attempt(
                0,
                [_reason("unresolved_expression"), _reason("equivalence_blocking_unsafety")],
            )
        ]
    )

    summary = summarize_root_blockers([payload])

    assert summary.active_root_blocker_count == 1
    blocker = summary.active_root_blockers[0]
    assert len(blocker.legacy_proof_obligation_ids) == 2
    assert len(blocker.required_proof_ids) == 1
    assert summary.required_unique_proof_count == 1


def test_proof_requirement_alone_cannot_discharge_occurrence():
    attempt = _attempt(0, [_reason("unresolved_expression")])
    target = attempt["reason_occurrences"][0]["occurrence_id"]
    payload = _payload(attempts=[attempt])
    payload["debug_trace"]["causal_transitions"] = [
        {
            "transition_id": ("bad-discharge",),
            "target_occurrence_id": target,
            "transition_kind": "discharged",
            "cause_kind": "proof_requirement",
            "cause_ref": _requirement().to_dict(),
            "emitted_at_attempt": _attempt_identity(1),
        }
    ]

    summary = summarize_root_blockers([payload])

    assert summary.active_root_blocker_count == 1
    assert summary.diagnostics["dangling_transition_cause"] == 1


def test_legacy_proof_completion_transition_cannot_discharge_occurrence():
    attempt = _attempt(
        0,
        [_reason("unresolved_expression"), _reason("sat_unsafety")],
    )
    target = attempt["reason_occurrences"][0]["occurrence_id"]
    payload = _payload(attempts=[attempt])
    payload["debug_trace"]["proof_completion_events"] = [
        {
            "completion_id": ("proof", 1),
            "proof_requirement_id": _requirement().to_dict(),
            "proof_artifact_ref": ("proof-artifact", "sha256"),
            "proof_status": "proven",
            "completed_at_attempt": _attempt_identity(1),
        }
    ]
    payload["debug_trace"]["causal_transitions"] = [
        {
            "transition_id": ("discharge", 1),
            "target_occurrence_id": target,
            "transition_kind": "discharged",
            "cause_kind": "proof_completion",
            "cause_ref": ("proof", 1),
            "emitted_at_attempt": _attempt_identity(1),
        }
    ]

    summary = summarize_root_blockers([payload])

    assert summary.active_root_blocker_count == 1
    assert len(summary.active_root_blockers[0].observed_occurrence_ids) == 2
    assert len(summary.observed_candidate_blockers[0].observed_occurrence_ids) == 2
    assert summary.diagnostics["dangling_transition_cause"] == 1


def test_applicable_reason_completion_discharges_exact_occurrence_without_transition():
    attempt = _attempt(0, [_reason("unresolved_expression")])
    target = attempt["reason_occurrences"][0]["occurrence_id"]
    payload = _payload(attempts=[attempt])
    payload["debug_trace"]["reason_completion_events"] = [{
        "completion_event_id": ("reason-completion", 1),
        "completed_occurrence_id": target,
        "exact_target_id": ("legacy-call", "left", "right"),
        "exact_missing_fact_or_proof_slot": "call_effect_summary_proof",
        "source_snapshot_fingerprint": "snapshot-sha",
        "semantic_seed_or_premise_digest": "premise-sha",
        "evidence_or_artifact_digest": "artifact-sha",
        "recognizing_stage": "call_effect_preflight",
        "completed_at_attempt": _attempt_identity(1),
        "applicability_status": "APPLICABLE",
    }]

    summary = summarize_root_blockers([payload])

    assert summary.active_root_blocker_count == 0
    assert summary.candidate_root_blocker_count == 1


def test_stale_reason_completion_remains_diagnostic_and_does_not_discharge():
    attempt = _attempt(0, [_reason("unresolved_expression")])
    target = attempt["reason_occurrences"][0]["occurrence_id"]
    payload = _payload(attempts=[attempt])
    payload["debug_trace"]["reason_completion_events"] = [{
        "completion_event_id": ("reason-completion", 2),
        "completed_occurrence_id": target,
        "exact_target_id": ("legacy-call", "left", "right"),
        "exact_missing_fact_or_proof_slot": "call_effect_summary_proof",
        "source_snapshot_fingerprint": "old-snapshot",
        "semantic_seed_or_premise_digest": "premise-sha",
        "evidence_or_artifact_digest": "artifact-sha",
        "recognizing_stage": "call_effect_preflight",
        "completed_at_attempt": _attempt_identity(1),
        "applicability_status": "STALE_SNAPSHOT",
    }]

    summary = summarize_root_blockers([payload])

    assert summary.active_root_blocker_count == 1
    assert summary.diagnostics["inapplicable_reason_completion"] == 1


def test_mixed_runs_require_explicit_snapshot_selection():
    unknown = _payload(run="old", attempts=[_attempt(0, [_reason("unresolved_expression")])])
    equivalent = _payload(run="new", result=True, attempts=[])

    ambiguous = summarize_root_blockers([unknown, equivalent])
    assert ambiguous.active_root_blocker_count == 0
    assert ambiguous.diagnostics["duplicate_current_result_occurrence"] == 1

    selected = summarize_root_blockers(
        [unknown, equivalent],
        snapshot=AggregationSnapshot(
            "new",
            selected_result_occurrences=((
                ("run_identity", ("new",)),
                ("artifact_identity", (("new", "f"),)),
                ("source_path", None),
                ("observed_at", None),
            ),),
        ),
    )
    assert selected.active_root_blocker_count == 0


def test_missing_status_is_inferred_but_not_reported_as_explicit():
    attempt = _attempt(0, [_reason("unresolved_expression")], statuses={0: "unclassified"})
    summary = summarize_root_blockers([_payload(attempts=[attempt])])

    assert summary.active_root_blocker_count == 1
    assert summary.active_root_blockers[0].causal_certainties == ("inferred_final_attempt",)
    assert summary.coverage["explicit_causal_status_coverage"] == 0.0


def test_legacy_pair_count_hint_does_not_create_case_pairs():
    reason = make_unknown_reason(
        "solver_unknown_timeout",
        decision_effect="retryable",
        object_target_key=(
            "solver_timeout",
            ("pair", "B10_B11"),
            ("stage", "pairwise"),
            ("query_hash", "query-sha"),
            ("timeout_budget_seconds", 10),
            ("solver_options", ("solver", "Z3"), ("timeout_seconds", 10)),
            ("left", ("function_ref", "B10", 0x1000)),
            ("right", ("function_ref", "B11", 0x2000)),
        ),
    ).to_dict()
    payload = _payload(attempts=[_attempt(0, [reason])])
    payload["pairwise_stats"] = {"unknown_pairs": 31, "total_pairs": 140}

    summary = summarize_root_blockers([payload])

    assert summary.active_root_blockers[0].affected_case_pairs == ()
    assert summary.aggregate_pair_count_hints == ("unknown 31 / total 140",)


def test_non_forward_transition_does_not_hide_blocker():
    attempt = _attempt(
        0,
        [_reason("unresolved_expression"), _reason("sat_unsafety")],
    )
    first = attempt["reason_occurrences"][0]["occurrence_id"]
    second = attempt["reason_occurrences"][1]["occurrence_id"]
    payload = _payload(attempts=[attempt])
    payload["debug_trace"]["causal_transitions"] = [
        {
            "transition_id": ("backward",),
            "target_occurrence_id": first,
            "transition_kind": "superseded",
            "cause_kind": "reason_occurrence",
            "cause_ref": second,
            "emitted_at_attempt": _attempt_identity(0),
        }
    ]

    summary = summarize_root_blockers([payload])

    assert summary.active_root_blocker_count == 1
    assert summary.diagnostics["non_forward_causal_transition"] == 1


def test_supersession_cycle_does_not_hide_blockers():
    attempt = _attempt(
        0,
        [_reason("unresolved_expression"), _reason("sat_unsafety")],
    )
    first = attempt["reason_occurrences"][0]["occurrence_id"]
    second = attempt["reason_occurrences"][1]["occurrence_id"]
    payload = _payload(attempts=[attempt])
    payload["debug_trace"]["causal_transitions"] = [
        {
            "transition_id": ("cycle", 1),
            "target_occurrence_id": first,
            "transition_kind": "superseded",
            "cause_kind": "reason_occurrence",
            "cause_ref": second,
            "emitted_at_attempt": _attempt_identity(1),
        },
        {
            "transition_id": ("cycle", 2),
            "target_occurrence_id": second,
            "transition_kind": "superseded",
            "cause_kind": "reason_occurrence",
            "cause_ref": first,
            "emitted_at_attempt": _attempt_identity(1),
        },
    ]

    summary = summarize_root_blockers([payload])

    assert summary.active_root_blocker_count == 1
    assert summary.diagnostics["causal_transition_cycle"] == 2


def test_missing_content_identity_is_not_promoted_from_binary_name():
    first = _payload(
        run="one",
        attempts=[_attempt(0, [_reason("unresolved_expression")])],
        with_content=False,
    )
    second = _payload(
        run="two",
        attempts=[_attempt(0, [_reason("unresolved_expression")])],
        with_content=False,
    )
    first.update(binary1_name="same", binary2_name="same")
    second.update(binary1_name="same", binary2_name="same")

    summary = summarize_root_blockers([first, second])

    assert summary.active_root_blocker_count == 0
    assert summary.diagnostics["missing_binary_content_identity"] == 2
    assert summary.diagnostics["missing_comparison_domain_identity"] == 2
    assert compare_root_blocker_summaries(summary, summary).persisting_blocker_ids == ()


def test_explicit_active_final_blocker_from_earlier_attempt_is_not_active():
    earlier = _reason("unresolved_expression")
    final = _reason("sat_unsafety")
    final["typed_cause_key"] = {
        **final["typed_cause_key"],
        "cause_kind": "different_final_cause",
    }
    payload = _payload(attempts=[_attempt(0, [earlier]), _attempt(1, [final])])

    summary = summarize_root_blockers([payload])

    assert summary.active_root_blocker_count == 1
    assert summary.active_root_blockers[0].blocker_id.cause_kind == "different_final_cause"
    assert summary.candidate_root_blocker_count == 2


def test_invalid_explicit_proof_requirement_marks_count_incomplete():
    reason = _reason("unresolved_expression")
    reason["proof_requirement_ids"] = [
        {"schema_version": 999, "proof_kind": "call_effect_summary_proof"}
    ]
    summary = summarize_root_blockers([_payload(attempts=[_attempt(0, [reason])])])

    assert summary.active_root_blocker_count == 1
    assert summary.active_root_blockers[0].proof_requirements_complete is False
    assert summary.required_unique_proof_count is None
    assert summary.diagnostics["unknown_proof_requirement_schema"] == 1


def test_error_payload_is_not_an_active_unknown_result():
    payload = _payload(attempts=[_attempt(0, [_reason("unresolved_expression")])])
    payload["error_message"] = "decompilation failed"
    payload["debug_trace"]["error_message"] = "decompilation failed"
    payload["debug_trace"]["attempts"][-1]["transition_reason"] = "critical_error"

    summary = summarize_root_blockers([payload])

    assert summary.active_root_blocker_count == 0
    assert summary.candidate_root_blocker_count == 1


def test_unknown_typed_cause_schema_has_specific_diagnostic():
    reason = _reason("unresolved_expression")
    reason["typed_cause_key"] = {**reason["typed_cause_key"], "schema_version": 999}

    summary = summarize_root_blockers([_payload(attempts=[_attempt(0, [reason])])])

    assert summary.active_root_blocker_count == 0
    assert summary.diagnostics["unknown_typed_cause_schema"] == 1


def test_retired_call_effect_umbrella_is_not_promoted_to_typed_identity():
    reason = make_unknown_reason(
        "equivalence_blocking_unsafety",
        evidence_refs=("function1:callsite",),
        recovery_proof_kind="call_effect_summary_proof",
        object_target_key=("call_argument_evidence", "function1", ("pcode_op", "B10", 7)),
        action_status="pending_proof",
    )
    manifest = {
        "proof_stage_backlog": [
            {"obligation_id": "obl-1", "primary_proof_stage": "argument_relation"}
        ],
        "legacy_blocker_mapping": [
            {
                "legacy_blocker": "function1:callsite",
                "mapping_basis": "callsite_pcode_ref",
                "mapping_status": "mapped",
                "obligation_ids": ["obl-1"],
            }
        ],
        "coupling": {"coupling_id": "coupling-sha"},
        "observation_contract": {"contract_id": "observation-sha"},
    }

    specialized = EquivalenceChecker._specialize_call_effect_unknown_reasons(
        [reason],
        manifest,
        comparison_identity={
            "left_binary_content_identity": ("sha256", "left"),
            "right_binary_content_identity": ("sha256", "right"),
            "architecture_identity": ("mips64",),
            "abi_identity": ("n64",),
            "function_identity": ("left-f", "right-f"),
            "signature_storage_contract": ("sig-left", "sig-right"),
            "calling_convention_fingerprint": ("default", "default"),
            "comparison_policy_fingerprint": ("policy-v1",),
        },
    )[0]

    assert specialized.typed_cause_key is None
    assert specialized.proof_requirement_ids == ()


def test_call_effect_specialization_refuses_typed_identity_without_content_hashes():
    reason = make_unknown_reason(
        "equivalence_blocking_unsafety",
        evidence_refs=("function1:callsite",),
        recovery_proof_kind="call_effect_summary_proof",
        object_target_key=("call_argument_evidence", "function1", ("pcode_op", "B10", 7)),
    )
    manifest = {
        "proof_stage_backlog": [
            {"obligation_id": "obl-1", "primary_proof_stage": "argument_relation"}
        ],
        "legacy_blocker_mapping": [
            {
                "legacy_blocker": "function1:callsite",
                "mapping_basis": "callsite_pcode_ref",
                "mapping_status": "mapped",
                "obligation_ids": ["obl-1"],
            }
        ],
    }

    specialized = EquivalenceChecker._specialize_call_effect_unknown_reasons(
        [reason], manifest, comparison_identity={}
    )[0]

    assert specialized.typed_cause_key is None
    assert specialized.proof_requirement_ids == ()


def test_retired_call_effect_umbrella_does_not_gain_content_derived_identity():
    reason = make_unknown_reason(
        "equivalence_blocking_unsafety",
        evidence_refs=("function1:callsite",),
        recovery_proof_kind="call_effect_summary_proof",
        object_target_key=("call_argument_evidence", "function1", ("pcode_op", "B10", 7)),
    )
    manifest = {
        "proof_stage_backlog": [
            {"obligation_id": "obl-1", "primary_proof_stage": "argument_relation"}
        ],
        "legacy_blocker_mapping": [
            {
                "legacy_blocker": "function1:callsite",
                "mapping_basis": "callsite_pcode_ref",
                "mapping_status": "mapped",
                "obligation_ids": ["obl-1"],
            }
        ],
        "coupling": {"coupling_id": "same-shape"},
        "observation_contract": {"contract_id": "same-contract"},
    }
    base = {
        "left_binary_content_identity": ("sha256", "left"),
        "architecture_identity": ("mips64",),
        "abi_identity": ("n64",),
        "function_identity": ("left-f", "right-f"),
        "signature_storage_contract": ("sig-left", "sig-right"),
        "calling_convention_fingerprint": ("default", "default"),
        "comparison_policy_fingerprint": ("policy-v1",),
    }
    first = EquivalenceChecker._specialize_call_effect_unknown_reasons(
        [reason], manifest, comparison_identity={**base, "right_binary_content_identity": ("sha256", "right-a")}
    )[0]
    second = EquivalenceChecker._specialize_call_effect_unknown_reasons(
        [reason], manifest, comparison_identity={**base, "right_binary_content_identity": ("sha256", "right-b")}
    )[0]

    assert first.typed_cause_key is None
    assert second.typed_cause_key is None
    assert first.proof_requirement_ids == second.proof_requirement_ids == ()


def test_registered_legacy_unary_cause_is_not_split_by_peer_domain():
    reason = make_unknown_reason(
        "return_coverage_gap",
        decision_effect="blocks_equivalence",
        object_target_key=(
            "return_coverage",
            ("target_schema_version", 3),
            "function1",
            (
                "function_identity",
                ("binary_identity", ("content", "left-sha")),
                ("function_name", "f"),
                ("entry_offset", 0x1000),
            ),
            "return_coverage_gap",
            ("return_storage", "return_value", 32),
            ("return_partition_identity", "partition-sha"),
            ("guard_disjunction_identity", "guards-sha"),
        ),
    ).to_dict()
    first = _payload(case="f", attempts=[_attempt(0, [reason])])
    second = _payload(case="f", attempts=[_attempt(0, [reason])])
    second["binary2_content_identity"] = ("sha256", "different-peer")

    summary = summarize_root_blockers([first, second])

    assert summary.active_root_blocker_count == 1
    assert len(summary.active_root_blockers[0].affected_unknown_results) == 2
    assert summary.required_unique_proof_count == 2


def test_unary_return_coverage_is_side_invariant():
    def coverage_reason(side):
        return make_unknown_reason(
            "return_coverage_gap",
            decision_effect="blocks_equivalence",
            object_target_key=(
                "return_coverage",
                ("target_schema_version", 3),
                side,
                (
                    "function_identity",
                    ("binary_identity", ("content", "same-function-binary")),
                    ("function_name", "f"),
                    ("entry_offset", 0x1000),
                ),
                "return_coverage_gap",
                ("return_storage", "return_value", 32),
                ("return_partition_identity", "partition-sha"),
                ("guard_disjunction_identity", "guards-sha"),
            ),
        ).to_dict()

    first = _payload(case="f", attempts=[_attempt(0, [coverage_reason("function1")])])
    first["binary1_content_identity"] = ("sha256", "same-function-binary")
    second = _payload(case="f", attempts=[_attempt(0, [coverage_reason("function2")])])
    second["binary1_content_identity"] = ("sha256", "peer-c")
    second["binary2_content_identity"] = ("sha256", "same-function-binary")
    second["function1_identity"] = ("function", "peer-c", "g", 0x3000)
    second["function2_identity"] = first["function1_identity"]

    summary = summarize_root_blockers([first, second])

    assert summary.active_root_blocker_count == 1
    assert summary.required_unique_proof_count == 2


def test_unary_call_evidence_is_side_invariant():
    def call_reason(side):
        return make_unknown_reason(
            "equivalence_blocking_unsafety",
            decision_effect="blocks_equivalence",
            recovery_proof_kind="call_effect_summary_proof",
            object_target_key=(
                "call_argument_evidence",
                side,
                ("function_ref", ("function", "same-binary", 0x1000)),
                ("pcode_op", "same-binary", 0x1010, 7, "CALL"),
                ("function", "same-binary", 0x2000),
                (("argument", 0, ("register", "a0", 8)),),
            ),
        ).to_dict()

    first = _payload(attempts=[_attempt(0, [call_reason("function1")])])
    second = _payload(attempts=[_attempt(0, [call_reason("function2")])])
    second["binary1_content_identity"] = ("sha256", "different-peer")
    second["binary2_content_identity"] = first["binary1_content_identity"]

    summary = summarize_root_blockers([first, second])

    assert summary.active_root_blocker_count == 1


def test_unary_call_evidence_distinguishes_local_binary_content():
    reason = make_unknown_reason(
        "equivalence_blocking_unsafety",
        decision_effect="blocks_equivalence",
        recovery_proof_kind="call_effect_summary_proof",
        object_target_key=(
            "call_argument_evidence",
            "function1",
            ("function_ref", ("function", "B10", 0x1000)),
            ("pcode_op", "B10", 0x1010, 7, "CALL"),
            ("function", "B10", 0x2000),
            (("argument", 0, ("register", "a0", 8)),),
        ),
    ).to_dict()
    first = _payload(attempts=[_attempt(0, [reason])])
    second = _payload(attempts=[_attempt(0, [reason])])
    second["binary1_content_identity"] = ("sha256", "different-local-content")

    summary = summarize_root_blockers([first, second])

    assert summary.active_root_blocker_count == 2
    assert summary.required_unique_proof_count == 2


def test_truncated_registered_legacy_schema_is_rejected():
    reason = make_unknown_reason(
        "return_coverage_gap",
        decision_effect="blocks_equivalence",
        object_target_key=("return_coverage", "gap"),
    ).to_dict()

    summary = summarize_root_blockers([_payload(attempts=[_attempt(0, [reason])])])

    assert summary.active_root_blocker_count == 0
    assert summary.diagnostics["legacy_cause_schema_invalid"] == 1


def test_trailing_no_changes_keeps_last_unknown_attempt_active():
    unknown = _attempt(0, [_reason("unresolved_expression")])
    no_changes = _attempt(1, [], transition="no_changes")

    summary = summarize_root_blockers([_payload(attempts=[unknown, no_changes])])

    assert summary.active_root_blocker_count == 1


def test_same_function_names_with_different_object_identities_do_not_collide():
    first = _payload(attempts=[_attempt(0, [_reason("unresolved_expression")])])
    second = _payload(attempts=[_attempt(0, [_reason("unresolved_expression")])])
    second["function1_identity"] = ("function", "left", "f", 0x3000, "other-sig")

    summary = summarize_root_blockers([first, second])

    assert summary.diagnostics.get("duplicate_current_result_occurrence", 0) == 0
    assert len(summary.active_root_blockers[0].affected_unknown_results) == 2


def test_missing_function_identity_is_not_replaced_by_display_name():
    payload = _payload(attempts=[_attempt(0, [_reason("unresolved_expression")])])
    payload.pop("function1_identity")

    summary = summarize_root_blockers([payload])

    assert summary.active_root_blocker_count == 0
    assert summary.diagnostics["missing_function_identity"] == 1


def test_check_from_binaries_preserves_supplied_content_identities(monkeypatch):
    import scripts.function_tracer_pcode.equivalence.checker as checker_module

    result = EquivalenceResult(
        is_equivalent=None,
        function1_name="f",
        function2_name="f",
        binary1_name="left",
        binary2_name="right",
        solver_results=ParallelResult(results=[]),
    )
    monkeypatch.setattr(checker_module, "run_check_from_binaries", lambda *args, **kwargs: result)
    checker = object.__new__(EquivalenceChecker)

    returned = checker.check_from_binaries(
        object(),
        object(),
        "f",
        "f",
        binary1_content_identity=("sha256", "left-sha"),
        binary2_content_identity=("sha256", "right-sha"),
    )

    assert returned.binary1_content_identity == ("sha256", "left-sha")
    assert returned.binary2_content_identity == ("sha256", "right-sha")
    assert returned.to_dict()["binary1_content_identity"] == ("sha256", "left-sha")


@pytest.mark.parametrize(
    ("reason_id", "expects_typed_identity"),
    [
        ("unresolved_expression", False),
        ("unresolved_value_expression", True),
        ("sat_unsafety", False),
        ("sat_counterexample_ambiguous", True),
        ("method_b_closure_blocked", False),
        ("loop_summary_proof_missing", False),
        ("phi_circular_replacement_unproven", True),
        ("outcome_partition_unknown", False),
        ("summary_precondition_incomplete", True),
    ],
)
def test_only_exact_reason_families_receive_typed_legacy_identity(
    reason_id, expects_typed_identity,
):
    reason = make_unknown_reason(
        reason_id,
        object_target_key=("semantic_blocker", ("pair", "B10_B11"), ("object", "stable-key")),
    )
    comparison = {
        "left_binary_content_identity": ("sha256", "left"),
        "right_binary_content_identity": ("sha256", "right"),
        "function_identity": (("left_function_identity", ("function", "left", 0x1000)), ("right_function_identity", ("function", "right", 0x2000))),
        "architecture_identity": ("mips64",),
        "abi_identity": ("n64",),
        "signature_storage_contract": ("left-sig", "right-sig"),
        "calling_convention_fingerprint": ("default", "default"),
        "comparison_policy_fingerprint": ("policy",),
    }

    enriched = EquivalenceChecker._attach_root_blocker_identities(
        [reason], comparison
    )[0]

    assert (enriched.typed_cause_key is not None) is expects_typed_identity
    if expects_typed_identity:
        assert enriched.proof_requirement_ids or enriched.recovery_proof_kind == "none"
    else:
        assert enriched.proof_requirement_ids == ()

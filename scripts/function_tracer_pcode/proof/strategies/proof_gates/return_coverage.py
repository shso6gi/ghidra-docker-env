"""Stateless method implementations extracted from ``scripts.function_tracer_pcode.proof.strategies.base``."""

from __future__ import annotations

from typing import Any, Dict, List, Mapping, Optional, Sequence, Set, Tuple
import hashlib
from scripts.function_tracer_pcode.core import Condition, Expression, FunctionReturnAnalysis
from scripts.function_tracer_pcode.core.render_smt import expression_smt_bit_width
from scripts.function_tracer_pcode.proof.strategies.proof_gates._shared import (
    ConditionSMTOracle,
    ReturnCoverageCheckResult,
    UnknownReasonId,
    UnknownReasonRecord,
    UnknownRecoveryActionStatus,
    UnknownRecoveryProofKind,
    build_proof_obligation_id,
    build_unknown_recovery_actions,
    coerce_value_to_bitvec_width,
    make_unknown_reason,
)
from scripts.function_tracer_pcode.proof.obligations import (
    SnapshotFingerprintCodec,
    UnaryPartitionProofResult,
    UnaryProducerResult,
    prove_unary_partition,
)


def _unary_header_context(base_ctx: Mapping[str, Any]) -> Mapping[str, Any]:
    """Keep declarations/definitions but exclude pair-derived assertions."""
    header = []
    for line in (base_ctx.get("header_lines", ()) if isinstance(base_ctx, Mapping) else ()) or ():
        stripped = str(line).lstrip()
        if stripped.startswith(("(declare-", "(define-", "(set-logic", "(set-option")):
            header.append(str(line))
    return {"header_lines": header}


def _unary_outcome_regions(seed: Any, kind: str) -> Tuple[Any, ...]:
    kinds = {
        tuple(item.candidate_id): str(item.terminal_kind_candidate)
        for item in (getattr(seed, "terminal_candidates", ()) or ())
    }
    return tuple(
        region for region in (getattr(seed, "symbolic_regions", ()) or ())
        if kinds.get(tuple(region.terminal_candidate_id)) == kind
    )


def _unary_solver_status(self, ctx: Mapping[str, Any], assertions: Sequence[str], title: str) -> str:
    header_lines = list(ctx.get("header_lines", ()) or ())
    if not header_lines or not assertions:
        return "unknown"
    normalized = self._normalize_zero_constant_widths_for_declared_symbols(assertions, header_lines)
    query = "\n".join((
        f"; {title}", *header_lines,
        *(f"(assert {assertion})" for assertion in normalized),
        "(check-sat)", "(get-model)",
    ))
    result = self.solver_runner.run_sequential(query)
    from scripts.function_tracer_pcode.authority.domains.return_outcome import (
        capture_active_outcome_solver_result,
    )

    capture_active_outcome_solver_result(
        query=query,
        parallel_result=result,
        configured_timeout_ms=(
            int(getattr(self.solver_runner, "timeout", 0) or 0) * 1000 or None
        ),
    )
    if result.is_equivalent is True:
        return "unsat"
    if result.is_equivalent is False:
        return "sat"
    raw_statuses = {
        str(getattr(getattr(item, "status", None), "name", "")).lower()
        for item in (getattr(result, "results", ()) or ())
    }
    # ParallelResult intentionally exposes only the decisive SAT/UNSAT view.
    # Timeout is execution authority on each raw SolverResult and must not be
    # reconstructed from an absent aggregate error string.
    return "timeout" if "timeout" in raw_statuses else "unknown"


def _unary_blocker_reason_id(blocker: str):
    text = str(blocker or "")
    # Issue #131: 切り捨てで止まった stage は、stage 名より原因の方が具体的なので
    # 専用 reason を先に返す（``path_region`` の一般 blocker へ丸めない）。
    if "case_budget_exceeded" in text:
        return UnknownReasonId.EXPANSION_CASE_BUDGET_EXCEEDED
    if "cfg_reachability" in text:
        return UnknownReasonId.OUTCOME_CFG_REACHABILITY_INCOMPLETE
    if "path_region" in text:
        return UnknownReasonId.OUTCOME_PATH_REGION_INCOMPLETE
    if "member_classification" in text:
        return UnknownReasonId.OUTCOME_MEMBER_UNCLASSIFIED
    if "same_kind_consistency_conflict" in text:
        return UnknownReasonId.OUTCOME_RETURN_VALUE_CONFLICT
    if "same_kind_consistency" in text:
        return UnknownReasonId.OUTCOME_RETURN_CONSISTENCY_UNKNOWN
    if "cross_kind" in text:
        return UnknownReasonId.OUTCOME_CROSS_KIND_OVERLAP
    if "residual_totality_residual_sat" in text:
        return UnknownReasonId.OUTCOME_PARTITION_RESIDUAL_SAT
    if "residual_totality_timeout" in text:
        return UnknownReasonId.OUTCOME_PARTITION_TOTALITY_TIMEOUT
    return "outcome_partition_completion_unproven"


def _reason_id_value(reason_id: Any) -> str:
    """Return the stable identifier for legacy enums and typed-v2 strings."""
    return str(getattr(reason_id, "value", reason_id))


def _prove_unary_outcome_for_analysis(
    self,
    base_ctx: Mapping[str, Any],
    analysis: FunctionReturnAnalysis,
    replace_fn,
):
    seed = getattr(analysis, "outcome_seed", None)
    runtime = getattr(self, "_obligation_runtime_session", None)
    if seed is None or runtime is None:
        return None
    unary_ctx = _unary_header_context(base_ctx)
    return_regions = _unary_outcome_regions(seed, "return")
    divergence_regions = _unary_outcome_regions(seed, "must_diverge")
    unknown_regions = _unary_outcome_regions(seed, "unknown")
    termination_kinds = {
        "exceptional_termination", "process_termination", "nonlocal_control_transfer"
    }
    termination_regions = tuple(
        region for kind in termination_kinds for region in _unary_outcome_regions(seed, kind)
    )
    terminals = tuple(getattr(seed, "terminal_candidates", ()) or ())
    profile = getattr(getattr(analysis, "effect_summary", None), "function_control_effect_profile", None)

    validated_termination_state = {"contracts": None, "artifact_keys": ()}
    validated_cfg_state = {"acyclic": False, "adjacency": ()}

    def _termination_tuple_schema(contract, terminal_kind):
        payload = tuple(contract.payload_key)
        effect = tuple(contract.effect_key)
        observation = tuple(contract.observation_contract_key)
        if terminal_kind != "process_termination" or contract.termination_class != "process":
            return False
        expected_flags = {
            ("atexit_handlers", False),
            ("quick_exit_handlers", False),
            ("stdio_flush", False),
            ("automatic_object_cleanup", False),
        }
        return bool(
            len(payload) == 4
            and payload[:2] == ("process_exit_payload_v1", "immediate_process_exit")
            and isinstance(payload[2], tuple)
            and payload[2][:1] == ("termination_callee_contract_v1",)
            and effect[:3] == (
                "termination_effect_v2", "process", "immediate_process_exit"
            )
            and set(effect[3:]) == expected_flags
            and observation == (
                "termination_observation_v2", "process",
                ("process_exit_status", True),
                ("pretermination_memory_effects", "compared_separately"),
            )
        )

    def termination_classification():
        terminal_by_id = {
            tuple(item.candidate_id): item for item in terminals
            if str(item.terminal_kind_candidate) in termination_kinds
        }
        contracts = []
        producer_evidence_by_terminal = {
            tuple(item.terminal_candidate_id): item
            for item in (getattr(analysis, "termination_path_effect_evidence", ()) or ())
        }
        profile_ops = set(getattr(profile, "region_pcode_op_keys", ()) or ())
        artifact_keys = []
        for region in termination_regions:
            terminal = terminal_by_id.get(tuple(region.terminal_candidate_id))
            contract = getattr(terminal, "termination_contract", None) if terminal is not None else None
            op_ref = getattr(terminal, "op_ref", None) if terminal is not None else None
            producer_evidence = producer_evidence_by_terminal.get(tuple(region.terminal_candidate_id))
            expected_guard_key = tuple(
                sorted((condition.structural_key() for condition in region.guard), key=repr)
            )
            if (
                contract is None
                or producer_evidence is None
                or op_ref is None
                or int(getattr(producer_evidence, "schema_version", 0) or 0) != 1
                or producer_evidence.producer_id != "analyzer_terminal_path_effect_v1"
                or producer_evidence.contract.stable_key() != contract.stable_key()
                or producer_evidence.terminal_op_ref.stable_key() != op_ref.stable_key()
                or tuple(producer_evidence.control_effect_profile_key) != tuple(profile.stable_key())
                or tuple(producer_evidence.path_guard_key) != expected_guard_key
                or int(getattr(contract, "schema_version", 0) or 0) != 1
                or not _termination_tuple_schema(contract, terminal.terminal_kind_candidate)
                or tuple(contract.object_identity_key) != tuple(op_ref.stable_key())
                or tuple(op_ref.stable_key()) not in profile_ops
                or not tuple(contract.source_contract_key)
                or tuple(contract.source_contract_key) != tuple(region.producer_evidence_key)
                or tuple(contract.source_contract_key)[:1] != ("terminal_path_effect_evidence_v1",)
                or len(tuple(contract.source_contract_key)) < 4
                or tuple(contract.source_contract_key)[1] != tuple(op_ref.stable_key())
                or tuple(contract.source_contract_key)[2] != tuple(profile.stable_key())
                or tuple(contract.source_contract_key)[3] != expected_guard_key
            ):
                return UnaryProducerResult("unclassified")
            contracts.append(contract)
            artifact_keys.append((
                "validated_termination_classification_v1",
                tuple(terminal.candidate_id),
                contract.stable_key(),
                tuple(profile.stable_key()),
                producer_evidence.stable_key(),
            ))
        validated_termination_state["contracts"] = tuple(contracts)
        validated_termination_state["artifact_keys"] = tuple(artifact_keys)
        return UnaryProducerResult(
            "proved",
            {"termination_classification_artifact_keys": tuple(artifact_keys)},
        )

    def validated_termination_contracts():
        return validated_termination_state["contracts"]

    def validated_divergence_payloads():
        outcomes = tuple(getattr(analysis, "divergence_outcomes", ()) or ())
        if len(outcomes) != len(divergence_regions):
            return None
        def profile_block_identity(key):
            key = tuple(key) if isinstance(key, (tuple, list)) else key
            if isinstance(key, tuple) and key:
                if key[0] == "pcode_block" and len(key) >= 5:
                    return key[3]
                if key[0] == "pcode_block" and len(key) >= 2:
                    return key[1]
                if key[0] == "block" and len(key) >= 2:
                    return key[1]
            return key

        profile_block_indices = {
            profile_block_identity(key)
            for key in (getattr(profile, "region_block_keys", ()) or ())
        }
        profile_edge_indices = {
            (profile_block_identity(source), profile_block_identity(target))
            for source, target in (getattr(profile, "region_cfg_edge_keys", ()) or ())
        }
        current_cfg_surface = (
            tuple(sorted(profile_block_indices, key=repr)),
            tuple(sorted(profile_edge_indices, key=repr)),
        )
        validated = []
        for outcome, region in zip(outcomes, divergence_regions):
            proof = getattr(outcome, "proof", None)
            if not isinstance(proof, Mapping):
                return None
            if tuple(getattr(outcome, "guard", ()) or ()) != tuple(getattr(region, "guard", ()) or ()):
                return None
            proof_kind = proof.get("proof_kind")
            proof_cfg_surface = proof.get("cfg_applicability_surface")
            if not (
                isinstance(proof_cfg_surface, (tuple, list))
                and len(proof_cfg_surface) == 2
                and tuple(proof_cfg_surface[0]) == current_cfg_surface[0]
                and tuple(tuple(edge) for edge in proof_cfg_surface[1]) == current_cfg_surface[1]
            ):
                return None
            if proof_kind == "branch_guarded_structural_nonprogress_must_diverge":
                nonprogress_edges = {
                    tuple(edge) for edge in tuple(proof.get("nonprogress_backedges") or ())
                    if isinstance(edge, (tuple, list)) and len(edge) == 2
                }
                conditional_edges = {
                    tuple(edge) for edge in tuple(proof.get("conditional_progress_backedges") or ())
                    if isinstance(edge, (tuple, list)) and len(edge) == 2
                }
                if not (
                    proof.get("candidate_rule") == "branch_guarded_loop_invariant_nonprogress"
                    and tuple(proof.get("invariant") or ())
                    and tuple(proof.get("structural_recurrence_proof") or ())[:1]
                    == ("branch_guarded_affine_unit_count_structural_proof",)
                    and (tuple(proof.get("nonprogress_backedges") or ()) or (
                        tuple(proof.get("conditional_progress_backedges") or ())
                        and proof.get("conditional_progress_guard_negated_by_invariant") is True
                    ))
                    and proof.get("state_preservation") == "state_phi_nonprogress_backedge_identity"
                    and proof.get("accumulator_preservation") == "accumulator_phi_nonprogress_backedge_identity"
                    and proof.get("loop_has_cfg_cycle") is True
                    and proof.get("forbidden_control_effect_ops_absent") is True
                    and getattr(profile, "cfg_acyclic", True) is False
                    and nonprogress_edges.issubset(profile_edge_indices)
                    and conditional_edges.issubset(profile_edge_indices)
                ):
                    return None
                validated.append(proof)
                continue
            if proof_kind == "branch_guarded_while_nonprogress_must_diverge":
                safety = proof.get("side_effect_control_safety")
                reachable = set(proof.get("reachable_blocks") or ())
                cycle = set(proof.get("cycle_blocks") or ())
                excluded = {
                    (edge.get("source"), edge.get("target"))
                    for edge in tuple(proof.get("excluded_edges") or ())
                    if isinstance(edge, Mapping)
                }
                # Legacy producer serializes block identities for this proof.
                profile_blocks_text = {str(key) for key in profile_block_indices}
                profile_edges_text = {(str(source), str(target)) for source, target in profile_edge_indices}
                cycle_exits = {
                    edge for edge in profile_edges_text
                    if edge[0] in cycle and edge[1] not in cycle
                }
                if not (
                    proof.get("candidate_rule") == "branch_guarded_loop_invariant_nonprogress"
                    and tuple(proof.get("invariant") or ())
                    and tuple(proof.get("reachable_blocks") or ())
                    and tuple(proof.get("cycle_blocks") or ())
                    and tuple(proof.get("excluded_edges") or ())
                    and isinstance(safety, Mapping)
                    and all(safety.get(key) is True for key in (
                        "forbidden_ops_absent", "return_ops_absent_under_invariant",
                        "guard_state_writes_absent_under_invariant",
                        "guard_dependency_writes_absent_under_invariant",
                    ))
                    and all(
                        isinstance(edge, Mapping)
                        and edge.get("relation") == "invariant_contradicts_edge"
                        and "source" in edge and "target" in edge and bool(edge.get("edge_condition"))
                        for edge in tuple(proof.get("excluded_edges") or ())
                    )
                    and getattr(profile, "cfg_acyclic", True) is False
                    and reachable.issubset(profile_blocks_text)
                    and cycle and cycle.issubset(reachable)
                    and excluded.issubset(profile_edges_text)
                    and cycle_exits.issubset(excluded)
                    and any(source in cycle and target in cycle for source, target in profile_edges_text)
                ):
                    return None
                validated.append(proof)
                continue
            required_scalars = {
                "proof_kind": "single_guard_nonprogress_must_diverge",
                "candidate_rule": "side_effect_free_nonprogress_loop_guard_complement",
                "guard": "param_positive",
                "return_partition": "param_nonpositive_return_zero",
            }
            if any(proof.get(key) != value for key, value in required_scalars.items()):
                return None
            scc_blocks = tuple(proof.get("scc_blocks") or ())
            entry_edges = tuple(proof.get("entry_edges") or ())
            exit_edges = tuple(proof.get("exit_edges") or ())
            safety = proof.get("side_effect_control_safety")
            invariant = proof.get("invariant_preservation")
            if (
                not scc_blocks
                or not set(scc_blocks).issubset(profile_block_indices)
                or not entry_edges
                or not isinstance(safety, Mapping)
                or not all(safety.get(key) is True for key in (
                    "forbidden_ops_absent", "return_ops_absent_in_scc", "guard_state_writes_absent"
                ))
                or not isinstance(invariant, Mapping)
                or not (
                    invariant.get("internal_guarded_continue") is True
                    or invariant.get("internal_unconditional_continue") is True
                )
            ):
                return None
            for edge in (*entry_edges, *exit_edges):
                if not isinstance(edge, Mapping) or "source" not in edge or "target" not in edge or "guard_relation" not in edge:
                    return None
            validated.append(proof)
        return tuple(validated)

    def cfg_reachability():
        def block_identity(value):
            key = tuple(value) if isinstance(value, (tuple, list)) else value
            if isinstance(key, tuple) and len(key) >= 5 and key[0] == "pcode_block":
                return ("pcode_block", key[3], key[-1])
            if isinstance(key, tuple) and len(key) == 3 and key[0] == "pcode_block":
                return ("pcode_block", key[1], key[2])
            return key
        region_op_keys = set(getattr(profile, "region_pcode_op_keys", ()) or ()) if profile is not None else set()
        block_keys = {
            block_identity(item) for item in (getattr(profile, "region_block_keys", ()) or ())
        } if profile is not None else set()
        entry_key = getattr(profile, "region_entry_block_key", None) if profile is not None else None
        adjacency = {}
        for source, target in (getattr(profile, "region_cfg_edge_keys", ()) or ()) if profile is not None else ():
            adjacency.setdefault(block_identity(source), set()).add(block_identity(target))
        reachable = set()
        pending = [block_identity(entry_key)] if entry_key is not None else []
        while pending:
            current = pending.pop()
            if current in reachable:
                continue
            reachable.add(current)
            pending.extend(adjacency.get(current, ()))
        all_blocks_reachable = bool(block_keys) and reachable == block_keys
        visiting = set()
        visited = set()

        def has_cfg_cycle(node):
            if node in visiting:
                return True
            if node in visited:
                return False
            visiting.add(node)
            if any(has_cfg_cycle(successor) for successor in adjacency.get(node, ())):
                return True
            visiting.remove(node)
            visited.add(node)
            return False

        cfg_surface_acyclic = bool(block_keys) and not any(
            has_cfg_cycle(block) for block in block_keys if block not in visited
        )
        validated_cfg_state["acyclic"] = cfg_surface_acyclic
        validated_cfg_state["adjacency"] = tuple(sorted(
            ((source, tuple(sorted(targets, key=repr))) for source, targets in adjacency.items()),
            key=repr,
        ))
        all_return_exits_reachable = all(
            block_identity(item) in reachable for item in (getattr(profile, "region_exit_block_keys", ()) or ())
        ) if profile is not None else False
        return_terminals = tuple(
            item for item in terminals if str(item.terminal_kind_candidate) == "return"
        )
        terminal_objects_linked = all(
            getattr(item, "op_ref", None) is not None
            and item.op_ref.stable_key() in region_op_keys
            for item in return_terminals
        )
        termination_terminals = tuple(
            item for item in terminals if str(item.terminal_kind_candidate) in termination_kinds
        )
        termination_objects_linked = all(
            getattr(item, "op_ref", None) is not None
            and item.op_ref.stable_key() in region_op_keys
            for item in termination_terminals
        )
        termination_surface_complete = bool(
            not termination_terminals
            and getattr(profile, "terminal_return_coverage_complete", False)
            and int(getattr(profile, "abnormal_terminal_block_count", 0) or 0) == 0
        ) or bool(
            termination_terminals
            and len(termination_terminals) == int(getattr(profile, "abnormal_terminal_block_count", 0) or 0)
            and termination_objects_linked
            and (not termination_terminals or validated_termination_contracts() is not None)
        )
        profile_key = profile.stable_key() if callable(getattr(profile, "stable_key", None)) else None
        profile_is_typed = bool(
            isinstance(profile_key, tuple)
            and profile_key
            and profile_key[0] == "function_control_effect_profile"
            and tuple(getattr(seed, "control_flow_evidence_key", ()) or ()) == profile_key
        )
        complete = bool(
            profile_is_typed
            and getattr(profile, "pcode_enumeration_complete", False)
            and getattr(profile, "cfg_edges_complete", False)
            and getattr(profile, "region_identity_complete", False)
            and getattr(profile, "region_single_entry", False)
            and getattr(profile, "region_all_exits_enumerated", False)
            and getattr(profile, "region_cross_edges_enumerated", False)
            and termination_surface_complete
            and not getattr(profile, "unsupported_mnemonics", ())
            and int(getattr(profile, "branchind_count", 0) or 0) == 0
            and int(getattr(profile, "callind_count", 0) or 0) == 0
            and int(getattr(profile, "callother_count", 0) or 0) == 0
            and terminal_objects_linked
            and all_blocks_reachable
            and all_return_exits_reachable
        )
        if not complete and getattr(self, "debug", False):
            self._debug_print(
                "Unary outcome CFG prerequisite incomplete: "
                f"typed={profile_is_typed}, pcode={getattr(profile, 'pcode_enumeration_complete', False)}, "
                f"edges={getattr(profile, 'cfg_edges_complete', False)}, "
                f"identity={getattr(profile, 'region_identity_complete', False)}, "
                f"single_entry={getattr(profile, 'region_single_entry', False)}, "
                f"all_exits={getattr(profile, 'region_all_exits_enumerated', False)}, "
                f"cross_edges={getattr(profile, 'region_cross_edges_enumerated', False)}, "
                f"termination={termination_surface_complete}, terminals={terminal_objects_linked}, "
                f"blocks_reachable={all_blocks_reachable}, returns_reachable={all_return_exits_reachable}, "
                f"entry={block_identity(entry_key)!r}, blocks={tuple(sorted(block_keys, key=repr))!r}, "
                f"reachable={tuple(sorted(reachable, key=repr))!r}, "
                f"edges={tuple(getattr(profile, 'region_cfg_edge_keys', ()) or ())!r}"
            )
        return UnaryProducerResult(
            "proved" if complete else "incomplete",
            {"control_flow_profile_key": profile_key if complete else None},
        )

    def path_region_completeness():
        # Issue #131: 展開ケース数・経路数の上限で切り捨てが起きた関数では、
        # region 集合そのものが「生き残ったケース」から作られている。生存 guard の
        # 和が恒真でも元の展開が完全である証明にはならないので、CFG 事実との
        # 照合へ進まずここで未完了にする。
        if bool(getattr(analysis, "has_expansion_budget_truncation", lambda: False)()):
            return UnaryProducerResult(
                "case_budget_exceeded",
                {"path_proof_kind": None, "return_member_path_artifacts": ()},
            )
        base_complete = bool(
            terminals
            and not unknown_regions
            and not getattr(analysis, "unknown_outcomes", ())
            and not getattr(seed, "unresolved_control_evidence", ())
            and not getattr(analysis, "incomplete_control_flow", False)
            and {
                tuple(region.terminal_candidate_id)
                for region in (getattr(seed, "symbolic_regions", ()) or ())
            } == {tuple(terminal.candidate_id) for terminal in terminals}
            and all(
                self._outcome_conditions_smt(tuple(region.guard), replace_fn) is not None
                for region in (getattr(seed, "symbolic_regions", ()) or ())
            )
        )
        def guard_key(guards):
            return tuple(sorted((condition.structural_key() for condition in guards or ()), key=repr))

        terminal_by_id = {tuple(item.candidate_id): item for item in terminals}
        return_infos_by_ref = {}
        for info in (getattr(analysis, "returns", ()) or ()):
            evidence = getattr(info, "return_path_evidence", None)
            if evidence is not None and evidence.terminal_op_ref is not None:
                return_infos_by_ref.setdefault(evidence.terminal_op_ref.stable_key(), []).append(info)

        def rewrite_proofs_valid(evidence):
            for proof in tuple(getattr(evidence, "guard_rewrite_proof_keys", ()) or ()):
                if not (
                    isinstance(proof, tuple)
                    and len(proof) == 3
                    and proof[0] in {
                        "return_extraction_guard_materialization_v1",
                        "bounded_refinement_guard_rewrite_v1",
                    }
                    and isinstance(proof[1], tuple)
                    and proof[1][:1] == ("return_path_evidence_v1",)
                    and tuple(proof[2]) == tuple(evidence.path_guard_keys)
                    and proof[1][2] == evidence.terminal_op_ref.stable_key()
                    and proof[1][3] == "complete"
                ):
                    return False
            return True
        return_member_proofs = []
        for terminal_id, terminal in terminal_by_id.items():
            if terminal.terminal_kind_candidate != "return":
                continue
            op_ref = getattr(terminal, "op_ref", None)
            infos = return_infos_by_ref.get(op_ref.stable_key(), ()) if op_ref is not None else ()
            evidences = tuple(
                info.return_path_evidence for info in infos
                if getattr(info, "return_path_evidence", None) is not None
            )
            member_regions = tuple(
                region for region in return_regions
                if tuple(region.terminal_candidate_id) == terminal_id
            )
            actual_guard_keys = tuple(sorted({guard_key(region.guard) for region in member_regions}, key=repr))
            evidence_guard_keys = tuple(sorted({
                guard for evidence in evidences for guard in tuple(evidence.path_guard_keys)
            }, key=repr))
            evidence_keys = {evidence.stable_key() for evidence in evidences}
            complete = bool(
                evidences
                and all(
                    evidence.coverage_status == "complete"
                    and evidence.terminal_op_ref is not None
                    and evidence.terminal_op_ref.stable_key() == op_ref.stable_key()
                    and not evidence.pruning_proof_keys
                    and rewrite_proofs_valid(evidence)
                    for evidence in evidences
                )
                and evidence_guard_keys == actual_guard_keys
                and member_regions
                and all(
                    tuple(region.producer_evidence_key)[:1] == ("return_path_evidence",)
                    and tuple(region.producer_evidence_key)[1] in evidence_keys
                    for region in member_regions
                )
            )
            member_evidence_key = tuple(sorted(evidence_keys, key=repr)) if complete else None
            return_member_proofs.append((terminal_id, complete, member_evidence_key))
            if not complete and getattr(self, "debug", False):
                self._debug_print(
                    "Return terminal path evidence mismatch: "
                    f"terminal={terminal_id!r}, op={op_ref.stable_key() if op_ref is not None else None!r}, "
                    f"statuses={tuple(getattr(e, 'coverage_status', None) for e in evidences)!r}, "
                    f"evidence_guards={evidence_guard_keys!r}, "
                    f"region_guards={actual_guard_keys!r}, pruning={tuple(getattr(e, 'pruning_proof_keys', None) for e in evidences)!r}, "
                    f"producer_keys={tuple(region.producer_evidence_key for region in member_regions)!r}"
                )
        all_return_members_exact = bool(
            len(return_member_proofs) == len({
                tuple(region.terminal_candidate_id) for region in return_regions
            })
            and all(item[1] for item in return_member_proofs)
        )
        general_return_exact = bool(
            base_complete
            and return_regions
            and not divergence_regions
            and not termination_regions
            and all_return_members_exact
            and validated_cfg_state["acyclic"]
        )
        guarded_divergence_exact = bool(
            base_complete
            and len(return_regions) == 1
            and len(divergence_regions) == 1
            and len(terminals) == 2
            and validated_divergence_payloads() is not None
            and all_return_members_exact
        )
        termination_exact = bool(
            base_complete
            and termination_regions
            and validated_termination_contracts() is not None
            and all(tuple(region.producer_evidence_key) for region in termination_regions)
            and (not return_regions or all_return_members_exact)
            and (not divergence_regions or validated_divergence_payloads() is not None)
        )
        if not (general_return_exact or guarded_divergence_exact or termination_exact) and getattr(self, "debug", False):
            self._debug_print(
                "Unary outcome path prerequisite incomplete: "
                f"base={base_complete}, return_regions={len(return_regions)}, "
                f"divergence_regions={len(divergence_regions)}, termination_regions={len(termination_regions)}, "
                f"acyclic={validated_cfg_state['acyclic']}, profile_acyclic={getattr(profile, 'cfg_acyclic', False)}, "
                f"adjacency={validated_cfg_state['adjacency']!r}, return_members={return_member_proofs!r}"
            )
        return UnaryProducerResult(
            "proved" if general_return_exact or guarded_divergence_exact or termination_exact else "incomplete",
            {
                "path_proof_kind": "acyclic_return_paths" if general_return_exact else "guarded_scc_partition" if guarded_divergence_exact else "validated_termination_contract" if termination_exact else None,
                "return_member_path_artifacts": tuple(item[2] for item in return_member_proofs if item[1]),
            },
        )

    def member_classification():
        kinds = tuple(str(item.terminal_kind_candidate) for item in terminals)
        supported = bool(not unknown_regions and not getattr(analysis, "unknown_outcomes", ()))
        supported = supported and all(kind in {"return", "must_diverge", *termination_kinds} for kind in kinds)
        divergence_proofs = validated_divergence_payloads()
        divergence_proof_digests = tuple(
            SnapshotFingerprintCodec.digest(item)
            for item in (divergence_proofs or ())
        )
        if divergence_regions and divergence_proofs is None:
            supported = False
        termination_contracts = validated_termination_contracts()
        if termination_regions and termination_contracts is None:
            supported = False
        return UnaryProducerResult(
            "proved" if supported else "unclassified",
            {
                "member_kinds": kinds,
                "divergence_proof_digests": divergence_proof_digests,
                "termination_contract_keys": tuple(
                    item.stable_key() for item in (termination_contracts or ())
                ),
            },
        )

    def same_kind_consistency():
        for index, left in enumerate(return_regions):
            left_value = getattr(left, "observed_value", None)
            if left_value is None:
                return UnaryProducerResult("comparison_surface_missing")
            for right in return_regions[index + 1:]:
                right_value = getattr(right, "observed_value", None)
                if right_value is None:
                    return UnaryProducerResult("comparison_surface_missing")
                left_guard = self._outcome_conditions_smt(tuple(left.guard), replace_fn)
                right_guard = self._outcome_conditions_smt(tuple(right.guard), replace_fn)
                left_smt = self._outcome_expression_smt(left_value, replace_fn)
                right_smt = self._outcome_expression_smt(right_value, replace_fn)
                left_bits = int(expression_smt_bit_width(left_value) or 0)
                right_bits = int(expression_smt_bit_width(right_value) or 0)
                if (
                    left_guard is None or right_guard is None
                    or left_smt is None or right_smt is None
                    or left_bits <= 0 or right_bits <= 0
                    or left_bits != right_bits
                ):
                    return UnaryProducerResult("comparison_surface_missing")
                status = _unary_solver_status(self, unary_ctx, [
                    *left_guard, *right_guard,
                    f"(not (= {left_smt} {right_smt}))",
                ], "Unary return disequality")
                if status != "unsat":
                    return UnaryProducerResult("conflict" if status == "sat" else status)
        terminal_by_id = {
            tuple(item.candidate_id): item for item in terminals
        }
        for index, left in enumerate(termination_regions):
            left_contract = terminal_by_id[tuple(left.terminal_candidate_id)].termination_contract
            for right in termination_regions[index + 1:]:
                right_contract = terminal_by_id[tuple(right.terminal_candidate_id)].termination_contract
                if left_contract.stable_key() == right_contract.stable_key():
                    continue
                assertions = []
                for region in (left, right):
                    rendered = self._outcome_conditions_smt(tuple(region.guard), replace_fn)
                    if rendered is None:
                        return UnaryProducerResult("unknown")
                    assertions.extend(rendered)
                status = _unary_solver_status(self, unary_ctx, assertions, "Unary termination contract conflict")
                if status != "unsat":
                    return UnaryProducerResult("conflict" if status == "sat" else status)
        return UnaryProducerResult("proved")

    def cross_kind_disjointness():
        kind_groups = (return_regions, divergence_regions, termination_regions)
        for left_index, left_group in enumerate(kind_groups):
            for right_group in kind_groups[left_index + 1:]:
                for left in left_group:
                    for right in right_group:
                        assertions = []
                        for region in (left, right):
                            rendered = self._outcome_conditions_smt(tuple(region.guard), replace_fn)
                            if rendered is None:
                                return UnaryProducerResult("unknown")
                            assertions.extend(rendered)
                        status = _unary_solver_status(self, unary_ctx, assertions, "Unary cross-kind overlap")
                        if status != "unsat":
                            return UnaryProducerResult("overlap" if status == "sat" else status)
        return UnaryProducerResult("proved")

    def residual_totality():
        # Issue #131: 生存 region の guard の和が恒真でも「展開が完全」ではない。
        # 切り捨てのある関数は path_region_completeness で先に止まるので、ここへは
        # 打ち切りなしのケース集合だけが到達する。
        union = self._outcome_guard_union_smt(
            [tuple(region.guard) for region in (return_regions + divergence_regions + termination_regions)], replace_fn
        )
        if union is None:
            return UnaryProducerResult("incomplete")
        status = _unary_solver_status(self, unary_ctx, [f"(not {union})"], "Unary classified residual")
        return UnaryProducerResult("proved" if status == "unsat" else ("residual_sat" if status == "sat" else status))

    producers = {
        "cfg_reachability": cfg_reachability,
        "termination_classification": termination_classification,
        "path_region_completeness": path_region_completeness,
        "member_classification": member_classification,
        "same_kind_consistency": same_kind_consistency,
        "cross_kind_disjointness": cross_kind_disjointness,
        "residual_totality": residual_totality,
        "partition_complete": lambda: UnaryProducerResult(
            "proved"
            if not unknown_regions and not getattr(analysis, "unknown_outcomes", ())
            else "unclassified"
        ),
    }
    proof = prove_unary_partition(
        analysis,
        domain_contract=getattr(seed, "input_domain_contract", ()),
        normalization_policy_digest=(
            self._return_coverage_normalization_policy_digest(
                self._return_coverage_normalization_policy()
            ) or "return-coverage-normalization-unavailable"
        ),
        producers=producers,
    )
    if not proof.complete or proof.cache_entry is None:
        return proof
    pair_side = "left" if replace_fn is getattr(self, "_param_replace_fn1", None) else None
    # Callers use function1/function2 replacement closures that are not stable
    # identity objects.  Match the current pair snapshots instead.
    current_fingerprint = runtime._snapshot(analysis, "candidate").semantic_fingerprint
    left_fingerprint = runtime.current_view.semantic_surface.get("left_snapshot")
    right_fingerprint = runtime.current_view.semantic_surface.get("right_snapshot")
    if current_fingerprint == left_fingerprint and current_fingerprint != right_fingerprint:
        pair_side = "left"
    elif current_fingerprint == right_fingerprint and current_fingerprint != left_fingerprint:
        pair_side = "right"
    elif current_fingerprint == left_fingerprint == right_fingerprint:
        pair_side = "left"
    else:
        return None
    normalization_digest = (
        self._return_coverage_normalization_policy_digest(
            self._return_coverage_normalization_policy()
        ) or "return-coverage-normalization-unavailable"
    )
    try:
        runtime.import_unary_artifact_for_analysis(
            proof.cache_entry,
            analysis=analysis,
            pair_side=pair_side,
            domain_contract=getattr(seed, "input_domain_contract", ()),
            normalization_policy_digest=normalization_digest,
        )
    except ValueError:
        return UnaryPartitionProofResult("blocked", "outcome_pair_import_applicability_mismatch")
    return proof


def prepare_unary_return_coverage_for_width(
    self,
    base_ctx: Mapping[str, Any],
    analysis1: FunctionReturnAnalysis,
    analysis2: FunctionReturnAnalysis,
    replace_fn1,
    replace_fn2,
) -> bool:
    """Publish both final unary coverage artifacts before width consumers run."""

    proofs = (
        _prove_unary_outcome_for_analysis(self, base_ctx, analysis1, replace_fn1),
        _prove_unary_outcome_for_analysis(self, base_ctx, analysis2, replace_fn2),
    )
    return all(proof is not None and proof.complete for proof in proofs)

def _impl__collect_return_coverage_unsafety_reasons(
    self,
    base_ctx: Dict[str, Any],
    cases1: Sequence[Any],
    cases2: Sequence[Any],
    param_replace_fn1,
    param_replace_fn2,
    analysis1: Optional[FunctionReturnAnalysis] = None,
    analysis2: Optional[FunctionReturnAnalysis] = None,
) -> List[str]:
    reasons: List[str] = []
    outcome_covered_labels = self._outcome_partition_covered_labels(
        base_ctx,
        analysis1,
        analysis2,
        param_replace_fn1,
        param_replace_fn2,
    )
    outcome_inconclusive_labels = self._outcome_partition_inconclusive_labels(
        base_ctx,
        analysis1,
        analysis2,
        param_replace_fn1,
        param_replace_fn2,
    )
    for label, cases, replace_fn, analysis in (
        ("function1", cases1, param_replace_fn1, analysis1),
        ("function2", cases2, param_replace_fn2, analysis2),
    ):
        if analysis is not None and bool(
            getattr(analysis, "has_expansion_budget_truncation", lambda: False)()
        ):
            # Issue #131: 切り捨てが起きた側は、outcome partition・object-centric
            # coverage・SMT 全域性のどの経路にも進ませない（生存ケースだけを見た
            # 判定が covered になり得るため）。completion proof も発行しない。
            coverage_result = ReturnCoverageCheckResult(
                status="inconclusive",
                reason_id=UnknownReasonId.EXPANSION_CASE_BUDGET_EXCEEDED,
                detail=(
                    f"Return case expansion truncated for {label}: "
                    "surviving cases are not the whole case set"
                ),
                inconclusive_cause="expansion_case_budget_exceeded",
                can_record_completion_proof=False,
                solver_status="unknown",
            )
        elif label in outcome_covered_labels:
            coverage_result = ReturnCoverageCheckResult(
                status="covered",
                coverage_proof_method="outcome_partition_equivalence",
                solver_status="unsat",
            )
        elif label in outcome_inconclusive_labels:
            unary_blocker = (getattr(self, "_last_unary_outcome_blockers", {}) or {}).get(label)
            coverage_result = ReturnCoverageCheckResult(
                status="inconclusive",
                reason_id=_unary_blocker_reason_id(unary_blocker),
                detail=f"Outcome partition unknown for {label}: {unary_blocker or 'unknown outcome region'}",
                inconclusive_cause="unknown_outcome_partition",
                solver_status="unknown",
            )
        else:
            coverage_result = self._check_return_case_coverage_gap(
                base_ctx,
                cases,
                replace_fn,
                label,
            )
        if coverage_result.status == "gap":
            if coverage_result.detail:
                self._debug_print(coverage_result.detail)
            reasons.append(f"{label}:return_coverage_gap")
            reasons.extend(
                f"{label}:{reason_id}"
                for reason_id in self._summary_return_candidate_blocker_reason_ids(analysis)
            )
        elif coverage_result.status == "inconclusive":
            if coverage_result.detail:
                self._debug_print(coverage_result.detail)
            blocker_reason = coverage_result.reason_id or UnknownReasonId.RETURN_COVERAGE_INCONCLUSIVE
            reasons.append(f"{label}:{_reason_id_value(blocker_reason)}")
            if (
                coverage_result.reason_id == UnknownReasonId.RETURN_COVERAGE_INCONCLUSIVE
                and self.enable_completed_recovery_proofs
                and analysis is not None
                and coverage_result.can_record_completion_proof
                and coverage_result.inconclusive_cause in self._RETURN_COVERAGE_DISCHARGEABLE_INCONCLUSIVE_CAUSES
                and self._return_coverage_proof_content_can_discharge_inconclusive(
                    self._return_coverage_inconclusive_proof_content(
                        base_ctx=base_ctx,
                        label=label,
                        cases=cases,
                        replace_fn=replace_fn,
                        inconclusive_cause=coverage_result.inconclusive_cause,
                    )
                )
            ):
                self._record_completed_return_coverage_proof(
                    label,
                    blocker_reason,
                    analysis,
                    analysis1,
                    analysis2,
                    proof_content=self._return_coverage_inconclusive_proof_content(
                        base_ctx=base_ctx,
                        label=label,
                        cases=cases,
                        replace_fn=replace_fn,
                        inconclusive_cause=coverage_result.inconclusive_cause,
                    ),
                )
        elif (
            coverage_result.status == "covered"
            and analysis1 is not None
            and analysis2 is not None
            and analysis is not None
        ):
            blocker_reason = self._analysis_requires_completed_return_coverage_proof(
                analysis,
                ignored_reason_ids=(coverage_result.reason_id,),
            )
            required_blocker_reason = blocker_reason
            proof_record_reason = blocker_reason
            if proof_record_reason is None and self.enable_completed_recovery_proofs:
                proof_record_reason = UnknownReasonId.RETURN_COVERAGE_GAP
            if proof_record_reason is not None and self.enable_completed_recovery_proofs:
                proof_content = self._return_coverage_covered_proof_content(
                    base_ctx=base_ctx,
                    label=label,
                    cases=cases,
                    replace_fn=replace_fn,
                    coverage_proof_method=coverage_result.coverage_proof_method,
                    solver_status=coverage_result.solver_status,
                )
                self._record_completed_return_coverage_proof(
                    label,
                    proof_record_reason,
                    analysis,
                    analysis1,
                    analysis2,
                    proof_content=proof_content,
                )
                if required_blocker_reason in {
                    UnknownReasonId.RETURN_COVERAGE_GAP,
                    UnknownReasonId.RETURN_COVERAGE_INCONCLUSIVE,
                }:
                    reason_record = self._make_blocking_unsafety_unknown_reason(
                        f"{label}:{required_blocker_reason.value}",
                        analysis1,
                        analysis2,
                        stage="S_RETURN_COVERAGE_CHECK",
                    )
                    if not self._return_coverage_proof_is_complete(
                        reason_record,
                        analysis1,
                        analysis2,
                    ):
                        reasons.append(f"{label}:{required_blocker_reason.value}")
            elif blocker_reason is not None:
                reasons.append(f"{label}:{blocker_reason.value}")
            if coverage_result.detail:
                self._debug_print(coverage_result.detail)
    return reasons

def _impl__record_completed_return_coverage_proof(
    self,
    label: str,
    reason_id: UnknownReasonId,
    analysis: FunctionReturnAnalysis,
    analysis1: FunctionReturnAnalysis,
    analysis2: FunctionReturnAnalysis,
    proof_content: Optional[Mapping[str, Any]] = None,
) -> None:
    if not self.enable_completed_recovery_proofs:
        return
    if self._analysis_has_active_return_coverage_blockers(
        analysis,
        ignored_reason_ids=(reason_id,),
    ):
        return
    requirements = self._RETURN_COVERAGE_COMPLETION_REQUIREMENTS.get(reason_id)
    if not requirements:
        return
    object_target_key = self._return_coverage_object_target_key(
        f"{label}:{reason_id.value}",
        analysis1,
        analysis2,
    )
    if object_target_key is None:
        return
    proof_kind = UnknownRecoveryProofKind.RETURN_COVERAGE_COMPLETION.value
    existing_ids = {
        self._normalize_nested_tuple(item.get("proof_obligation_id"))
        for item in getattr(analysis, "completed_recovery_proof_evidence", ()) or ()
        if isinstance(item, Mapping)
    }
    records: List[Dict[str, Any]] = [
        dict(item)
        for item in getattr(analysis, "completed_recovery_proof_evidence", ()) or ()
        if isinstance(item, Mapping)
    ]
    proof_content_map = dict(proof_content) if isinstance(proof_content, Mapping) else {}
    proof_content_map["proof_target_identity"] = object_target_key
    prototype = {
        "status": "complete",
        "reason_id": reason_id.value,
        "target_schema_version": self._RETURN_COVERAGE_TARGET_SCHEMA_VERSION,
        "proof_schema_version": self._RETURN_COVERAGE_PROOF_SCHEMA_VERSION,
        "object_target_key": object_target_key,
        "proof_content": proof_content_map,
    }
    if not self._return_coverage_proof_content_is_complete(
        prototype,
        reason_id=reason_id,
    ):
        return
    for proof_stage, evidence_kind in requirements:
        proof_id = build_proof_obligation_id(
            reason_id.value,
            proof_stage,
            proof_kind,
            evidence_kind,
            object_target_key,
        )
        if proof_id in existing_ids:
            continue
        candidate = {
            "object_derived": True,
            "status": "complete",
            "reason_id": reason_id.value,
            "recovery_proof_kind": proof_kind,
            "target_schema_version": self._RETURN_COVERAGE_TARGET_SCHEMA_VERSION,
            "proof_schema_version": self._RETURN_COVERAGE_PROOF_SCHEMA_VERSION,
            "proof_stage": proof_stage,
            "evidence_kind": evidence_kind,
            "object_target_key": object_target_key,
            "proof_obligation_id": proof_id,
            "proof_source": "return_case_coverage_check",
            "coverage_status": "covered",
            "required_evidence": (evidence_kind,),
            "proof_content": proof_content_map,
        }
        if self._return_coverage_proof_id_from_evidence(candidate) is None:
            continue
        records.append(candidate)
        existing_ids.add(proof_id)
    analysis.completed_recovery_proof_evidence = tuple(records)

def _impl__return_coverage_covered_proof_content(
    self,
    base_ctx: Dict[str, Any],
    label: str,
    cases: Sequence[Any],
    replace_fn,
    *,
    coverage_proof_method: Optional[str] = None,
    solver_status: Optional[str] = None,
) -> Dict[str, Any]:
    disjuncts = self._return_case_smt_disjunctions(cases, replace_fn)
    query = self._build_return_case_coverage_query(
        base_ctx,
        cases,
        replace_fn,
        label,
    )
    normalized_query = self._normalize_query(query) if query is not None else None
    if normalized_query is None and disjuncts:
        normalized_query = "(or " + " ".join(disjuncts) + ")"
    normalized_query_status = (
        "complete" if normalized_query is not None else "missing"
    )
    structural_evidence = self._return_coverage_structural_proof_content(
        cases,
        solver_status=solver_status,
        coverage_proof_method=coverage_proof_method,
    )
    coverage_method = coverage_proof_method or "return_case_coverage_check"
    return {
        "proof_schema_version": self._RETURN_COVERAGE_PROOF_SCHEMA_VERSION,
        "normalization_schema_version": self._RETURN_COVERAGE_NORMALIZATION_SCHEMA_VERSION,
        **structural_evidence,
        "case_guard_disjunction": {
            "status": "complete",
            "query_cases": tuple(disjuncts or ()),
            "case_count": len(tuple(disjuncts or ())),
            "status_scope": "function-local",
        },
        "normalized_guard_formula": {
            "status": normalized_query_status,
            "query": normalized_query if normalized_query is not None else query,
        },
        "coverage_guard_evidence": {
            "status": normalized_query_status,
            "guard_source": "return_partition_guard_set",
            "coverage_status": "covered",
            "coverage_proof_method": coverage_method,
            "case_count": len(tuple(disjuncts or ())),
            "normalized_guard_formula_sha256": (
                hashlib.sha256(normalized_query.encode("utf-8")).hexdigest()
                if isinstance(normalized_query, str) and normalized_query
                else None
            ),
        },
        "coverage_status": {
            "status": "complete",
            "result": "covered",
            "proof_source": "return_case_coverage_check",
        },
    }

def _impl__return_coverage_inconclusive_proof_content(
    self,
    base_ctx: Dict[str, Any],
    label: str,
    cases: Sequence[Any],
    replace_fn,
    inconclusive_cause: Optional[str] = None,
) -> Dict[str, Any]:
    disjuncts = self._return_case_smt_disjunctions(cases, replace_fn)
    query = self._build_return_case_coverage_query(
        base_ctx,
        cases,
        replace_fn,
        label,
    )
    normalized_query = self._normalize_query(query) if query is not None else None
    if normalized_query is None and disjuncts:
        normalized_query = "(or " + " ".join(disjuncts) + ")"
    normalized_query_status = (
        "complete" if normalized_query is not None else "missing"
    )
    structural_evidence = self._return_coverage_structural_proof_content(
        cases,
        solver_status="unknown",
    )
    return {
        "proof_schema_version": self._RETURN_COVERAGE_PROOF_SCHEMA_VERSION,
        "normalization_schema_version": self._RETURN_COVERAGE_NORMALIZATION_SCHEMA_VERSION,
        "inconclusive_cause": inconclusive_cause,
        **structural_evidence,
        "case_guard_disjunction": {
            "status": "complete",
            "query_cases": tuple(disjuncts or ()),
            "case_count": len(tuple(disjuncts or ())),
            "status_scope": "function-local",
        },
        "normalized_guard_formula": {
            "status": normalized_query_status,
            "query": normalized_query if normalized_query is not None else query,
        },
        "coverage_guard_evidence": {
            "status": normalized_query_status,
            "guard_source": "case_guard_disjunction",
            "case_count": len(tuple(disjuncts or ())),
            "normalized_guard_formula_sha256": (
                hashlib.sha256(normalized_query.encode("utf-8")).hexdigest()
                if isinstance(normalized_query, str) and normalized_query
                else None
            ),
        },
        "solver_model_or_timeout": {
            "status": "unknown",
            "detail": "coverage query returned UNKNOWN/timeout",
        },
    }

def _impl__return_coverage_structural_proof_content(
    self,
    cases: Sequence[Any],
    *,
    solver_status: Optional[str],
    coverage_proof_method: Optional[str] = None,
) -> Dict[str, Any]:
    case_entries: List[Tuple[Any, ...]] = []
    miss_entries: List[Tuple[Any, ...]] = []
    bit_widths: Set[int] = set()
    signedness: Set[str] = set()
    for case_index, case in enumerate(cases or ()):
        return_info = getattr(case, "return_info", None)
        structural_conditions = (
            getattr(return_info, "conditions", None)
            if return_info is not None
            else getattr(case, "conditions", None)
        ) or ()
        structural_value = (
            getattr(return_info, "value", None)
            if return_info is not None
            else getattr(case, "value_expr", None)
        )
        guard_keys = tuple(
            self._return_condition_object_key(condition)
            for condition in structural_conditions
        )
        value_key = self._expression_runtime_object_key(structural_value)
        miss_expr = self._case_miss_expression(
            list(structural_conditions)
        )
        miss_key = self._expression_runtime_object_key(miss_expr) if miss_expr is not None else None
        case_entries.append(
            (
                "return_case_guard_set",
                int(case_index),
                ("guard_structural_keys", guard_keys),
                ("return_value_structural_key", value_key),
            )
        )
        miss_entries.append(
            (
                "case_miss_formula",
                int(case_index),
                miss_key,
            )
        )
        for condition in structural_conditions:
            self._collect_condition_width_sign_metadata(condition, bit_widths, signedness)
    case_entries = list(self._canonicalize_key_sequence(case_entries))
    miss_entries = list(self._canonicalize_key_sequence(miss_entries))
    return {
        "structural_guard_keys": {
            "status": "complete",
            "case_count": len(case_entries),
            "keys": tuple(case_entries),
        },
        "structural_miss_formula_keys": {
            "status": "complete",
            "case_count": len(miss_entries),
            "keys": tuple(miss_entries),
        },
        "coverage_solver_evidence": {
            "status": str(solver_status) if solver_status is not None else "not_applicable",
            "proof_method": coverage_proof_method or "unknown",
        },
        "bit_width_signedness_metadata": {
            "status": "complete",
            "bit_widths": tuple(sorted(bit_widths)),
            "signedness": tuple(sorted(signedness)),
        },
    }

def _impl__return_coverage_normalization_policy(cls, *, rules: Sequence[Any] = ()) -> Dict[str, Any]:
    return {
        "normalization_policy_id": cls._RETURN_COVERAGE_NORMALIZATION_POLICY_ID,
        "normalization_schema_version": cls._RETURN_COVERAGE_NORMALIZATION_SCHEMA_VERSION,
        "rule_set_version": cls._RETURN_COVERAGE_NORMALIZATION_RULESET_VERSION,
        "canonical_encoding_version": cls._RETURN_COVERAGE_NORMALIZATION_CANONICAL_ENCODING_VERSION,
        "rules": tuple(sorted(tuple(rules or ()), key=repr)),
    }

def _impl__return_coverage_normalization_policy_digest(cls, policy: Mapping[str, Any]) -> Optional[str]:
    if not isinstance(policy, Mapping):
        return None
    required = {
        "normalization_policy_id",
        "normalization_schema_version",
        "rule_set_version",
        "canonical_encoding_version",
        "rules",
    }
    if not required.issubset(set(policy.keys())):
        return None
    if policy.get("normalization_policy_id") != cls._RETURN_COVERAGE_NORMALIZATION_POLICY_ID:
        return None
    if policy.get("normalization_schema_version") != cls._RETURN_COVERAGE_NORMALIZATION_SCHEMA_VERSION:
        return None
    if policy.get("rule_set_version") != cls._RETURN_COVERAGE_NORMALIZATION_RULESET_VERSION:
        return None
    if policy.get("canonical_encoding_version") != cls._RETURN_COVERAGE_NORMALIZATION_CANONICAL_ENCODING_VERSION:
        return None
    rules = policy.get("rules")
    if not isinstance(rules, (tuple, list)):
        return None
    normalized_rules = []
    for rule in rules:
        if not isinstance(rule, Mapping) or not isinstance(rule.get("rule_id"), str):
            return None
        normalized_rules.append({key: rule[key] for key in sorted(rule.keys())})
    normalized_rules.sort(key=lambda item: str(item.get("rule_id")))
    return cls._canonical_json_digest(
        {
            "canonical_encoding_version": policy.get("canonical_encoding_version"),
            "normalization_policy_id": policy.get("normalization_policy_id"),
            "normalization_schema_version": policy.get("normalization_schema_version"),
            "rule_set_version": policy.get("rule_set_version"),
            "rules": tuple(normalized_rules),
        }
    )

def _impl__analysis_has_active_return_coverage_blockers(
    self,
    analysis: FunctionReturnAnalysis,
    *,
    ignored_reason_ids: Sequence[Optional[UnknownReasonId]],
) -> bool:
    return (
        self._analysis_requires_completed_return_coverage_proof(
            analysis,
            ignored_reason_ids=ignored_reason_ids,
        )
        is not None
    )

def _impl__analysis_requires_completed_return_coverage_proof(
    self,
    analysis: FunctionReturnAnalysis,
    *,
    ignored_reason_ids: Sequence[Optional[UnknownReasonId]],
) -> Optional[UnknownReasonId]:
    ignored_reason_kinds = {
        self._blocking_reason_kind(getattr(reason, "value", reason))
        for reason in ignored_reason_ids
        if reason is not None
    }
    for reason in (
        getattr(analysis, "get_decisive_sat_unsafety_reasons", lambda: ())()
    ):
        reason_text = str(reason)
        reason_kind = self._blocking_reason_kind(reason_text)
        if reason_kind in {
            "return_case_coverage_gap",
            "return_case_coverage_inconclusive",
        }:
            continue
        if reason_kind in ignored_reason_kinds:
            continue
        if reason_kind == "return_coverage_gap":
            return UnknownReasonId.RETURN_COVERAGE_GAP
        if reason_kind == "return_coverage_inconclusive":
            return UnknownReasonId.RETURN_COVERAGE_INCONCLUSIVE
        return self._unknown_reason_id_for_blocking_unsafety(reason_text)
    return None

def _impl__make_return_coverage_unknown_reason(
    self,
    typed_reason_id: UnknownReasonId,
    blocking_reason: str,
    analysis1: FunctionReturnAnalysis,
    analysis2: FunctionReturnAnalysis,
    *,
    stage: str,
) -> UnknownReasonRecord:
    object_target_key = self._return_coverage_object_target_key(
        blocking_reason,
        analysis1,
        analysis2,
    )
    kwargs: Dict[str, Any] = {}
    if object_target_key is not None:
        kwargs.update(
            {
                "object_target_key": object_target_key,
                "recovery_action": "return_coverage_proof_required",
                "action_status": UnknownRecoveryActionStatus.PENDING_PROOF,
            }
        )
    return make_unknown_reason(
        typed_reason_id,
        stage=stage,
        evidence_refs=(blocking_reason,),
        detail=blocking_reason,
        **kwargs,
    )

def _impl__unresolved_return_coverage_unknown_reasons(
    self,
    blocking_reasons: Sequence[str],
    analysis1: FunctionReturnAnalysis,
    analysis2: FunctionReturnAnalysis,
    *,
    stage: str,
) -> List[UnknownReasonRecord]:
    unresolved: List[UnknownReasonRecord] = []
    for blocking_reason in blocking_reasons:
        reason_record = self._make_blocking_unsafety_unknown_reason(
            blocking_reason,
            analysis1,
            analysis2,
            stage=stage,
        )
        self._record_completed_call_effect_summary_proof_if_safe(
            reason_record,
            analysis1,
            analysis2,
        )
        if self._recovery_proof_is_complete(
            reason_record,
            analysis1,
            analysis2,
        ):
            continue
        unresolved.append(reason_record)
    return unresolved

def _impl__return_coverage_proof_is_complete(
    self,
    reason_record: UnknownReasonRecord,
    analysis1: FunctionReturnAnalysis,
    analysis2: FunctionReturnAnalysis,
) -> bool:
    if reason_record.reason_id not in (
        UnknownReasonId.RETURN_COVERAGE_GAP.value,
        UnknownReasonId.RETURN_COVERAGE_INCONCLUSIVE.value,
    ):
        return False
    completed = set(self._completed_recovery_proof_ids(analysis1, analysis2))
    required_ids = tuple(
        self._normalize_nested_tuple(action.proof_obligation_id)
        for action in build_unknown_recovery_actions([reason_record])
    )
    if not required_ids or any(proof_id is None for proof_id in required_ids):
        return False
    return all(proof_id in completed for proof_id in required_ids)

def _impl__return_coverage_proof_content_can_discharge_inconclusive(
    cls,
    proof_content: Any,
) -> bool:
    if not isinstance(proof_content, Mapping):
        return False
    solver_evidence = proof_content.get("solver_model_or_timeout")
    if solver_evidence is None:
        return False
    if not isinstance(solver_evidence, Mapping):
        return False
    status = cls._evidence_text(solver_evidence, "status")
    return status in {"complete", "completed", "proven", "unsat", "discharged"}

def _impl__return_coverage_guard_evidence_is_complete(
    cls,
    proof_content: Mapping[str, Any],
    normalized_query: str,
) -> bool:
    guard_evidence = proof_content.get("coverage_guard_evidence")
    if not isinstance(guard_evidence, Mapping):
        return False
    if cls._evidence_text(guard_evidence, "status") not in {"complete", "completed", "proven"}:
        return False
    guard_source = cls._evidence_text(guard_evidence, "guard_source")
    if guard_source not in {
        "case_guard_disjunction",
        "normalized_guard_formula",
        "return_partition_guard_set",
    }:
        return False
    if guard_source != "case_guard_disjunction" and cls._evidence_text(
        guard_evidence,
        "coverage_status",
    ) != "covered":
        return False
    case_count = guard_evidence.get("case_count")
    if not isinstance(case_count, int) or case_count < 0:
        return False
    expected_hash = hashlib.sha256(normalized_query.encode("utf-8")).hexdigest()
    return guard_evidence.get("normalized_guard_formula_sha256") == expected_hash

def _impl__return_coverage_proof_content_is_complete(
    cls,
    evidence: Mapping[str, Any],
    reason_id: Optional[UnknownReasonId] = None,
) -> bool:
    if cls._evidence_get(evidence, "target_schema_version") != cls._RETURN_COVERAGE_TARGET_SCHEMA_VERSION:
        return False
    evidence_schema = cls._evidence_get(evidence, "proof_schema_version")
    if evidence_schema not in {
        cls._RETURN_COVERAGE_PROOF_SCHEMA_VERSION,
        cls._RETURN_COVERAGE_NORMALIZATION_AWARE_PROOF_SCHEMA_VERSION,
    }:
        return False
    if reason_id is not None:
        evidence_reason_id = cls._evidence_text(evidence, "reason_id")
        if evidence_reason_id != reason_id.value:
            return False
    proof_content = cls._evidence_get(evidence, "proof_content")
    if not isinstance(proof_content, Mapping):
        return False
    if reason_id is not None:
        applicable_reason_ids = cls._normalize_nested_tuple(
            cls._evidence_get(evidence, "applicable_reason_ids")
        )
        if applicable_reason_ids is None:
            applicable_reason_ids = cls._normalize_nested_tuple(
                proof_content.get("applicable_reason_ids")
            )
        if applicable_reason_ids is not None and reason_id.value not in set(applicable_reason_ids):
            return False
    evidence_target = cls._normalize_nested_tuple(cls._evidence_get(evidence, "object_target_key"))
    proof_target = cls._normalize_nested_tuple(proof_content.get("proof_target_identity"))
    if proof_target != evidence_target:
        return False
    content_schema = proof_content.get("proof_schema_version")
    if content_schema != evidence_schema:
        return False
    if proof_content.get("normalization_schema_version") != cls._RETURN_COVERAGE_NORMALIZATION_SCHEMA_VERSION:
        return False
    normalization_required = cls._return_coverage_normalization_required(
        evidence,
        proof_content,
        evidence_target,
    )
    if normalization_required and evidence_schema != cls._RETURN_COVERAGE_NORMALIZATION_AWARE_PROOF_SCHEMA_VERSION:
        return False
    if evidence_schema == cls._RETURN_COVERAGE_NORMALIZATION_AWARE_PROOF_SCHEMA_VERSION:
        if not cls._return_coverage_normalization_proof_content_is_complete(
            proof_content,
            evidence_target,
            required=normalization_required,
        ):
            return False
    if not cls._return_coverage_structural_proof_content_is_complete(proof_content):
        return False
    if not cls._return_coverage_structural_proof_content_matches_target(
        proof_content,
        evidence_target,
    ):
        return False
    case_guard_disjunction = proof_content.get("case_guard_disjunction")
    if not isinstance(case_guard_disjunction, Mapping):
        return False
    status = cls._evidence_text(case_guard_disjunction, "status")
    if status not in {"complete", "completed", "proven"}:
        return False
    normalized_guard_formula = proof_content.get("normalized_guard_formula")
    if not isinstance(normalized_guard_formula, Mapping):
        return False
    normalized_status = cls._evidence_text(normalized_guard_formula, "status")
    if normalized_status not in {"complete", "completed", "proven"}:
        return False
    normalized_query = normalized_guard_formula.get("query")
    if not isinstance(normalized_query, str) or not normalized_query:
        return False
    if not cls._return_coverage_guard_evidence_is_complete(proof_content, normalized_query):
        return False
    if reason_id == UnknownReasonId.RETURN_COVERAGE_INCONCLUSIVE:
        if not cls._return_coverage_proof_content_can_discharge_inconclusive(proof_content):
            return False
    else:
        solver_evidence = proof_content.get("solver_model_or_timeout")
        if isinstance(solver_evidence, Mapping):
            solver_status = cls._evidence_text(solver_evidence, "status")
            if solver_status in {"unknown", "timeout", "error", "inconclusive"}:
                return False
    return True

def _impl__return_coverage_normalization_required(
    cls,
    evidence: Mapping[str, Any],
    proof_content: Mapping[str, Any],
    object_target_key: Any,
) -> bool:
    if cls._evidence_bool(evidence, "normalization_required") or bool(
        proof_content.get("normalization_required")
    ):
        return True
    if cls._nested_contains_tag(object_target_key, "normalization_policy_digest"):
        return True
    for key in (
        "normalized_guard_payload",
        "normalized_value_payload",
        "normalized_address_payload",
        "raw_normalized_correspondence",
    ):
        if key in proof_content:
            return True
    return False

def _impl__return_coverage_normalization_proof_content_is_complete(
    cls,
    proof_content: Mapping[str, Any],
    object_target_key: Any,
    *,
    required: bool,
) -> bool:
    policy = proof_content.get("normalization_policy")
    policy_digest = proof_content.get("normalization_policy_digest")
    if not isinstance(policy, Mapping) or not isinstance(policy_digest, str) or not policy_digest:
        return not required
    if cls._return_coverage_normalization_policy_digest(policy) != policy_digest:
        return False
    target_digest = cls._normalization_policy_digest_from_target(object_target_key)
    if target_digest is not None and target_digest != policy_digest:
        return False
    correspondence = proof_content.get("raw_normalized_correspondence")
    if not isinstance(correspondence, Mapping):
        return not required
    if cls._evidence_text(correspondence, "status") not in {"complete", "completed", "proven"}:
        return False
    if correspondence.get("normalization_policy_digest") != policy_digest:
        return False
    raw_identity = cls._normalize_nested_tuple(correspondence.get("raw_guard_identity"))
    normalized_identity = cls._normalize_nested_tuple(correspondence.get("normalized_guard_identity"))
    before_key = cls._normalize_nested_tuple(correspondence.get("before_structural_key"))
    after_key = cls._normalize_nested_tuple(correspondence.get("after_structural_key"))
    if raw_identity is None or normalized_identity is None or before_key is None or after_key is None:
        return False
    if not correspondence.get("rule_id"):
        return False
    equivalence_proof = correspondence.get("equivalence_proof")
    if not isinstance(equivalence_proof, Mapping):
        return False
    if cls._evidence_text(equivalence_proof, "status") not in {"complete", "completed", "proven", "unsat"}:
        return False
    normalized_guard_formula = proof_content.get("normalized_guard_formula")
    if not isinstance(normalized_guard_formula, Mapping):
        return False
    query = normalized_guard_formula.get("query")
    if not isinstance(query, str) or not query:
        return False
    expected_query_hash = hashlib.sha256(query.encode("utf-8")).hexdigest()
    payloads: List[Tuple[str, Mapping[str, Any]]] = []
    for kind, key in (
        ("guard", "normalized_guard_payload"),
        ("value", "normalized_value_payload"),
        ("address", "normalized_address_payload"),
    ):
        payload = proof_content.get(key)
        if payload is None:
            continue
        if not isinstance(payload, Mapping):
            return False
        payloads.append((kind, payload))
    if not payloads:
        return not required
    for kind, payload in payloads:
        if not cls._return_coverage_normalized_payload_is_complete(
            kind,
            payload,
            policy_digest=policy_digest,
            expected_query_hash=expected_query_hash,
            correspondence=correspondence,
            default_raw_identity=raw_identity,
            default_normalized_identity=normalized_identity,
        ):
            return False
    return True

def _impl__return_coverage_normalized_payload_is_complete(
    cls,
    kind: str,
    payload: Mapping[str, Any],
    *,
    policy_digest: str,
    expected_query_hash: str,
    correspondence: Mapping[str, Any],
    default_raw_identity: Any,
    default_normalized_identity: Any,
) -> bool:
    if payload.get("normalization_policy_digest") != policy_digest:
        return False
    payload_raw = cls._normalize_nested_tuple(payload.get("raw_identity"))
    payload_normalized = cls._normalize_nested_tuple(payload.get("normalized_identity"))
    if payload_raw is None or payload_normalized is None:
        return False
    expected_raw = cls._normalize_nested_tuple(correspondence.get(f"raw_{kind}_identity"))
    expected_normalized = cls._normalize_nested_tuple(
        correspondence.get(f"normalized_{kind}_identity")
    )
    if kind == "guard":
        expected_raw = expected_raw if expected_raw is not None else default_raw_identity
        expected_normalized = (
            expected_normalized
            if expected_normalized is not None
            else default_normalized_identity
        )
    elif expected_raw is None or expected_normalized is None:
        return False
    if expected_raw is not None and payload_raw != expected_raw:
        return False
    if expected_normalized is not None and payload_normalized != expected_normalized:
        return False
    final_hash = payload.get("final_query_sha256")
    if not isinstance(final_hash, str) or not final_hash:
        return False
    return final_hash == expected_query_hash

def _impl__return_coverage_structural_proof_content_is_complete(
    cls,
    proof_content: Mapping[str, Any],
) -> bool:
    guard_keys = proof_content.get("structural_guard_keys")
    miss_keys = proof_content.get("structural_miss_formula_keys")
    solver_evidence = proof_content.get("coverage_solver_evidence")
    bit_width_metadata = proof_content.get("bit_width_signedness_metadata")
    if not isinstance(guard_keys, Mapping) or cls._evidence_text(guard_keys, "status") != "complete":
        return False
    if not isinstance(miss_keys, Mapping) or cls._evidence_text(miss_keys, "status") != "complete":
        return False
    if not isinstance(solver_evidence, Mapping):
        return False
    solver_status = cls._evidence_text(solver_evidence, "status")
    proof_method = cls._evidence_text(solver_evidence, "proof_method")
    if solver_status != "unsat" and not (
        solver_status == "not_applicable"
        and proof_method in {"unconditional_return_case", "object_centric_total_coverage"}
    ):
        return False
    if not isinstance(bit_width_metadata, Mapping):
        return False
    if cls._evidence_text(bit_width_metadata, "status") != "complete":
        return False
    guard_key_values = cls._normalize_nested_tuple(guard_keys.get("keys"))
    miss_key_values = cls._normalize_nested_tuple(miss_keys.get("keys"))
    if not isinstance(guard_key_values, tuple) or not guard_key_values:
        return False
    if not isinstance(miss_key_values, tuple) or not miss_key_values:
        return False
    if cls._evidence_has_any_recursive(
        {
            "structural_guard_keys": guard_key_values,
            "structural_miss_formula_keys": miss_key_values,
        },
        cls._COMPLETED_PROOF_BLOCKER_FIELDS,
    ):
        return False
    return True

def _impl__return_coverage_structural_proof_content_matches_target(
    cls,
    proof_content: Mapping[str, Any],
    object_target_key: Any,
) -> bool:
    if not cls._return_coverage_object_target_key_is_valid(object_target_key):
        return False
    target_partition_cases = cls._return_coverage_target_partition_cases(object_target_key)
    if target_partition_cases is None:
        return False
    expected_guard_entries: List[Tuple[Any, ...]] = []
    expected_miss_entries: List[Tuple[Any, ...]] = []
    for case in target_partition_cases:
        fields = {
            field[0]: field[1]
            for field in case[1:]
            if isinstance(field, tuple) and len(field) == 2 and isinstance(field[0], str)
        }
        if "guards" not in fields or "return_value" not in fields or "case_miss_formula" not in fields:
            return False
        expected_guard_entries.append(
            (
                "return_case_guard_set",
                ("guard_structural_keys", cls._normalize_nested_tuple(fields["guards"])),
                ("return_value_structural_key", cls._normalize_nested_tuple(fields["return_value"])),
            )
        )
        expected_miss_entries.append(
            (
                "case_miss_formula",
                cls._normalize_nested_tuple(fields["case_miss_formula"]),
            )
        )

    guard_keys = proof_content.get("structural_guard_keys")
    miss_keys = proof_content.get("structural_miss_formula_keys")
    if not isinstance(guard_keys, Mapping) or not isinstance(miss_keys, Mapping):
        return False
    actual_guard_entries = []
    for entry in cls._normalize_nested_tuple(guard_keys.get("keys")) or ():
        if not isinstance(entry, tuple) or len(entry) < 4 or entry[0] != "return_case_guard_set":
            return False
        fields = {
            field[0]: field[1]
            for field in entry[2:]
            if isinstance(field, tuple) and len(field) == 2 and isinstance(field[0], str)
        }
        if "guard_structural_keys" not in fields or "return_value_structural_key" not in fields:
            return False
        actual_guard_entries.append(
            (
                "return_case_guard_set",
                ("guard_structural_keys", cls._normalize_nested_tuple(fields["guard_structural_keys"])),
                ("return_value_structural_key", cls._normalize_nested_tuple(fields["return_value_structural_key"])),
            )
        )
    actual_miss_entries = []
    for entry in cls._normalize_nested_tuple(miss_keys.get("keys")) or ():
        if not isinstance(entry, tuple) or len(entry) < 3 or entry[0] != "case_miss_formula":
            return False
        actual_miss_entries.append(
            (
                "case_miss_formula",
                cls._normalize_nested_tuple(entry[2]),
            )
        )
    return (
        cls._canonicalize_key_sequence(expected_guard_entries)
        == cls._canonicalize_key_sequence(actual_guard_entries)
        and cls._canonicalize_key_sequence(expected_miss_entries)
        == cls._canonicalize_key_sequence(actual_miss_entries)
    )

def _impl__return_coverage_target_partition_cases(object_target_key: Any) -> Optional[Tuple[Any, ...]]:
    if not isinstance(object_target_key, tuple) or len(object_target_key) < 7:
        return None
    partition = object_target_key[6]
    if not isinstance(partition, tuple) or len(partition) < 3:
        return None
    if partition[0] != "return_partition_identity":
        return None
    cases = partition[2]
    if not isinstance(cases, tuple):
        return None
    for case in cases:
        if not isinstance(case, tuple) or not case or case[0] != "return_case_identity":
            return None
    return cases

def _impl__return_coverage_proof_id_from_evidence(cls, evidence: Any) -> Optional[Tuple[Any, ...]]:
    if not cls._evidence_bool(evidence, "object_derived"):
        return None
    if cls._evidence_text(evidence, "status") not in {"complete", "completed", "proven"}:
        return None
    reason_id = cls._evidence_text(evidence, "reason_id")
    if reason_id not in {
        UnknownReasonId.RETURN_COVERAGE_GAP.value,
        UnknownReasonId.RETURN_COVERAGE_INCONCLUSIVE.value,
    }:
        return None
    canonical_reason_id = None
    try:
        canonical_reason_id = UnknownReasonId(reason_id)
    except ValueError:
        canonical_reason_id = None
    proof_kind = cls._evidence_text(evidence, "recovery_proof_kind")
    if proof_kind != UnknownRecoveryProofKind.RETURN_COVERAGE_COMPLETION.value:
        return None
    proof_stage = cls._evidence_text(evidence, "proof_stage")
    requirements = (
        cls._RETURN_COVERAGE_COMPLETION_REQUIREMENTS.get(canonical_reason_id)
        if canonical_reason_id is not None
        else None
    )
    if not requirements:
        return None
    allowed_stages = {proof_stage_ for proof_stage_, _ in requirements}
    if proof_stage not in allowed_stages:
        return None
    evidence_kind = cls._evidence_text(evidence, "evidence_kind")
    if not evidence_kind:
        return None
    if cls._evidence_has_any(evidence, cls._COMPLETED_PROOF_BLOCKER_FIELDS):
        return None
    object_target_key = cls._normalize_nested_tuple(cls._evidence_get(evidence, "object_target_key"))
    if not isinstance(object_target_key, tuple):
        return None
    if not cls._return_coverage_object_target_key_is_valid(object_target_key):
        return None
    proof_id = build_proof_obligation_id(
        reason_id,
        proof_stage,
        proof_kind,
        evidence_kind,
        object_target_key,
    )
    provided_id = cls._normalize_nested_tuple(cls._evidence_get(evidence, "proof_obligation_id"))
    if provided_id is None or provided_id != proof_id:
        return None
    if not cls._return_coverage_proof_content_is_complete(evidence, canonical_reason_id):
        return None
    return proof_id

def _impl__return_coverage_object_target_key_is_valid(cls, object_target_key: Tuple[Any, ...]) -> bool:
    if not isinstance(object_target_key, tuple) or len(object_target_key) < 8:
        return False
    if object_target_key[0] != "return_coverage":
        return False
    schema = object_target_key[1]
    if not (
        isinstance(schema, tuple)
        and len(schema) == 2
        and schema[0] == "target_schema_version"
        and schema[1] == cls._RETURN_COVERAGE_TARGET_SCHEMA_VERSION
    ):
        return False
    if object_target_key[2] not in {"function1", "function2"}:
        return False
    if not isinstance(object_target_key[3], tuple) or object_target_key[3][0] != "function_identity":
        return False
    if object_target_key[4] not in {"return_coverage_gap", "return_coverage_inconclusive"}:
        return False
    if not isinstance(object_target_key[6], tuple) or object_target_key[6][0] != "return_partition_identity":
        return False
    if not isinstance(object_target_key[7], tuple) or object_target_key[7][0] != "guard_disjunction_identity":
        return False
    return not cls._return_coverage_identity_contains_forbidden_atoms(object_target_key)

def _impl__return_coverage_identity_contains_forbidden_atoms(cls, value: Any) -> bool:
    if isinstance(value, Mapping):
        return True
    if isinstance(value, (list, set, frozenset)):
        return True
    if isinstance(value, tuple):
        if value and value[0] in {"object_id", "program_uid", "opaque"}:
            return True
        if len(value) == 2 and value[0] == "int" and isinstance(value[1], int) and value[1] < 0:
            return False
        return any(cls._return_coverage_identity_contains_forbidden_atoms(item) for item in value)
    if value is None or isinstance(value, str) or isinstance(value, bool):
        return False
    if isinstance(value, int) and not isinstance(value, bool):
        return False
    return True

def _impl__return_coverage_object_target_key(
    self,
    blocking_reason: str,
    analysis1: FunctionReturnAnalysis,
    analysis2: FunctionReturnAnalysis,
) -> Optional[Tuple[Any, ...]]:
    label, _reason_text = self._split_blocking_reason(blocking_reason)
    reason_kind = self._blocking_reason_kind(blocking_reason)
    if reason_kind not in {"return_coverage_gap", "return_coverage_inconclusive"}:
        return None
    analysis = analysis1 if label == "function1" else analysis2 if label == "function2" else None
    if analysis is None:
        return None
    target = (
        "return_coverage",
        ("target_schema_version", self._RETURN_COVERAGE_TARGET_SCHEMA_VERSION),
        label,
        self._deterministic_function_identity(analysis),
        reason_kind,
        self._return_storage_object_key(analysis),
        self._return_coverage_partition_identity_key(analysis),
        self._return_coverage_guard_disjunction_identity_key(analysis),
    )
    return self._identity_freeze(
        self._artifact_stable_key_for_analysis(
            self._identity_freeze(target),
            analysis,
        )
    )

def _impl__outcome_partition_unknown_object_target_key(
    self,
    blocking_reason: str,
    analysis1: FunctionReturnAnalysis,
    analysis2: FunctionReturnAnalysis,
) -> Optional[Tuple[Any, ...]]:
    label, _reason_text = self._split_blocking_reason(blocking_reason)
    reason_kind = self._blocking_reason_kind(blocking_reason)
    if reason_kind != "outcome_partition_completion_unproven" and not reason_kind.startswith("outcome_"):
        return None
    analysis = analysis1 if label == "function1" else analysis2 if label == "function2" else None
    if analysis is None:
        return None
    if reason_kind == "outcome_partition_completion_unproven":
        target = (
            reason_kind,
            ("target_schema_version", 1),
            label,
            self._deterministic_function_identity(analysis),
            self._return_storage_object_key(analysis),
            ("outcome_seed_identity", getattr(getattr(analysis, "outcome_seed", None), "stable_key", lambda: ())()),
        )
    else:
        # Unary blockers deliberately exclude pair-side labels so the same
        # function requirement aggregates across every dependent case pair.
        target = (
            "unary_outcome_partition",
            ("target_schema_version", 1),
            self._deterministic_function_identity(analysis),
            reason_kind,
            ("outcome_seed_identity", getattr(getattr(analysis, "outcome_seed", None), "stable_key", lambda: ())()),
        )
    return self._identity_freeze(
        self._artifact_stable_key_for_analysis(
            self._identity_freeze(target),
            analysis,
        )
    )

def _impl__outcome_partition_unknown_object_evidence(
    self,
    blocking_reason: str,
    analysis1: FunctionReturnAnalysis,
    analysis2: FunctionReturnAnalysis,
) -> Optional[Dict[str, Any]]:
    label, _reason_text = self._split_blocking_reason(blocking_reason)
    analysis = analysis1 if label == "function1" else analysis2 if label == "function2" else None
    if analysis is None:
        return None
    return {
        "object_derived": True,
        "evidence_version": 1,
        "evidence_kind": "outcome_partition",
        "blocker_reason": blocking_reason,
        "side": label,
        "analysis_key": self._analysis_entry_key(analysis),
        "return_storage": self._return_storage_object_key(analysis),
        "outcome_partition": self._outcome_partition_identity_key(analysis),
        "unknown_outcomes": self._unknown_outcome_identity_key(analysis),
    }

def _impl__return_case_partition_member_object_key(
    self,
    case: Any,
    return_info: Any,
) -> Tuple[Any, ...]:
    case_index = getattr(case, "index", None)
    try:
        normalized_case_index = int(case_index)
    except (TypeError, ValueError):
        normalized_case_index = None
    source_indices = []
    for source_index in getattr(case, "source_indices", ()) or ():
        try:
            source_indices.append(int(source_index))
        except (TypeError, ValueError):
            continue
    return (
        "return_case_partition_member",
        normalized_case_index,
        tuple(source_indices),
        self._return_case_object_key(
            normalized_case_index if normalized_case_index is not None else -1,
            return_info,
        )
        if return_info is not None
        else None,
        (
            "comparison_surface",
            getattr(getattr(case, "comparison_surface", None), "kind", None),
            getattr(getattr(case, "comparison_surface", None), "explicit_bit_width", None),
            getattr(getattr(case, "comparison_surface", None), "use_sign_extension", None),
        ),
        ("value", self._expression_runtime_object_key(getattr(case, "value_expr", None))),
    )

def _impl__return_partition_object_key(self, analysis: FunctionReturnAnalysis) -> Tuple[Any, ...]:
    return (
        "return_partition",
        tuple(
            self._return_case_object_key(index, return_info)
            for index, return_info in enumerate(getattr(analysis, "returns", ()) or ())
        ),
    )

def _impl__return_coverage_partition_identity_key(self, analysis: FunctionReturnAnalysis) -> Tuple[Any, ...]:
    cases = tuple(
        self._return_coverage_case_identity_key(return_info)
        for return_info in (getattr(analysis, "returns", ()) or ())
    )
    return (
        "return_partition_identity",
        ("normalization_schema_version", self._RETURN_COVERAGE_NORMALIZATION_SCHEMA_VERSION),
        self._canonicalize_key_sequence(cases),
    )

def _impl__return_coverage_case_identity_key(self, return_info: Any) -> Tuple[Any, ...]:
    pcode_op_ref = getattr(return_info, "pcode_op_ref", None)
    value = getattr(return_info, "value", None)
    conditions = tuple(getattr(return_info, "conditions", None) or ())
    miss_expr = self._case_miss_expression(list(conditions))
    return (
        "return_case_identity",
        ("site", self._identity_freeze(getattr(return_info, "address", None))),
        ("pcode_sequence", self._identity_freeze(self._stable_key_or_none(pcode_op_ref))),
        ("pcode_identity", self._identity_freeze(getattr(return_info, "pcode_identity", None))),
        ("pcode_order", self._identity_freeze(getattr(return_info, "pcode_order", None))),
        ("pcode_time", self._identity_freeze(getattr(return_info, "pcode_time", None))),
        ("return_value", self._expression_runtime_object_key(value)),
        (
            "case_miss_formula",
            self._expression_runtime_object_key(miss_expr) if miss_expr is not None else None,
        ),
        (
            "guards",
            self._canonicalize_key_sequence(
                tuple(
                    self._return_condition_object_key(condition)
                    for condition in conditions
                )
            ),
        ),
        ("bit_width", self._expression_smt_bit_width_for_object_key(value)),
    )

def _impl__return_coverage_guard_disjunction_identity_key(self, analysis: FunctionReturnAnalysis) -> Tuple[Any, ...]:
    guard_sets = tuple(
        (
            "return_case_guard_identity",
            self._canonicalize_key_sequence(
                tuple(
                    self._return_condition_object_key(condition)
                    for condition in (getattr(return_info, "conditions", None) or ())
                )
            ),
        )
        for return_info in (getattr(analysis, "returns", ()) or ())
    )
    return (
        "guard_disjunction_identity",
        ("normalization_schema_version", self._RETURN_COVERAGE_NORMALIZATION_SCHEMA_VERSION),
        self._canonicalize_key_sequence(guard_sets),
    )

def _impl__outcome_partition_identity_key(self, analysis: FunctionReturnAnalysis) -> Tuple[Any, ...]:
    return_outcomes = tuple(getattr(analysis, "return_outcomes", ()) or ())
    divergence_outcomes = tuple(getattr(analysis, "divergence_outcomes", ()) or ())
    unknown_outcomes = tuple(getattr(analysis, "unknown_outcomes", ()) or ())
    return_keys = tuple(
        (
            "return",
            index,
            self._canonicalize_key_sequence(
                tuple(self._return_condition_object_key(condition) for condition in (getattr(outcome, "guard", ()) or ()))
            ),
            self._expression_runtime_object_key(getattr(outcome, "value", None)),
            self._identity_freeze(getattr(outcome, "provenance", None)),
        )
        for index, outcome in enumerate(return_outcomes)
    )
    divergence_keys = tuple(
        (
            "divergence",
            index,
            self._canonicalize_key_sequence(
                tuple(self._return_condition_object_key(condition) for condition in (getattr(outcome, "guard", ()) or ()))
            ),
            self._identity_freeze(getattr(outcome, "proof", None)),
        )
        for index, outcome in enumerate(divergence_outcomes)
    )
    unknown_keys = tuple(
        self._unknown_outcome_member_identity_key(index, outcome)
        for index, outcome in enumerate(unknown_outcomes)
    )
    return (
        "outcome_partition_identity",
        ("normalization_schema_version", self._RETURN_COVERAGE_NORMALIZATION_SCHEMA_VERSION),
        self._canonicalize_key_sequence(return_keys),
        self._canonicalize_key_sequence(divergence_keys),
        self._canonicalize_key_sequence(unknown_keys),
    )

def _impl__unknown_outcome_identity_key(self, analysis: FunctionReturnAnalysis) -> Tuple[Any, ...]:
    return (
        "unknown_outcomes",
        self._canonicalize_key_sequence(
            tuple(
                self._unknown_outcome_member_identity_key(index, outcome)
                for index, outcome in enumerate(getattr(analysis, "unknown_outcomes", ()) or ())
            )
        ),
    )

def _impl__unknown_outcome_member_identity_key(self, index: int, outcome: Any) -> Tuple[Any, ...]:
    return (
        "unknown_outcome",
        int(index),
        ("reason", str(getattr(outcome, "reason", "") or "")),
        (
            "guard",
            self._canonicalize_key_sequence(
                tuple(self._return_condition_object_key(condition) for condition in (getattr(outcome, "guard", ()) or ()))
            ),
        ),
        ("evidence", self._identity_freeze(getattr(outcome, "evidence", None))),
    )

def _impl__outcome_partition_covered_labels(
    self,
    base_ctx: Mapping[str, Any],
    analysis1: Optional[FunctionReturnAnalysis],
    analysis2: Optional[FunctionReturnAnalysis],
    param_replace_fn1,
    param_replace_fn2,
) -> Set[str]:
    if analysis1 is None or analysis2 is None:
        return set()
    if (
        getattr(self, "_obligation_runtime_session", None) is not None
        and (
            getattr(analysis1, "outcome_seed", None) is not None
            or getattr(analysis2, "outcome_seed", None) is not None
        )
    ):
        blockers = {}
        proofs_complete = True
        left_proof = _prove_unary_outcome_for_analysis(
            self, base_ctx, analysis1, param_replace_fn1
        )
        right_proof = _prove_unary_outcome_for_analysis(
            self, base_ctx, analysis2, param_replace_fn2
        )
        for label, analysis, proof in (
            ("function1", analysis1, left_proof),
            ("function2", analysis2, right_proof),
        ):
            if proof is None or not proof.complete:
                proofs_complete = False
                # Do not add a redundant outcome backlog when extraction has
                # already established that the function-level semantic surface
                # is incomplete.  The unary proof still fails and cannot cover
                # the label; the pre-existing extraction/unsafety reason owns
                # recovery until that prerequisite is repaired.
                has_unresolved_return = getattr(analysis, "has_unresolved_return_value", None)
                independently_incomplete = bool(
                    getattr(analysis, "incomplete_control_flow", False)
                    or (callable(has_unresolved_return) and has_unresolved_return())
                )
                if not independently_incomplete:
                    blockers[label] = getattr(proof, "blocker_kind", None) or "outcome_unary_artifact_missing"
        self._last_unary_outcome_blockers = blockers
        if not proofs_complete:
            return set()
        if not self._outcome_partitions_are_equivalent(
            base_ctx, analysis1, analysis2, param_replace_fn1, param_replace_fn2
        ):
            self._last_unary_outcome_blockers = {
                "function1": "outcome_relational_consistency_unknown",
                "function2": "outcome_relational_consistency_unknown",
            }
            return set()
        return {"function1", "function2"}
    if not self._analysis_has_proved_outcome_partition(
        base_ctx,
        analysis1,
        param_replace_fn1,
        "function1",
    ):
        self._debug_print("Outcome partition coverage declined: function1 partition is not proved total")
        return set()
    if not self._analysis_has_proved_outcome_partition(
        base_ctx,
        analysis2,
        param_replace_fn2,
        "function2",
    ):
        self._debug_print("Outcome partition coverage declined: function2 partition is not proved total")
        return set()
    if not self._outcome_partitions_are_equivalent(
        base_ctx,
        analysis1,
        analysis2,
        param_replace_fn1,
        param_replace_fn2,
    ):
        self._debug_print("Outcome partition coverage declined: partitions are not equivalent")
        return set()
    return {"function1", "function2"}

RELATIONAL_OUTCOME_PARTITION_BLOCKER = "outcome_relational_consistency_unknown"


def _impl__sat_decisive_return_coverage_unsafety_reasons(
    self,
    coverage_unsafety_reasons: Sequence[str],
) -> List[str]:
    """Return the coverage reasons that must also block a decisive SAT.

    ``_outcome_partition_covered_labels`` reports
    ``outcome_relational_consistency_unknown`` only after both unary outcome
    proofs are complete and merely the cross-function relation (return values
    equal under overlapping guards, matching divergence/termination regions)
    could not be established.  That relation is exactly what an equivalence
    closure needs, so it keeps blocking EQUIVALENT; but for two functions that
    really differ it fails by construction, and it says nothing about whether
    a replayed SAT witness is genuine.  Unary blockers (incomplete path
    regions, unclassified members, ...) stay SAT-blocking (Issue #28).
    """
    unary_blockers = getattr(self, "_last_unary_outcome_blockers", {}) or {}
    relational_labels = {
        label
        for label, blocker in unary_blockers.items()
        if blocker == RELATIONAL_OUTCOME_PARTITION_BLOCKER
    }
    kept: List[str] = []
    for reason in coverage_unsafety_reasons:
        label, _, reason_id = str(reason).partition(":")
        if (
            label in relational_labels
            and reason_id == "outcome_partition_completion_unproven"
        ):
            self._debug_print(
                f"  SAT decisiveness keeps {label}: relational outcome-partition "
                "mismatch blocks EQUIVALENT only (unary partition proofs are complete)"
            )
            continue
        kept.append(reason)
    return kept


def _impl__outcome_partition_inconclusive_labels(
    self,
    base_ctx: Mapping[str, Any],
    analysis1: Optional[FunctionReturnAnalysis],
    analysis2: Optional[FunctionReturnAnalysis],
    param_replace_fn1,
    param_replace_fn2,
) -> Set[str]:
    labels: Set[str] = set()
    unary_blockers = getattr(self, "_last_unary_outcome_blockers", {}) or {}
    for label, analysis, replace_fn in (
        ("function1", analysis1, param_replace_fn1),
        ("function2", analysis2, param_replace_fn2),
    ):
        if analysis is None:
            continue
        if getattr(analysis, "outcome_seed", None) is not None and label in unary_blockers:
            labels.add(label)
            continue
        if not getattr(analysis, "unknown_outcomes", ()) or ():
            continue
        if self._analysis_has_total_outcome_partition(
            base_ctx,
            analysis,
            replace_fn,
            label,
        ):
            labels.add(label)
    return labels

def _impl__analysis_has_total_outcome_partition(
    self,
    base_ctx: Mapping[str, Any],
    analysis: FunctionReturnAnalysis,
    replace_fn,
    label: str,
) -> bool:
    return_outcomes = tuple(getattr(analysis, "return_outcomes", ()) or ())
    divergence_outcomes = tuple(getattr(analysis, "divergence_outcomes", ()) or ())
    unknown_outcomes = tuple(getattr(analysis, "unknown_outcomes", ()) or ())
    outcome_guards = [
        tuple(getattr(outcome, "guard", ()) or ())
        for outcome in (*return_outcomes, *divergence_outcomes, *unknown_outcomes)
    ]
    if not outcome_guards:
        return False
    return self._outcome_guard_union_is_total(
        base_ctx,
        outcome_guards,
        replace_fn,
        label,
    )

def _impl__analysis_has_proved_outcome_partition(
    self,
    base_ctx: Mapping[str, Any],
    analysis: FunctionReturnAnalysis,
    replace_fn,
    label: str,
) -> bool:
    if getattr(analysis, "unknown_outcomes", ()) or ():
        return False
    seed = getattr(analysis, "outcome_seed", None)
    if seed is not None and getattr(self, "_obligation_runtime_session", None) is not None:
        # Semantic seeds are candidates only.  The production gate must never
        # infer proof completion from candidate booleans or guard unions.
        # A later branch consumes only imported validated unary artifacts.
        return False
    return_outcomes = tuple(getattr(analysis, "return_outcomes", ()) or ())
    divergence_outcomes = tuple(getattr(analysis, "divergence_outcomes", ()) or ())
    if not divergence_outcomes:
        return False
    return self._outcome_guard_union_is_total(
        base_ctx,
        [tuple(getattr(outcome, "guard", ()) or ()) for outcome in (*return_outcomes, *divergence_outcomes)],
        replace_fn,
        label,
    )

def _impl__outcome_partitions_are_equivalent(
    self,
    base_ctx: Mapping[str, Any],
    analysis1: FunctionReturnAnalysis,
    analysis2: FunctionReturnAnalysis,
    param_replace_fn1,
    param_replace_fn2,
) -> bool:
    divergence1 = tuple(getattr(analysis1, "divergence_outcomes", ()) or ())
    divergence2 = tuple(getattr(analysis2, "divergence_outcomes", ()) or ())
    returns1 = tuple(getattr(analysis1, "return_outcomes", ()) or ())
    returns2 = tuple(getattr(analysis2, "return_outcomes", ()) or ())
    seed1 = getattr(analysis1, "outcome_seed", None)
    seed2 = getattr(analysis2, "outcome_seed", None)
    def termination_groups(seed):
        groups = {}
        if seed is None:
            return groups
        terminals = {
            tuple(item.candidate_id): item
            for item in (getattr(seed, "terminal_candidates", ()) or ())
        }
        for region in (getattr(seed, "symbolic_regions", ()) or ()):
            terminal = terminals.get(tuple(region.terminal_candidate_id))
            contract = getattr(terminal, "termination_contract", None) if terminal is not None else None
            if contract is None:
                continue
            signature = (
                contract.termination_class,
                tuple(contract.payload_key),
                tuple(contract.effect_key),
                tuple(contract.observation_contract_key),
            )
            groups.setdefault(signature, []).append(region)
        return {key: tuple(value) for key, value in groups.items()}
    termination1 = termination_groups(seed1)
    termination2 = termination_groups(seed2)
    if seed1 is not None and not returns1:
        terminal_kinds = {tuple(item.candidate_id): item.terminal_kind_candidate for item in seed1.terminal_candidates}
        returns1 = tuple(
            region for region in seed1.symbolic_regions
            if terminal_kinds.get(tuple(region.terminal_candidate_id)) == "return"
        )
    if seed2 is not None and not returns2:
        terminal_kinds = {tuple(item.candidate_id): item.terminal_kind_candidate for item in seed2.terminal_candidates}
        returns2 = tuple(
            region for region in seed2.symbolic_regions
            if terminal_kinds.get(tuple(region.terminal_candidate_id)) == "return"
        )
    if bool(divergence1) != bool(divergence2):
        self._debug_print("Outcome partition equivalence declined: one-sided divergence outcomes")
        return False
    if set(termination1) != set(termination2):
        self._debug_print("Outcome partition equivalence declined: termination contracts differ")
        return False
    for signature in termination1:
        if not self._outcome_guard_unions_equivalent(
            base_ctx,
            [tuple(region.guard) for region in termination1[signature]],
            [tuple(region.guard) for region in termination2[signature]],
            param_replace_fn1,
            param_replace_fn2,
        ):
            self._debug_print("Outcome partition equivalence declined: termination regions differ")
            return False
    if divergence1 and not self._outcome_guard_unions_equivalent(
        base_ctx,
        [tuple(getattr(outcome, "guard", ()) or ()) for outcome in divergence1],
        [tuple(getattr(outcome, "guard", ()) or ()) for outcome in divergence2],
        param_replace_fn1,
        param_replace_fn2,
    ):
        self._debug_print("Outcome partition equivalence declined: divergence guard unions differ")
        return False
    if not self._outcome_cross_kind_disjoint(
        base_ctx,
        returns1,
        divergence2,
        param_replace_fn1,
        param_replace_fn2,
    ):
        self._debug_print("Outcome partition equivalence declined: function1 returns overlap function2 divergence")
        return False
    flat_termination1 = tuple(region for regions in termination1.values() for region in regions)
    flat_termination2 = tuple(region for regions in termination2.values() for region in regions)
    for left_members, right_members, left_replace, right_replace in (
        (returns1, flat_termination2, param_replace_fn1, param_replace_fn2),
        (returns2, flat_termination1, param_replace_fn2, param_replace_fn1),
        (divergence1, flat_termination2, param_replace_fn1, param_replace_fn2),
        (divergence2, flat_termination1, param_replace_fn2, param_replace_fn1),
    ):
        if not self._outcome_cross_kind_disjoint(
            base_ctx, left_members, right_members, left_replace, right_replace
        ):
            self._debug_print("Outcome partition equivalence declined: cross-side termination overlap")
            return False
    if not self._outcome_cross_kind_disjoint(
        base_ctx,
        returns2,
        divergence1,
        param_replace_fn2,
        param_replace_fn1,
    ):
        self._debug_print("Outcome partition equivalence declined: function2 returns overlap function1 divergence")
        return False
    if not self._return_outcome_values_are_equivalent(
        base_ctx,
        returns1,
        returns2,
        param_replace_fn1,
        param_replace_fn2,
    ):
        self._debug_print("Outcome partition equivalence declined: return outcome values differ")
        return False
    return True

def _impl__return_outcome_values_are_equivalent(
    self,
    base_ctx: Mapping[str, Any],
    returns1: Sequence[Any],
    returns2: Sequence[Any],
    param_replace_fn1,
    param_replace_fn2,
) -> bool:
    for left in returns1 or ():
        left_guard = tuple(getattr(left, "guard", ()) or ())
        left_value = getattr(left, "value", None)
        if left_value is None:
            left_value = getattr(left, "observed_value", None)
        if left_value is None:
            return False
        for right in returns2 or ():
            right_guard = tuple(getattr(right, "guard", ()) or ())
            right_value = getattr(right, "value", None)
            if right_value is None:
                right_value = getattr(right, "observed_value", None)
            if right_value is None:
                return False
            if self._outcome_condition_groups_are_unsat(
                base_ctx,
                ((left_guard, param_replace_fn1), (right_guard, param_replace_fn2)),
                title="Outcome return guard overlap",
            ):
                continue
            if not self._outcome_return_values_equal_under_guards(
                base_ctx,
                left_guard,
                right_guard,
                left_value,
                right_value,
                param_replace_fn1,
                param_replace_fn2,
            ):
                return False
    return True

def _impl__outcome_cross_kind_disjoint(
    self,
    base_ctx: Mapping[str, Any],
    return_outcomes: Sequence[Any],
    divergence_outcomes: Sequence[Any],
    return_replace_fn,
    divergence_replace_fn,
) -> bool:
    for ret in return_outcomes or ():
        ret_guard = tuple(getattr(ret, "guard", ()) or ())
        for divergence in divergence_outcomes or ():
            div_guard = tuple(getattr(divergence, "guard", ()) or ())
            if not self._outcome_condition_groups_are_unsat(
                base_ctx,
                ((ret_guard, return_replace_fn), (div_guard, divergence_replace_fn)),
                title="Outcome return/divergence disjointness",
            ):
                return False
    return True

def _impl__outcome_guard_unions_equivalent(
    self,
    base_ctx: Mapping[str, Any],
    left_guards: Sequence[Sequence[Condition]],
    right_guards: Sequence[Sequence[Condition]],
    left_replace_fn,
    right_replace_fn,
) -> bool:
    left_union = self._outcome_guard_union_smt(left_guards, left_replace_fn)
    right_union = self._outcome_guard_union_smt(right_guards, right_replace_fn)
    if left_union is None or right_union is None:
        return False

    left_implies_right = self._outcome_smt_assertions_are_unsat(
        base_ctx,
        [left_union, f"(not {right_union})"],
        title="Outcome divergence guard implication left-to-right",
    )
    right_implies_left = self._outcome_smt_assertions_are_unsat(
        base_ctx,
        [right_union, f"(not {left_union})"],
        title="Outcome divergence guard implication right-to-left",
    )
    return left_implies_right and right_implies_left

def _impl__outcome_guard_union_is_total(
    self,
    base_ctx: Mapping[str, Any],
    guard_sets: Sequence[Sequence[Condition]],
    replace_fn,
    label: str,
) -> bool:
    """渡された region guard の和が恒真かを判定する補助検査。

    Issue #131: これが True でも、元の展開が上限で切り捨てられていれば区画全体の
    complete／covered は成立しない。切り捨ては ``path_region_completeness``
    producer が先に未完了へ倒す（この関数を弱めて補うことはしない）。
    """

    union = self._outcome_guard_union_smt(guard_sets, replace_fn)
    if union is None:
        return False
    return self._outcome_smt_assertions_are_unsat(
        base_ctx,
        [f"(not {union})"],
        title=f"Outcome partition total coverage: {label}",
    )

def _impl__outcome_condition_groups_are_unsat(
    self,
    base_ctx: Mapping[str, Any],
    condition_groups: Sequence[Tuple[Sequence[Condition], Any]],
    *,
    title: str,
) -> bool:
    assertions: List[str] = []
    for conditions, replace_fn in condition_groups:
        rendered = self._outcome_conditions_smt(conditions, replace_fn)
        if rendered is None:
            return False
        assertions.extend(rendered)
    return self._outcome_smt_assertions_are_unsat(base_ctx, assertions, title=title)

def _impl__outcome_return_values_equal_under_guards(
    self,
    base_ctx: Mapping[str, Any],
    left_guard: Sequence[Condition],
    right_guard: Sequence[Condition],
    left_value: Expression,
    right_value: Expression,
    left_replace_fn,
    right_replace_fn,
) -> bool:
    left_conditions = self._outcome_conditions_smt(left_guard, left_replace_fn)
    right_conditions = self._outcome_conditions_smt(right_guard, right_replace_fn)
    if left_conditions is None or right_conditions is None:
        return False
    left_smt = self._outcome_expression_smt(left_value, left_replace_fn)
    right_smt = self._outcome_expression_smt(right_value, right_replace_fn)
    if left_smt is None or right_smt is None:
        return False
    left_bits = int(expression_smt_bit_width(left_value) or 0)
    right_bits = int(expression_smt_bit_width(right_value) or 0)
    if left_bits <= 0 or right_bits <= 0:
        return False
    target_bits = max(left_bits, right_bits)
    left_smt = coerce_value_to_bitvec_width(left_value, left_smt, target_bits)
    right_smt = coerce_value_to_bitvec_width(right_value, right_smt, target_bits)
    return self._outcome_smt_assertions_are_unsat(
        base_ctx,
        [*left_conditions, *right_conditions, f"(not (= {left_smt} {right_smt}))"],
        title="Outcome return value equality",
    )

def _impl__outcome_guard_union_smt(
    self,
    guard_sets: Sequence[Sequence[Condition]],
    replace_fn,
) -> Optional[str]:
    disjuncts: List[str] = []
    for guards in guard_sets or ():
        rendered = self._outcome_conditions_smt(guards, replace_fn)
        if rendered is None:
            return None
        if not rendered:
            return "true"
        if len(rendered) == 1:
            disjuncts.append(rendered[0])
        else:
            disjuncts.append(f"(and {' '.join(rendered)})")
    if not disjuncts:
        return None
    if len(disjuncts) == 1:
        return disjuncts[0]
    return f"(or {' '.join(disjuncts)})"

def _impl__outcome_conditions_smt(
    self,
    conditions: Sequence[Condition],
    replace_fn,
) -> Optional[List[str]]:
    rendered: List[str] = []
    for condition in conditions or ():
        smt = self._outcome_condition_smt(condition, replace_fn)
        if smt is None:
            return None
        rendered.append(smt)
    return rendered

def _impl__outcome_condition_smt(self, condition: Condition, replace_fn) -> Optional[str]:
    try:
        if replace_fn is None:
            return condition.to_smt(float_mode="fp")
        return replace_fn(condition)
    except TypeError:
        try:
            return replace_fn(condition.to_smt(float_mode="fp"))
        except Exception:
            return None
    except Exception:
        return None

def _impl__outcome_expression_smt(self, expression: Expression, replace_fn) -> Optional[str]:
    try:
        if replace_fn is None:
            return expression.to_smt(float_mode="fp")
        return replace_fn(expression)
    except TypeError:
        try:
            return replace_fn(expression.to_smt(float_mode="fp"))
        except Exception:
            return None
    except Exception:
        return None

def _impl__outcome_smt_assertions_are_unsat(
    self,
    base_ctx: Mapping[str, Any],
    assertions: Sequence[str],
    *,
    title: str,
) -> bool:
    header_lines = list(base_ctx.get("header_lines", []) or []) if isinstance(base_ctx, Mapping) else []
    if not header_lines:
        return False
    if not assertions:
        return False
    normalized_assertions = self._normalize_zero_constant_widths_for_declared_symbols(
        assertions,
        header_lines,
    )
    query = "\n".join(
        [
            f"; {title}",
            *header_lines,
            *(f"(assert {assertion})" for assertion in normalized_assertions),
            "(check-sat)",
            "(get-model)",
        ]
    )
    result = self.solver_runner.run_sequential(query)
    return result.is_equivalent is True

def _impl__check_return_case_coverage_gap(
    self,
    base_ctx: Dict[str, Any],
    cases: Sequence[Any],
    param_replace_fn,
    label: str,
) -> ReturnCoverageCheckResult:
    if not cases:
        return ReturnCoverageCheckResult(
            status="gap",
            detail=f"{label} has no return cases after extraction",
        )
    if any(not getattr(case, "conditions", None) for case in cases):
        return ReturnCoverageCheckResult(
            status="covered",
            coverage_proof_method="unconditional_return_case",
        )
    object_centric_status = self._return_cases_have_object_centric_total_coverage(
        cases
    )
    if object_centric_status is True:
        return ReturnCoverageCheckResult(
            status="covered",
            coverage_proof_method="object_centric_total_coverage",
        )
    if object_centric_status is False and not self._base_context_has_return_coverage_domain_assumptions(base_ctx):
        return ReturnCoverageCheckResult(
            status="gap",
            detail=f"{label} object-centric return-case coverage check found uncovered region",
        )
    if object_centric_status is None:
        case_conditions = [
            cond
            for case in (cases or ())
            for cond in (getattr(case, "conditions", None) or ())
        ]
        if not ConditionSMTOracle.has_object_identity_support(case_conditions):
            return ReturnCoverageCheckResult(
                status="inconclusive",
                reason_id=UnknownReasonId.RETURN_COVERAGE_INCONCLUSIVE,
                detail=f"{label} return-case object-centric coverage check was inconclusive",
                inconclusive_cause="object_identity_unsupported",
            )
    if not base_ctx.get("header_lines"):
        return ReturnCoverageCheckResult(
            status="inconclusive",
            reason_id=UnknownReasonId.RETURN_COVERAGE_INCONCLUSIVE,
            detail=f"{label} return-case coverage query skipped: base context has no declarations",
            inconclusive_cause="missing_header_context",
        )
    if any(self._case_conditions_contain_unresolved_expression(case) for case in cases):
        return ReturnCoverageCheckResult(
            status="inconclusive",
            reason_id=UnknownReasonId.RETURN_COVERAGE_INCONCLUSIVE,
            detail=f"{label} return-case coverage query skipped: unresolved condition expression",
            inconclusive_cause="expression_translation_incomplete",
        )

    query = self._build_return_case_coverage_query(
        base_ctx,
        cases,
        param_replace_fn,
        label,
    )
    if query is None:
        return ReturnCoverageCheckResult(
            status="inconclusive",
            reason_id=UnknownReasonId.RETURN_COVERAGE_INCONCLUSIVE,
            detail=f"{label} return-case coverage query could not be built",
            inconclusive_cause="unsupported_expression",
        )

    result = self.solver_runner.run_sequential(query)
    if result.is_equivalent is False:
        model = result.get_counterexample()
        detail = f"{label} has uncovered return-condition region"
        if model:
            detail += f" under model {model}"
        if getattr(self, "debug", False):
            detail += self._return_coverage_case_debug_suffix(cases)
        return ReturnCoverageCheckResult(status="gap", detail=detail)
    if result.is_equivalent is None:
        return ReturnCoverageCheckResult(
            status="inconclusive",
            reason_id=UnknownReasonId.RETURN_COVERAGE_INCONCLUSIVE,
            detail=f"{label} return-case coverage query was inconclusive",
            can_record_completion_proof=True,
            inconclusive_cause="smt_disambiguation_inconclusive",
        )
    return ReturnCoverageCheckResult(
        status="covered",
        coverage_proof_method="smt_coverage_query",
        solver_status="unsat",
    )

def _impl__return_coverage_case_debug_suffix(self, cases: Sequence[Any]) -> str:
    lines: List[str] = []
    for case in cases or ():
        case_index = getattr(case, "index", "?")
        rendered_conditions = []
        for condition in getattr(case, "conditions", []) or []:
            to_string = getattr(condition, "to_string", None)
            if callable(to_string):
                try:
                    rendered_conditions.append(to_string())
                    continue
                except Exception:
                    pass
            rendered_conditions.append(repr(condition))
        lines.append(f"case[{case_index}] conditions={rendered_conditions}")
    if not lines:
        return ""
    return "\n  coverage cases:\n  " + "\n  ".join(lines)

def _impl__base_context_has_return_coverage_domain_assumptions(
    base_ctx: Mapping[str, Any],
) -> bool:
    assumptions = base_ctx.get("return_coverage_domain_assumptions")
    if not isinstance(assumptions, Mapping):
        return False
    return bool(assumptions.get("fp_non_nan"))

def _impl__return_cases_have_object_centric_total_coverage(
    self,
    cases: Sequence[Any],
) -> Optional[bool]:
    """観測済みケース集合が全体であることを前提にした網羅性判定。

    Issue #131: **生存 guard の OR が恒真であることは、元の展開が完全である
    ことの証明ではない。** 展開ケース数・経路数の上限で捨てられたケースがあると、
    その guard が生存ケースの短い guard に包含されているだけで covered になり得る。
    切り捨ての有無は ``FunctionReturnAnalysis.has_expansion_budget_truncation()``
    が持ち、呼び出し側（``_impl__collect_return_coverage_unsafety_reasons`` と
    ``path_region_completeness`` producer）がここへ来る前に inconclusive へ倒す。
    ここでは「入力のケース集合が打ち切りなしで生成されている」ことを前提とする。
    """
    if not cases:
        return False
    if any(not getattr(case, "conditions", None) for case in cases):
        return True
    case_conditions = [
        condition
        for case in cases
        for condition in (getattr(case, "conditions", None) or ())
    ]
    if not ConditionSMTOracle.has_object_identity_support(case_conditions):
        return None
    smt_result = self._return_cases_have_smt_total_coverage(cases)
    if smt_result is not None:
        return smt_result
    return None

def _impl__return_cases_have_smt_total_coverage(
    self,
    cases: Sequence[Any],
) -> Optional[bool]:
    """Prove coverage from Condition objects without rendered-query plumbing.

    A coverage gap exists iff every return case can be missed at once.
    For a case with conditions c1..cn, the case is missed by
    (not c1) or ... or (not cn).  If the conjunction of all case-miss
    formulas is UNSAT, the return partition is total.

    Issue #131: この「全体」は渡されたケース集合に対する全体であって、元の展開が
    完全であることの証明ではない。生存 guard の OR が恒真でも、上限で捨てられた
    ケースがあれば覆えていない入力領域が残り得る。切り捨ての有無は呼び出し側が
    先に判定する。
    """

    miss_conditions: List[Condition] = []
    for case in cases or ():
        conditions = list(getattr(case, "conditions", None) or [])
        if not conditions:
            return True
        miss_expr = self._case_miss_expression(conditions)
        if miss_expr is None:
            return None
        miss_conditions.append(Condition(miss_expr, False))
    if not miss_conditions:
        return False
    return ConditionSMTOracle.conjunction_is_unsat(miss_conditions)

def _impl__build_return_case_coverage_query(
    self,
    base_ctx: Dict[str, Any],
    cases: Sequence[Any],
    param_replace_fn,
    label: str,
) -> Optional[str]:
    disjuncts: List[str] = []
    for case in cases:
        conditions = list(getattr(case, "get_conditions_smt")(param_replace_fn))
        if not conditions:
            return None
        if len(conditions) == 1:
            disjuncts.append(conditions[0])
        else:
            disjuncts.append(f"(and {' '.join(conditions)})")

    if not disjuncts:
        return None

    lines = [
        f"; Return coverage gap query: {label}",
        *base_ctx.get("header_lines", []),
        f"(assert (not (or {' '.join(disjuncts)})))",
        "(check-sat)",
        "(get-model)",
    ]
    return "\n".join(lines)

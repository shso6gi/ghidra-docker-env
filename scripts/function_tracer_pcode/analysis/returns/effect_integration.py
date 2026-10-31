"""Stateless method implementations extracted from ``scripts.function_tracer_pcode.analysis.returns.analyzer``."""

from __future__ import annotations

from typing import Any, Callable, Dict, Iterable, List, Optional, Sequence, Set, TYPE_CHECKING, Tuple
from dataclasses import replace
from scripts.function_tracer_pcode.core.analysis import (
    ComparisonSurface,
    FunctionReturnAnalysis,
    ReturnInfo,
)
from scripts.function_tracer_pcode.core.call_target import CallTargetRef
from scripts.function_tracer_pcode.core.expression import Condition, Expression, ExpressionType
from scripts.function_tracer_pcode.core.runtime_refs import (
    ExpansionBudgetCollector,
    PcodeBlockRef,
    PcodeOpRef,
    PostStateValueRef,
    merge_expansion_budget_truncations,
)
from scripts.function_tracer_pcode.core.structural import StructuralKey
from scripts.function_tracer_pcode.analysis.returns.region_facts import input_is_nondata_operand
from scripts.function_tracer_pcode.analysis.returns._shared import (
    ConditionSimplifier,
    EffectSummary,
    FunctionControlEffectProfile,
    PcodeTracer,
    _EffectRewritePrecision,
    _FUNCTION_PROFILE_RECOGNIZED_PCODE_MNEMONICS,
    _PHASE2_MEMORY_FREE_SCALAR_PCODE_MNEMONICS,
    _TrackedReturnValue,
    _expression_contains_observed_loads,
    _expression_reads_location,
    _expressions_equivalent,
    _expressions_equivalent_under_conditions,
    _find_matching_effect_value,
    _find_unique_effect_location_for_value,
    _iter_expression_nodes,
    _materialize_existing_effect_value_carrier,
    _replay_definite_active_effects_for_location,
    _strip_materialized_post_state_value_refs,
    canonicalize_expr_read_location,
    concretize_readonly_loads,
    expression_contains_post_state_reads,
    expression_matches_stale_post_state_replay,
    lower_post_state_expression_for_smt,
    materialize_definite_post_state_expression,
    normalize_post_state_expression,
    promote_effect_value_carrier_to_post_state_read,
    promote_effect_value_match_to_post_state_read,
    promote_observed_loads_to_post_state_reads,
    resolve_definite_post_state_read_for_location,
    rewrite_loads_from_effects,
    rewrite_observed_loads_from_effects,
    summarize_store_effects,
)
from scripts.function_tracer_pcode.analysis.effects._shared import (
    _EFFECT_GLOBAL_READ_IDENTITY_REASON,
    _EFFECT_SURFACE_COMPOSITION_REASON,
)
from scripts.function_tracer_pcode.analysis.effects.summary import expression_reads_unidentified_writable_memory
from scripts.function_tracer_pcode.analysis.effects.external_call_models import resolve_effect_callee
from scripts.function_tracer_pcode.analysis.session import AnalysisSession
from scripts.function_tracer_pcode.analysis.runtime_state import AnalysisRuntimeState
from scripts.function_tracer_pcode.analysis.returns.lifecycle import ProgramAccessService
from scripts.function_tracer_pcode.analysis.returns.lifecycle import collect_java_or_python_iterable
from scripts.function_tracer_pcode.analysis.returns.lifecycle import function_cache_key as lifecycle_function_cache_key
from scripts.function_tracer_pcode.analysis.returns.expansion_budget import (
    callee_reference_truncation,
    make_expansion_budget_sink,
    mark_effect_expansion_case_budget_exceeded,
)
from scripts.function_tracer_pcode.analysis.returns.debug_reporter import DebugReporter
from scripts.function_tracer_pcode.analysis.returns._api import ConditionTracker
from scripts.function_tracer_pcode.analysis.returns.expression_cases import ExpressionCaseService
from scripts.function_tracer_pcode.analysis.returns.return_normalization import ReturnNormalizationService
from scripts.function_tracer_pcode.analysis.returns.pcode_sites import PcodeSiteService
from scripts.function_tracer_pcode.analysis.returns.phi_origins import PhiOriginService
from scripts.function_tracer_pcode.analysis.returns.divergence_proofs import DivergenceProofService
from scripts.function_tracer_pcode.analysis.returns.parameters import ParameterService
from scripts.function_tracer_pcode.analysis.returns.region_facts import RegionFacts
from scripts.function_tracer_pcode.analysis.debug import bounded_enumerate, summarize_conditions

if TYPE_CHECKING:  # local_values は本 module の local_memory_key を import するため循環回避
    from scripts.function_tracer_pcode.analysis.returns.local_values import LocalValueResolver


def local_memory_key(addr_expr: Expression, size: int) -> Tuple[StructuralKey, int]:
    """Structural cache key of a local memory access (pure; no facade state)."""
    key_expr = (
        addr_expr.operands[0]
        if getattr(addr_expr, "expr_type", None) == ExpressionType.MEMORY
        and getattr(addr_expr, "operands", None)
        else addr_expr
    )
    return (
        key_expr.structural_key(
            normalize_commutative=True,
            strip_width_adapters=True,
            collapse_full_masks=True,
        ),
        int(size),
    )


OBSERVABLE_EFFECT_SURFACE_SOURCE = "observable_effects_and_return_value"


def _incomplete_reason_tuple(effect_summary: Any) -> Tuple[str, ...]:
    reasons = getattr(effect_summary, "incomplete_reasons", ())
    if not isinstance(reasons, (list, tuple, set, frozenset)):
        return ()
    return tuple(reasons)


def observable_store_effects(effect_summary: Any) -> List[Any]:
    """Stores a caller can observe: through parameter pointers or globals.

    Stack-frame stores die with the frame and are not part of the observable
    behaviour; everything else (parameter-based, storage/global) is.
    """
    observable: List[Any] = []
    for effect in getattr(effect_summary, "effects", None) or ():
        location = getattr(effect, "location", None)
        base_ref = getattr(location, "base_ref", None)
        if getattr(base_ref, "kind", None) == "stack_frame":
            continue
        observable.append(effect)
    return observable


class EffectIntegrationService:
    """ReturnAnalyzer から切り出した effect summary 統合（構築・キャッシュ・effect-sensitive 書き換え・観測面適用）の collaborator。

    per-analysis state: ``AnalysisSession`` を返す ``session`` supplier を 1 本保持し、呼び出し時に
    ``self.session().parameters`` / ``self.session().effect_summary`` を読む（nested ``_analysis_context`` の
    push/pop に追随する）。
    analyzer-lifetime mutable state: ``AnalysisRuntimeState`` owner を ``runtime_state`` 直接依存として保持し、
    effect summary の 2 キャッシュ・直接呼び出しグラフ・完了ノード集合は ``self.runtime_state.<field>`` で owner 経由で
    都度読み、その container を in-place 更新する。owner の identity は固定するが各 field は都度参照するため、
    facade property による field object の差し替えには追随する。
    configuration: ``program`` / ``binary_id`` / ``debug`` フラグは従来どおり supplier 境界。
    既存 collaborator（式ケース・条件正規化・p-code site・PHI 起源・発散証明・パラメータ・
    RegionFacts・LocalValueResolver）は直接依存。未抽出 family（lifecycle / call_recovery / return_extraction）が
    所有する helper は facade 経由で遅延 dispatch する callable として注入する。
    ``local_memory_key`` / ``observable_store_effects`` は module 関数のまま据え置く。
    """

    def __init__(
        self,
        *,
        runtime_state: "AnalysisRuntimeState",
        session: Callable[[], "AnalysisSession"],
        program_access: ProgramAccessService,
        expression_cases: ExpressionCaseService,
        return_normalization: ReturnNormalizationService,
        pcode_sites: PcodeSiteService,
        phi_origins: PhiOriginService,
        divergence_proofs: DivergenceProofService,
        parameters: ParameterService,
        region_facts: RegionFacts,
        local_values: "LocalValueResolver",
        debug_reporter: DebugReporter,
        extend_active_functions: Callable[..., Any],
        current_function_entry_address: Callable[..., Any],
        analysis_scope_key: Callable[..., Any],
        get_freshest_callee_parameters: Callable[..., Any],
        make_call_resolver: Callable[..., Any],
        bound_parameter_values_from_call_args: Callable[..., Any],
        bound_parameter_storage_values_from_call_args: Callable[..., Any],
        target_active_key: Callable[..., Any],
        resolve_target_function: Callable[..., Any],
        make_deferred_call_recorder: Callable[..., Any],
        is_semantically_lossless_effect_sensitive_rewrite: Callable[..., Any],
        direct_call_target_function_key: Callable[..., Any],
        coerce_runtime_target_ref: Callable[..., Any],
        make_tracked_return_value: Callable[..., Any],
        function_body_has_phase1_pure_return_forbidden_ops: Callable[..., Any],
        high_function_has_phase1_pure_return_forbidden_ops: Callable[..., Any],
        phase1_return_type_is_float: Callable[..., Any],
        decompile_with_broker: Callable[..., Any],
        program_value: Callable[..., Any],
        binary_id_value: Callable[..., Any],
        debug_flag: Callable[..., Any],
        external_call_effect_policy: Callable[..., Any],
    ) -> None:
        self.runtime_state = runtime_state
        self.session = session
        self.program_access = program_access
        self.expression_cases = expression_cases
        self.return_normalization = return_normalization
        self.pcode_sites = pcode_sites
        self.phi_origins = phi_origins
        self.divergence_proofs = divergence_proofs
        self.parameters = parameters
        self.region_facts = region_facts
        self.local_values = local_values
        self.debug_reporter = debug_reporter
        self.extend_active_functions = extend_active_functions
        self.current_function_entry_address = current_function_entry_address
        self.analysis_scope_key = analysis_scope_key
        self.get_freshest_callee_parameters = get_freshest_callee_parameters
        self.make_call_resolver = make_call_resolver
        self.bound_parameter_values_from_call_args = bound_parameter_values_from_call_args
        self.bound_parameter_storage_values_from_call_args = bound_parameter_storage_values_from_call_args
        self.target_active_key = target_active_key
        self.resolve_target_function = resolve_target_function
        self.make_deferred_call_recorder = make_deferred_call_recorder
        self.is_semantically_lossless_effect_sensitive_rewrite = is_semantically_lossless_effect_sensitive_rewrite
        self.direct_call_target_function_key = direct_call_target_function_key
        self.coerce_runtime_target_ref = coerce_runtime_target_ref
        self.make_tracked_return_value = make_tracked_return_value
        self.function_body_has_phase1_pure_return_forbidden_ops = function_body_has_phase1_pure_return_forbidden_ops
        self.high_function_has_phase1_pure_return_forbidden_ops = high_function_has_phase1_pure_return_forbidden_ops
        self.phase1_return_type_is_float = phase1_return_type_is_float
        self.decompile_with_broker = decompile_with_broker
        self.program_value = program_value
        self.binary_id_value = binary_id_value
        self.debug_flag = debug_flag
        self.external_call_effect_policy = external_call_effect_policy

    def effect_summary_allows_pre_return_structural_summary(
        self,
        effect_summary: Optional[EffectSummary],
        *,
        function=None,
        high_function=None,
        return_type: Optional[str] = None,
        return_type_obj=None,
    ) -> bool:
        if effect_summary is None:
            return False
        if self.phase1_return_type_is_float(return_type, return_type_obj):
            self.debug_reporter.debug_print("Declined pre-return counted loop summary: Phase 1 excludes FP return types")
            return False
        if self.function_body_has_phase1_pure_return_forbidden_ops(function):
            self.debug_reporter.debug_print(
                "Declined pre-return counted loop summary: function body is not Phase 1 pure/no-memory"
            )
            return False
        if self.high_function_has_phase1_pure_return_forbidden_ops(high_function):
            self.debug_reporter.debug_print(
                "Declined pre-return counted loop summary: HighFunction-visible body is not Phase 1 pure/no-memory"
            )
            return False
        if getattr(effect_summary, "effects", None):
            self.debug_reporter.debug_print("Declined pre-return counted loop summary: effect summary contains memory writes")
            return False
        if getattr(effect_summary, "has_unsupported_call", False):
            self.debug_reporter.debug_print("Declined pre-return counted loop summary: effect summary contains unsupported call")
            return False
        return True

    def build_function_control_effect_profile(
        self,
        high_function,
        function=None,
        parameters: Optional[Sequence[Dict[str, Any]]] = None,
    ) -> FunctionControlEffectProfile:
        """Conservatively census CFG/P-code for direct-call eligibility."""

        function_identity_key = None
        if function is not None:
            try:
                function_identity_key = CallTargetRef.from_function(function).stable_key()
            except Exception:
                function_identity_key = None

        blocks, blocks_complete = collect_java_or_python_iterable(
            getattr(high_function, "getBasicBlocks", lambda: None)()
            if high_function is not None
            and callable(getattr(high_function, "getBasicBlocks", None))
            else None
        )
        adjacency: Dict[int, Tuple[int, ...]] = {}
        block_keys_by_index: Dict[int, Tuple[object, ...]] = {}
        block_refs_by_index: Dict[int, PcodeBlockRef] = {}
        terminal_return_indices: Set[int] = set()
        pcode_complete = bool(blocks_complete)
        edges_complete = bool(blocks_complete)
        terminal_coverage_complete = bool(blocks_complete and blocks)
        pcode_op_count = 0
        return_block_count = 0
        counts = {
            "LOAD": 0,
            "STORE": 0,
            "CALL": 0,
            "CALLIND": 0,
            "CALLOTHER": 0,
            "BRANCHIND": 0,
        }
        float_op_count = 0
        pcode_after_return_count = 0
        abnormal_terminal_block_count = 0
        call_like_pcode_op_keys: List[Tuple[object, ...]] = []
        call_like_identity_complete = bool(blocks_complete)
        direct_call_target_keys: List[Tuple[object, ...]] = []
        call_graph_edges_complete = bool(blocks_complete and function_identity_key is not None)
        phase2_unsafe: Set[str] = set()
        region_pcode_op_keys: List[Tuple[object, ...]] = []
        region_live_in_keys: Set[Tuple[object, ...]] = set()
        region_live_out_keys: Set[Tuple[object, ...]] = set()
        region_identity_complete = bool(blocks_complete and function_identity_key is not None)
        unsupported: Set[str] = set()
        function_entry_address = None
        if function is not None:
            try:
                function_entry_address = function.getEntryPoint()
            except Exception:
                function_entry_address = None
        if function_entry_address is None:
            function_entry_address = self.current_function_entry_address()
        try:
            function_entry_space = function_entry_address.getAddressSpace().getName()
            function_entry_offset = int(function_entry_address.getOffset())
        except Exception:
            function_entry_space = None
            function_entry_offset = None

        for ordinal, block in enumerate(blocks):
            try:
                block_index = int(block.getIndex())
            except Exception:
                block_index = ordinal
                edges_complete = False
            try:
                start = block.getStart()
                start_space = start.getAddressSpace().getName()
                start_offset = int(start.getOffset())
            except Exception:
                start_space = None
                start_offset = None
                region_identity_complete = False
            block_keys_by_index[block_index] = (
                "pcode_block",
                self.binary_id_value(),
                function_identity_key,
                block_index,
                start_space,
                start_offset,
            )
            block_refs_by_index[block_index] = PcodeBlockRef(
                block_index=block_index,
                start_address_offset=start_offset,
                binary_id=self.binary_id_value(),
                function_entry_space=function_entry_space,
                function_entry_offset=function_entry_offset,
            )
            successors: List[int] = []
            try:
                out_size = int(block.getOutSize())
            except Exception:
                out_size = 0
                edges_complete = False
            for out_index in range(max(0, out_size)):
                try:
                    successors.append(int(block.getOut(out_index).getIndex()))
                except Exception:
                    edges_complete = False
            adjacency[block_index] = tuple(successors)

            ops, complete = collect_java_or_python_iterable(
                getattr(block, "getIterator", lambda: None)()
            )
            pcode_complete = pcode_complete and complete
            saw_return = False
            if not complete:
                terminal_coverage_complete = False
            for local_ordinal, op in enumerate(ops):
                pcode_op_count += 1
                try:
                    mnemonic = str(op.getMnemonic() or "").strip().upper()
                except Exception:
                    mnemonic = ""
                region_ref = PcodeOpRef.from_pcode_op(
                    op,
                    binary_id=self.binary_id_value(),
                    program_uid=self.program_access.program_identity(),
                    function_entry=self.current_function_entry_address(),
                    local_op_ordinal=local_ordinal,
                )
                if region_ref is None:
                    region_identity_complete = False
                else:
                    region_pcode_op_keys.append(region_ref.stable_key())
                try:
                    num_inputs = int(op.getNumInputs())
                except Exception:
                    num_inputs = 0
                    region_identity_complete = False
                for input_index in range(max(0, num_inputs)):
                    try:
                        input_varnode = op.getInput(input_index)
                    except Exception:
                        region_identity_complete = False
                        continue
                    input_key, input_status = self.region_facts.live_in_key(
                        input_varnode,
                        mnemonic=mnemonic,
                        input_index=input_index,
                        parameters=parameters or (),
                    )
                    if input_status == "incomplete":
                        region_identity_complete = False
                    elif input_key is not None:
                        region_live_in_keys.add(tuple(input_key))
                if not mnemonic:
                    unsupported.add("<missing_mnemonic>")
                    continue
                if mnemonic not in _FUNCTION_PROFILE_RECOGNIZED_PCODE_MNEMONICS:
                    unsupported.add(mnemonic)
                elif mnemonic not in _PHASE2_MEMORY_FREE_SCALAR_PCODE_MNEMONICS:
                    phase2_unsafe.add(mnemonic)
                if mnemonic in counts:
                    counts[mnemonic] += 1
                if saw_return:
                    pcode_after_return_count += 1
                    unsupported.add(f"<op_after_return:{mnemonic}>")
                if mnemonic in {"CALL", "CALLIND", "CALLOTHER"}:
                    ref = PcodeOpRef.from_pcode_op(
                        op,
                        binary_id=self.binary_id_value(),
                        program_uid=self.program_access.program_identity(),
                        function_entry=self.current_function_entry_address(),
                        local_op_ordinal=local_ordinal,
                    )
                    if ref is None:
                        call_like_identity_complete = False
                    else:
                        call_like_pcode_op_keys.append(ref.stable_key())
                if mnemonic == "CALL":
                    target_key = self.direct_call_target_function_key(op)
                    if target_key is None:
                        call_graph_edges_complete = False
                    else:
                        direct_call_target_keys.append(target_key)
                elif mnemonic in {"CALLIND", "CALLOTHER"}:
                    call_graph_edges_complete = False
                if "FLOAT" in mnemonic or mnemonic in {"INT2FLOAT", "FLOAT2INT"}:
                    float_op_count += 1
                if mnemonic == "RETURN":
                    saw_return = True
                    for input_index in range(max(0, num_inputs)):
                        if input_is_nondata_operand(mnemonic, input_index):
                            continue
                        try:
                            return_input = op.getInput(input_index)
                            if bool(return_input.isConstant()):
                                continue
                            output_key = self.pcode_sites.varnode_location_key(return_input)
                        except Exception:
                            output_key = None
                        if output_key is not None:
                            region_live_out_keys.add(
                                ("return_value", input_index - 1, tuple(output_key))
                            )
            if not successors:
                if saw_return:
                    return_block_count += 1
                    terminal_return_indices.add(block_index)
                else:
                    terminal_coverage_complete = False
                    abnormal_terminal_block_count += 1

        visiting: Set[int] = set()
        visited: Set[int] = set()

        def has_cycle(node: int) -> bool:
            if node in visiting:
                return True
            if node in visited:
                return False
            visiting.add(node)
            for successor in adjacency.get(node, ()):
                if successor not in adjacency:
                    nonlocal_edges_complete[0] = False
                    continue
                if has_cycle(successor):
                    return True
            visiting.remove(node)
            visited.add(node)
            return False

        nonlocal_edges_complete = [edges_complete]
        cfg_acyclic = bool(blocks_complete)
        for node in adjacency:
            if has_cycle(node):
                cfg_acyclic = False
                break
        edges_complete = nonlocal_edges_complete[0]
        predecessor_counts = {index: 0 for index in adjacency}
        for successors in adjacency.values():
            for successor in successors:
                if successor in predecessor_counts:
                    predecessor_counts[successor] += 1
        entry_indices = tuple(
            index for index, count in predecessor_counts.items() if count == 0
        )
        region_single_entry = len(entry_indices) == 1
        region_entry_block_key = (
            block_keys_by_index.get(entry_indices[0]) if region_single_entry else None
        )
        region_exit_block_keys = tuple(
            block_keys_by_index[index]
            for index in sorted(terminal_return_indices)
            if index in block_keys_by_index
        )
        region_identity_complete = bool(
            region_identity_complete
            and pcode_complete
            and edges_complete
            and len(block_keys_by_index) == len(blocks)
            and len(region_pcode_op_keys) == pcode_op_count
        )

        if function_identity_key is not None:
            self.runtime_state.direct_call_graph[function_identity_key] = set(direct_call_target_keys)
            if call_graph_edges_complete and pcode_complete:
                self.runtime_state.direct_call_graph_complete_nodes.add(function_identity_key)
            else:
                self.runtime_state.direct_call_graph_complete_nodes.discard(function_identity_key)
        recursive_scc_proven, recursive_scc_identity, recursive_scc_members = (
            self.divergence_proofs.recursive_scc_certificate(function_identity_key)
        )
        region_cfg_edge_keys = tuple(
            (
                block_refs_by_index[source].stable_key(),
                block_refs_by_index[target].stable_key(),
            )
            for source in sorted(adjacency)
            for target in sorted(adjacency[source])
            if source in block_refs_by_index and target in block_refs_by_index
        )

        return FunctionControlEffectProfile(
            block_count=len(blocks),
            pcode_op_count=pcode_op_count,
            return_block_count=return_block_count,
            pcode_enumeration_complete=pcode_complete,
            cfg_edges_complete=edges_complete,
            cfg_acyclic=cfg_acyclic,
            terminal_return_coverage_complete=terminal_coverage_complete,
            load_count=counts["LOAD"],
            store_count=counts["STORE"],
            call_count=counts["CALL"],
            callind_count=counts["CALLIND"],
            callother_count=counts["CALLOTHER"],
            branchind_count=counts["BRANCHIND"],
            float_op_count=float_op_count,
            pcode_after_return_count=pcode_after_return_count,
            abnormal_terminal_block_count=abnormal_terminal_block_count,
            call_like_pcode_op_keys=tuple(call_like_pcode_op_keys),
            call_like_identity_complete=(
                call_like_identity_complete and pcode_complete
            ),
            function_identity_key=function_identity_key,
            direct_call_target_keys=tuple(direct_call_target_keys),
            call_graph_edges_complete=(call_graph_edges_complete and pcode_complete),
            recursive_scc_proven=recursive_scc_proven,
            recursive_scc_identity=recursive_scc_identity,
            recursive_scc_member_keys=recursive_scc_members,
            phase2_unsafe_mnemonics=tuple(sorted(phase2_unsafe)),
            region_entry_block_key=region_entry_block_key,
            region_exit_block_keys=region_exit_block_keys,
            region_block_keys=tuple(
                block_keys_by_index[index] for index in sorted(block_keys_by_index)
            ),
            region_cfg_edge_keys=region_cfg_edge_keys,
            region_pcode_op_keys=tuple(region_pcode_op_keys),
            region_live_in_keys=tuple(sorted(region_live_in_keys, key=repr)),
            region_live_out_keys=tuple(sorted(region_live_out_keys, key=repr)),
            region_identity_complete=region_identity_complete,
            region_single_entry=region_single_entry,
            region_all_exits_enumerated=bool(
                edges_complete and terminal_coverage_complete
            ),
            region_cross_edges_enumerated=bool(edges_complete),
            unsupported_mnemonics=tuple(sorted(unsupported)),
        )

    def make_empty_effect_summary(
        self,
        parameters: List[Dict],
    ) -> EffectSummary:
        parameter_names = [
            str(name)
            for param in (parameters or [])
            for name in [param.get("name")]
            if isinstance(name, str) and name
        ]
        return EffectSummary(parameter_names=parameter_names, effects=[])

    def propagate_indirect_return_effect(
        self,
        tracked: _TrackedReturnValue,
        pcode_op,
        tracer: Optional[PcodeTracer],
    ) -> List[_TrackedReturnValue]:
        try:
            base_input = pcode_op.getInput(0)
        except Exception:
            return []

        # Ghidra の INDIRECT は input0 が 0 の場合、
        # 出力が「副作用 op によってのみ生成された値」であることを表す。
        # この場合は return storage 自体を追跡し続ける。
        if self.pcode_sites.is_zero_constant_varnode(base_input):
            return [tracked]

        if base_input is None:
            return []
        return [self.make_tracked_return_value(base_input, tracer)]

    def invoke_build_effect_summary(
        self,
        function,
        high_function,
        tracer: PcodeTracer,
        condition_tracker: ConditionTracker,
        parameters: List[Dict],
        active_functions: Set[Tuple[Any, ...]],
        *,
        bound_parameter_values: Optional[Dict[int, Expression]] = None,
        bound_parameter_storage_values: Optional[Dict[Tuple[Any, ...], Expression]] = None,
    ):
        try:
            return self.build_effect_summary(
                function,
                high_function,
                tracer,
                condition_tracker,
                parameters,
                active_functions=active_functions,
                bound_parameter_values=bound_parameter_values,
                bound_parameter_storage_values=bound_parameter_storage_values,
            )
        except TypeError:
            return self.build_effect_summary(
                function,
                high_function,
                tracer,
                condition_tracker,
                parameters,
                active_functions=active_functions,
            )

    def build_effect_summary(
        self,
        function,
        high_function,
        tracer: PcodeTracer,
        condition_tracker: ConditionTracker,
        parameters: List[Dict],
        active_functions: Set[Tuple[Any, ...]],
        bound_parameter_values: Optional[Dict[int, Expression]] = None,
        bound_parameter_storage_values: Optional[Dict[Tuple[Any, ...], Expression]] = None,
    ):
        function_cache_key = lifecycle_function_cache_key(function)
        if function_cache_key is None:
            return None
        self.runtime_state.effect_summary_parameter_cache[function_cache_key] = list(parameters)
        summary_cache_key = self.analysis_scope_key(
            function,
            bound_parameter_values,
            bound_parameter_storage_values,
        )
        cached = self.runtime_state.effect_summary_cache.get(summary_cache_key)
        if cached is not None:
            return cached

        # Issue #131: この効果要約 1 件分の局所 collector。``_analysis_context`` が押す
        # 子 session に依存せず、要約の scope で切り捨てを集める。callee 由来は
        # ``callee_analysis`` 参照だけを持ち、本体は callee 側の entry に残る。
        budget_collector = ExpansionBudgetCollector()

        def summarize_call(target, args):
            target_ref = self.coerce_runtime_target_ref(target)
            if target_ref is None:
                return None
            active_key = self.target_active_key(target_ref)
            if active_key is not None and active_key in active_functions:
                return None
            callee = self.resolve_target_function(target_ref)
            if callee is None:
                return None
            # Issue #104 (Gap 4): an external / thunk callee has no body in
            # this binary.  Its empty HighFunction must not read as "no
            # effect": follow a thunk to its internal body, or fail closed
            # (``callee_effect_summary_missing``).  There is no name-based
            # effect model for externals.
            callee_resolution = resolve_effect_callee(
                callee,
                self.external_call_effect_policy(),
                parameter_names=(),
            )
            if callee_resolution.kind != "analyze":
                self.debug_reporter.debug_print(
                    f"[EffectSummary] external callee not summarised: "
                    f"{callee_resolution.external_name} ({callee_resolution.reason})"
                )
                return None
            callee = callee_resolution.function
            callee_parameters_for_binding = self.get_freshest_callee_parameters(target_ref)
            callee_bound_parameter_values = self.bound_parameter_values_from_call_args(
                args,
                callee_parameters_for_binding,
            )
            callee_bound_parameter_storage_values = self.bound_parameter_storage_values_from_call_args(
                args,
                callee_parameters_for_binding,
            )
            callee_scope_key = self.analysis_scope_key(
                callee,
                callee_bound_parameter_values,
                callee_bound_parameter_storage_values,
            )
            if callee_scope_key is None:
                return None
            cached_callee = self.runtime_state.effect_summary_cache.get(callee_scope_key)
            if cached_callee is not None:
                # cache hit でも採用した callee の切り捨て参照は失わない（保存済み
                # 診断が空/欠落なら marker は作らない）。
                budget_collector.record(
                    callee_reference_truncation(
                        self.runtime_state.effect_summary_budget_diagnostics.get(
                            callee_scope_key
                        )
                        or (),
                        callee_scope_key=callee_scope_key,
                        owner_scope_key=summary_cache_key,
                        label=target_ref.display_name(),
                    )
                )
                return cached_callee

            from scripts.function_tracer_pcode.ghidra.decompilation_broker import EFFECT_SUMMARY_SOURCE_CONTRACT
            # broker は analyzer（facade）を第 1 引数に取るため、facade 経由の callable で呼ぶ
            results = self.decompile_with_broker(
                callee, 60, None,
                source_contract_id=EFFECT_SUMMARY_SOURCE_CONTRACT,
                semantic_owner="subordinate",
            )
            if not results.decompileCompleted():
                return None
            callee_high = results.getHighFunction()
            if callee_high is None:
                return None

            fresh_callee_parameters = self.parameters.collect_parameters(callee_high)
            callee_parameters = self.parameters.choose_richer_parameter_descriptors(
                callee_parameters_for_binding,
                fresh_callee_parameters,
            )
            callee_bound_parameter_values = self.bound_parameter_values_from_call_args(
                args,
                callee_parameters,
            )
            callee_bound_parameter_storage_values = self.bound_parameter_storage_values_from_call_args(
                args,
                callee_parameters,
            )
            callee_tracer = self.program_access.make_tracer(
                callee_high,
                bound_parameter_values=callee_bound_parameter_values,
                bound_parameter_storage_values=callee_bound_parameter_storage_values,
            )
            callee_tracer.record_deferred_call = self.make_deferred_call_recorder(
                callee, program_order=getattr(callee_tracer, "program_order", None)
            )
            callee_tracker = ConditionTracker(callee_tracer)
            callee_tracer.condition_tracker = callee_tracker
            from scripts.function_tracer_pcode.analysis.phi_resolver import PhiHandler

            callee_phi_handler = PhiHandler(callee_tracer, callee_tracker)
            callee_tracer.phi_handler = callee_phi_handler
            callee_tracker.build()
            callee_function_cache_key = lifecycle_function_cache_key(callee)
            if callee_function_cache_key is not None:
                self.runtime_state.effect_summary_parameter_cache[callee_function_cache_key] = list(callee_parameters)
            image_base = None
            try:
                image_base = self.program_value().getImageBase().getOffset()
            except Exception:
                image_base = None
            # Issue #131: この経路には通常の子 ``AnalysisSession`` が無い。callee の
            # 分岐条件 refinement と STORE 展開の両方を、callee 要約と同じ key の
            # 診断へ集約する（refinement は要約構築の外で走るため局所 collector 経由）。
            callee_summary_cache_key = self.analysis_scope_key(
                callee,
                callee_bound_parameter_values,
                callee_bound_parameter_storage_values,
            )
            callee_refinement_collector = ExpansionBudgetCollector()
            callee_tracker.refine_branch_conditions(
                call_resolver=self.make_call_resolver(
                    self.extend_active_functions(active_functions, target_ref),
                    callee,
                    budget_collector=callee_refinement_collector,
                    budget_owner_scope_key=callee_summary_cache_key,
                ),
                parameters=callee_parameters,
                resolve_callee_parameters=self.get_freshest_callee_parameters,
                read_memory_value=self.read_memory_value,
                image_base=image_base,
                budget_sink=make_expansion_budget_sink(
                    callee_refinement_collector,
                    surface="branch_condition",
                    owner_scope_key=callee_summary_cache_key,
                ),
            )
            summary = self.invoke_build_effect_summary(
                callee,
                callee_high,
                callee_tracer,
                callee_tracker,
                callee_parameters,
                self.extend_active_functions(active_functions, target_ref),
                bound_parameter_values=callee_bound_parameter_values,
                bound_parameter_storage_values=callee_bound_parameter_storage_values,
            )
            if summary is not None and callee_summary_cache_key is not None:
                # 要約構築側が同じ key の診断を置き換えた後に、refinement 分を足す。
                diagnostics = self.runtime_state.effect_summary_budget_diagnostics
                diagnostics[callee_summary_cache_key] = merge_expansion_budget_truncations(
                    diagnostics.get(callee_summary_cache_key) or (),
                    callee_refinement_collector.as_tuple(),
                )
                # Issue #131 PR-B: refinement は要約構築の外で走るので、その分の
                # 切り捨ては要約自身の不完全性としてもここで残す（診断 dict が
                # 失われても、cache 済み要約から不完全性を復元できるようにする）。
                if callee_refinement_collector:
                    mark_effect_expansion_case_budget_exceeded(summary)
                budget_collector.record(
                    callee_reference_truncation(
                        diagnostics.get(callee_summary_cache_key) or (),
                        callee_scope_key=callee_summary_cache_key,
                        owner_scope_key=summary_cache_key,
                        label=target_ref.display_name(),
                    )
                )
            return summary

        def resolve_callee_parameters(target):
            return self.get_freshest_callee_parameters(target)

        current_target = CallTargetRef.from_function(function)
        # Register outgoing direct-call edges before recursive summary descent;
        # recompute the certificate after descent when more graph nodes exist.
        self.build_function_control_effect_profile(high_function, function, parameters)
        image_base = None
        try:
            image_base = self.program_value().getImageBase().getOffset()
        except Exception:
            image_base = None
        summary = summarize_store_effects(
            condition_tracker.block_by_index.values(),
            tracer,
            condition_tracker,
            parameters,
            direct_call_summary=summarize_call,
            # Issue #131: STORE 値展開が CALL を解決して callee 解析を採用した場合の
            # marker は、周囲の AnalysisSession ではなくこの要約の collector へ入れる
            # （下で summary_cache_key の診断 cache に保存される）。
            direct_call_expander=self.make_call_resolver(
                self.extend_active_functions(active_functions, current_target),
                function,
                budget_collector=budget_collector,
                budget_owner_scope_key=summary_cache_key,
            ),
            resolve_callee_parameters=resolve_callee_parameters,
            read_memory_value=self.read_memory_value,
            image_base=image_base,
            debug=self.debug_flag(),
            budget_sink=make_expansion_budget_sink(
                budget_collector,
                surface="store_value",
                owner_scope_key=summary_cache_key,
            ),
        )
        summary.function_control_effect_profile = self.build_function_control_effect_profile(
            high_function,
            function,
            parameters,
        )
        # Issue #131 PR-B: 効果面の切り捨ては要約自身の不完全性として残す。
        # 診断 dict は破棄・欠落し得るが、この reason は要約と一緒に cache へ入るので、
        # cache hit でも不完全性が失われない（診断欠落から推定はしない）。
        if budget_collector:
            mark_effect_expansion_case_budget_exceeded(summary)
        self.runtime_state.effect_summary_cache[summary_cache_key] = summary
        # 再構築なので古い診断は残さず置き換える（切り捨てが無ければ空になる）。
        # 寿命と key は ``effect_summary_cache`` に揃える。
        self.runtime_state.effect_summary_budget_diagnostics[summary_cache_key] = (
            budget_collector.as_tuple()
        )
        return summary

    def local_memory_key(self, addr_expr: Expression, size: int) -> Tuple[StructuralKey, int]:
        return local_memory_key(addr_expr, size)

    def apply_local_store_effect(
        self,
        pcode_op,
        tracer,
        local_values: Dict[Tuple[str, int, int], Expression],
        local_storages: Dict[Tuple[str, int, int], Any],
        local_memory: Dict[Tuple[StructuralKey, int], Expression],
    ) -> None:
        if pcode_op.getNumInputs() < 3:
            return
        addr_expr = self.local_values.evaluate_varnode(
            pcode_op.getInput(1),
            tracer,
            local_values,
            local_storages,
            local_memory,
        )
        value_expr = self.local_values.evaluate_varnode(
            pcode_op.getInput(2),
            tracer,
            local_values,
            local_storages,
            local_memory,
        )
        size = pcode_op.getInput(2).getSize()
        local_memory[self.local_memory_key(addr_expr, size)] = value_expr

    def split_effect_sensitive_return_case(
        self,
        value: Expression,
        conditions: List[Condition],
    ) -> List[Tuple[Expression, List[Condition]]]:
        effect_summary = self.session().effect_summary
        if effect_summary is None or not effect_summary.effects:
            return [(value, conditions)]

        rewritten = self.rewrite_effect_sensitive_return_value(
            value,
            conditions,
            effect_summary,
        )
        if self.debug_flag() and rewritten is not None and not _expressions_equivalent(rewritten, value):
            self.debug_reporter.debug_print(
                "Effect-sensitive rewrite candidate: "
                f"{self.debug_reporter.debug_expr_details_summary(value)} -> "
                f"{self.debug_reporter.debug_expr_details_summary(rewritten)}"
            )
        if rewritten is None or _expressions_equivalent(rewritten, value):
            return [(value, conditions)]

        expanded = self.expression_cases.expand_object_centric_expression_cases(
            rewritten,
            conditions,
        )
        if not expanded:
            return [(value, conditions)]
        expanded = [
            (
                self.collapse_effect_sensitive_case_wrapper(
                    value,
                    case_value,
                    case_conditions,
                    effect_summary,
                ),
                case_conditions,
            )
            for case_value, case_conditions in expanded
        ]

        deduplicated = self.expression_cases.deduplicate_expression_cases(expanded)
        if self.debug_flag() and deduplicated:
            for case_index, (case_value, case_conditions) in bounded_enumerate(deduplicated):
                cond_dump = summarize_conditions(case_conditions)
                self.debug_reporter.debug_print(
                    "  effect-sensitive case "
                    f"[{case_index}]: {self.debug_reporter.debug_expr_details_summary(case_value)}"
                )
                self.debug_reporter.debug_print(f"    conditions={cond_dump}")
        if (
            len(deduplicated) == 1
            and _expressions_equivalent(deduplicated[0][0], value)
            and self.expression_cases.condition_lists_equivalent(deduplicated[0][1], conditions)
        ):
            return [(value, conditions)]

        if self.debug_flag() and len(deduplicated) > 1:
            self.debug_reporter.debug_print(
                "Split effect-sensitive expanded return into "
                f"{len(deduplicated)} object-centric cases: "
                f"{self.debug_reporter.debug_expr_summary(value)} -> {self.debug_reporter.debug_expr_summary(rewritten)}"
            )
        return deduplicated

    def rewrite_effect_sensitive_return_value(
        self,
        value: Expression,
        conditions: List[Condition],
        effect_summary: EffectSummary,
    ) -> Optional[Expression]:
        precise_object_state_value = self.expression_cases.resolve_precise_object_state_value(
            value,
            conditions,
            effect_summary,
        )
        if precise_object_state_value is not None and precise_object_state_value is not value:
            if self.debug_flag():
                self.debug_reporter.debug_print(
                    "Resolved return to precise object-state carrier before generic rewrite: "
                    f"{self.debug_reporter.debug_expr_details_summary(value)} -> "
                    f"{self.debug_reporter.debug_expr_details_summary(precise_object_state_value)}"
                )
            return precise_object_state_value

        for rewrite_kind, rewritten in self.iter_effect_sensitive_rewrite_candidates(
            value,
            conditions,
            effect_summary,
        ):
            accepted = self.accept_effect_sensitive_rewrite(
                value,
                rewritten,
                conditions,
                effect_summary,
                rewrite_kind=rewrite_kind,
            )
            if (
                not accepted
                and self.accept_effect_rewrite_without_rank_gain(
                    value,
                    rewritten,
                    conditions,
                    effect_summary,
                )
            ):
                accepted = True
            if accepted:
                return rewritten
        return value

    def accept_effect_rewrite_without_rank_gain(
        self,
        original: Optional[Expression],
        rewritten: Optional[Expression],
        conditions: List[Condition],
        effect_summary: EffectSummary,
    ) -> bool:
        if original is None or rewritten is None:
            return False
        if _expressions_equivalent(original, rewritten):
            return False
        if _expression_contains_observed_loads(original):
            return False
        if self.return_normalization.rewrite_drops_composite_location_wrapper(original, rewritten, conditions):
            return False
        if expression_contains_post_state_reads(rewritten):
            return True
        original_effect_locations = self.matched_effect_locations(
            original,
            conditions,
            effect_summary,
        )
        rewritten_effect_locations = self.matched_effect_locations(
            rewritten,
            conditions,
            effect_summary,
        )
        if rewritten_effect_locations > original_effect_locations:
            return True

        location = canonicalize_expr_read_location(
            original,
            self.session().parameters,
        )
        if location is None:
            return False

        original_match = _find_matching_effect_value(
            original,
            location,
            conditions,
            effect_summary.effects,
            self.session().parameters,
        )
        rewritten_match = _find_matching_effect_value(
            rewritten,
            location,
            conditions,
            effect_summary.effects,
            self.session().parameters,
        )
        return original_match is None and rewritten_match is not None

    def matched_effect_locations(
        self,
        expr: Optional[Expression],
        conditions: List[Condition],
        effect_summary: EffectSummary,
    ) -> set[tuple]:
        matched_locations: set[tuple] = set()
        if expr is None:
            return matched_locations

        for current in _iter_expression_nodes(expr, include_phi_conditions=False):
            location = canonicalize_expr_read_location(current, self.session().parameters)
            if location is None:
                continue
            if _find_matching_effect_value(
                current,
                location,
                conditions,
                effect_summary.effects,
                self.session().parameters,
            ) is None:
                continue
            matched_locations.add(location.stable_key())
        return matched_locations

    def iter_effect_sensitive_rewrite_candidates(
        self,
        value: Expression,
        conditions: List[Condition],
        effect_summary: EffectSummary,
    ) -> Iterable[Tuple[str, Optional[Expression]]]:
        expr_location = canonicalize_expr_read_location(
            value,
            self.session().parameters,
        )
        nontrivial_location_wrapper = False
        effect_value_matches_wrapper = False
        if expr_location is not None:
            nontrivial_location_wrapper = self.expression_cases.expression_has_nontrivial_location_wrapper(
                value,
                expr_location,
            )
            if nontrivial_location_wrapper:
                effect_value_matches_wrapper = _find_matching_effect_value(
                    value,
                    expr_location,
                    conditions,
                    effect_summary.effects,
                    self.session().parameters,
                ) is not None
        if expr_location is not None:
            post_state_read = resolve_definite_post_state_read_for_location(
                expr_location,
                conditions,
                effect_summary.effects,
                self.session().parameters,
                symbolic_post_state=True,
            )
            if post_state_read is not None:
                yield ("final object-state concrete", lower_post_state_expression_for_smt(
                    post_state_read,
                    conditions,
                    effect_summary.effects,
                    self.session().parameters,
                ))
                if not nontrivial_location_wrapper or effect_value_matches_wrapper:
                    yield ("final object-state symbolic", post_state_read)
        if _expression_contains_observed_loads(value):
            yield (
                "observed-load",
                rewrite_observed_loads_from_effects(
                    value,
                    conditions,
                    effect_summary.effects,
                    self.session().parameters,
                ),
            )
        yield (
            "wrapper-preserving effect-sensitive",
            normalize_post_state_expression(
                value,
                conditions,
                effect_summary.effects,
                self.session().parameters,
                prefer_canonical_post_state=False,
                preserve_composite_location_wrappers=True,
            ),
        )
        yield (
            "generic effect-sensitive",
            rewrite_loads_from_effects(
                value,
                conditions,
                effect_summary.effects,
                self.session().parameters,
            ),
        )

    def collapse_effect_sensitive_case_wrapper(
        self,
        original: Optional[Expression],
        rewritten: Optional[Expression],
        conditions: List[Condition],
        effect_summary: EffectSummary,
    ) -> Optional[Expression]:
        if original is None or rewritten is None:
            return rewritten
        rebuilt_wrapper = self.rebuild_effect_sensitive_case_wrapper(
            original,
            rewritten,
            conditions,
            effect_summary,
        )
        if rebuilt_wrapper is not None:
            return rebuilt_wrapper
        if (
            original.expr_type != ExpressionType.BINARY_OP
            or rewritten.expr_type != ExpressionType.BINARY_OP
            or original.operator != rewritten.operator
            or len(original.operands) != 2
            or len(rewritten.operands) != 2
        ):
            return rewritten

        original_operands = list(original.operands)
        rewritten_operands = list(rewritten.operands)
        for original_index, original_operand in enumerate(original_operands):
            location = canonicalize_expr_read_location(
                original_operand,
                self.session().parameters,
            )
            if location is None:
                continue
            shared_original = original_operands[1 - original_index]
            for rewritten_index, rewritten_operand in enumerate(rewritten_operands):
                shared_rewritten = rewritten_operands[1 - rewritten_index]
                if not _expressions_equivalent(shared_rewritten, shared_original):
                    continue
                if not self.expression_cases.wrapper_preserves_collapsed_operand(
                    original.operator,
                    shared_original,
                    kept_operand_index=rewritten_index,
                ):
                    continue
                if (
                    _find_matching_effect_value(
                        rewritten_operand,
                        location,
                        conditions,
                        effect_summary.effects,
                        self.session().parameters,
                    )
                    is None
                ):
                    continue
                post_state_read = promote_effect_value_carrier_to_post_state_read(
                    rewritten_operand,
                    conditions,
                    effect_summary.effects,
                    self.session().parameters,
                    symbolic_post_state=True,
                )
                if post_state_read is not None:
                    final_replayed = _replay_definite_active_effects_for_location(
                        location,
                        conditions,
                        effect_summary.effects,
                        self.session().parameters,
                    )
                    if final_replayed is not None and _expressions_equivalent_under_conditions(
                        final_replayed,
                        rewritten_operand,
                        conditions,
                        self.session().parameters,
                    ):
                        post_state_read = None
                if self.debug_flag():
                    self.debug_reporter.debug_print(
                        "Collapsed duplicate effect-sensitive binary wrapper: "
                        f"{self.debug_reporter.debug_expr_details_summary(rewritten)} -> "
                        f"{self.debug_reporter.debug_expr_details_summary(post_state_read or rewritten_operand)}"
                    )
                return post_state_read or rewritten_operand

        return rewritten

    def rebuild_effect_sensitive_case_wrapper(
        self,
        original: Optional[Expression],
        rewritten: Optional[Expression],
        conditions: List[Condition],
        effect_summary: EffectSummary,
    ) -> Optional[Expression]:
        if (
            original is None
            or rewritten is None
            or original.expr_type != ExpressionType.BINARY_OP
            or len(original.operands) != 2
        ):
            return None
        if (
            rewritten.expr_type == ExpressionType.BINARY_OP
            and rewritten.operator == original.operator
            and len(rewritten.operands) == 2
        ):
            return None

        rewritten_runtime_ref = getattr(rewritten, "runtime_ref", None)
        if not isinstance(rewritten_runtime_ref, PostStateValueRef):
            return None

        original_operands = list(original.operands)
        for original_index, original_operand in enumerate(original_operands):
            location = canonicalize_expr_read_location(
                original_operand,
                self.session().parameters,
            )
            if location is None:
                continue
            rewritten_without_carrier_ref = _strip_materialized_post_state_value_refs(rewritten)
            if _expression_reads_location(
                rewritten_without_carrier_ref,
                location,
                conditions,
                self.session().parameters,
            ):
                continue
            shared_original = original_operands[1 - original_index]
            if self.expression_cases.wrapper_preserves_collapsed_operand(
                original.operator,
                shared_original,
                kept_operand_index=original_index,
            ):
                continue
            if (
                _find_matching_effect_value(
                    rewritten,
                    location,
                    conditions,
                    effect_summary.effects,
                    self.session().parameters,
                )
                is None
            ):
                continue
            rebuilt_operands = [shared_original, shared_original]
            rebuilt_operands[original_index] = rewritten
            rebuilt_operands[1 - original_index] = shared_original
            rebuilt = original.clone_with(operands=rebuilt_operands)
            rebuilt = ConditionSimplifier.reduce_expression_under_conditions(
                rebuilt,
                conditions,
            )
            rebuilt = self.expression_cases.fold_constant_expression(rebuilt, fallback_expr=original)
            if self.debug_flag():
                self.debug_reporter.debug_print(
                    "Rebuilt effect-sensitive wrapper around branch-local effect value: "
                    f"{self.debug_reporter.debug_expr_details_summary(rewritten)} -> "
                    f"{self.debug_reporter.debug_expr_details_summary(rebuilt)}"
                )
            return rebuilt

        return None

    def accept_effect_sensitive_rewrite(
        self,
        original: Optional[Expression],
        rewritten: Optional[Expression],
        conditions: List[Condition],
        effect_summary: EffectSummary,
        *,
        rewrite_kind: str,
    ) -> bool:
        if rewritten is None or original is None:
            return False
        if _expressions_equivalent(rewritten, original):
            return False

        if self.is_semantically_lossless_effect_sensitive_rewrite(
            original,
            rewritten,
            conditions,
            effect_summary,
        ):
            original_precision = self.effect_sensitive_rewrite_precision(
                original,
                conditions,
                effect_summary,
            )
            rewritten_precision = self.effect_sensitive_rewrite_precision(
                rewritten,
                conditions,
                effect_summary,
            )
            accepted = (
                rewritten_precision.post_state_reads > original_precision.post_state_reads
                or rewritten_precision.observed_loads < original_precision.observed_loads
                or rewritten_precision.matched_effect_locations >= original_precision.matched_effect_locations
                or rewritten_precision.downstream_unresolved_values
                <= original_precision.downstream_unresolved_values
            )
            if accepted:
                return True

        original_precision = self.effect_sensitive_rewrite_precision(
            original,
            conditions,
            effect_summary,
        )
        rewritten_precision = self.effect_sensitive_rewrite_precision(
            rewritten,
            conditions,
            effect_summary,
        )
        accepted = (
            rewritten_precision.opaque_unknowns < original_precision.opaque_unknowns
            or rewritten_precision.downstream_unresolved_values < original_precision.downstream_unresolved_values
            or rewritten_precision.matched_effect_locations > original_precision.matched_effect_locations
            or rewritten_precision.post_state_reads > original_precision.post_state_reads
            or (
                rewritten_precision.object_centric_unknowns > original_precision.object_centric_unknowns
                and rewritten_precision.downstream_unresolved_values
                <= original_precision.downstream_unresolved_values
            )
        )
        if not accepted:
            original_rank = self.effect_sensitive_rewrite_rank(original)
            rewritten_rank = self.effect_sensitive_rewrite_rank(rewritten)
            accepted = rewritten_rank > original_rank
        else:
            original_rank = self.effect_sensitive_rewrite_rank(original)
            rewritten_rank = self.effect_sensitive_rewrite_rank(rewritten)

        if self.debug_flag() and not accepted:
            self.debug_reporter.debug_print(
                f"Rejected {rewrite_kind} rewrite without object-centric precision gain: "
                f"{self.debug_reporter.debug_expr_details_summary(original)} -> "
                f"{self.debug_reporter.debug_expr_details_summary(rewritten)} "
                f"rank {original_rank} -> {rewritten_rank} "
                f"precision {original_precision} -> {rewritten_precision}"
            )

        return accepted

    def effect_sensitive_rewrite_precision(
        self,
        expr: Optional[Expression],
        conditions: List[Condition],
        effect_summary: EffectSummary,
    ) -> _EffectRewritePrecision:
        matched_locations = len(
            self.matched_effect_locations(expr, conditions, effect_summary)
        )
        post_state_reads = 1 if expression_contains_post_state_reads(expr) else 0
        lowered = expr
        if expr is not None and effect_summary is not None and getattr(effect_summary, "effects", None):
            lowered_candidate = lower_post_state_expression_for_smt(
                expr,
                conditions,
                effect_summary.effects,
                self.session().parameters,
            )
            if lowered_candidate is not None:
                lowered = lowered_candidate

        return _EffectRewritePrecision(
            matched_effect_locations=matched_locations,
            post_state_reads=post_state_reads,
            object_centric_unknowns=self.expression_cases.count_object_centric_unknowns(expr),
            opaque_unknowns=self.expression_cases.count_opaque_unknowns(expr),
            downstream_unresolved_values=self.expression_cases.count_unresolved_value_nodes(lowered),
            observed_loads=self.count_observed_loads(expr),
            phi_nodes=self.expression_cases.count_phi_nodes(expr),
        )

    def effect_sensitive_rewrite_rank(
        self,
        expr: Optional[Expression],
    ) -> Tuple[int, int, int, int]:
        if expr is None:
            return (0, 0, 0, 0)
        return (
            1 if expression_contains_post_state_reads(expr) else 0,
            1 if self.phi_origins.expression_contains_phi(expr) else 0,
            1 if _expression_contains_observed_loads(expr) else 0,
            self.count_memory_reads(expr),
        )

    def count_observed_loads(self, expr: Optional[Expression]) -> int:
        count = 0
        for current in _iter_expression_nodes(expr, include_phi_conditions=False):
            if _expression_contains_observed_loads(current):
                count += 1
        return count

    def return_info_effective_region_conditions(
        self,
        info: ReturnInfo,
    ) -> List[Condition]:
        """ReturnInfo conditions plus proof/runtime guards carried by its value."""

        conditions = list(getattr(info, "conditions", None) or [])
        conditions.extend(self.expression_cases.expression_runtime_guard_conditions(getattr(info, "value", None)))
        return ConditionSimplifier.simplify_conditions_object_centric(conditions)

    def normalize_return_value_with_effect_summary(
        self,
        value: Expression,
        conditions: List[Condition],
        effect_summary: EffectSummary,
    ) -> Optional[Expression]:
        carrier_post_state_read = promote_effect_value_carrier_to_post_state_read(
            value,
            conditions,
            effect_summary.effects,
            self.session().parameters,
            symbolic_post_state=True,
        )
        atomic_object_state_value = _materialize_existing_effect_value_carrier(
            value,
            conditions,
            effect_summary.effects,
            self.session().parameters,
        )
        if (
            atomic_object_state_value is not None
            and atomic_object_state_value is not value
            and isinstance(getattr(atomic_object_state_value, "runtime_ref", None), PostStateValueRef)
            and self.count_memory_reads(value) > 1
        ):
            return atomic_object_state_value

        canonicalized = normalize_post_state_expression(
            value,
            conditions,
            effect_summary.effects,
            self.session().parameters,
            prefer_canonical_post_state=True,
            symbolic_post_state=True,
        )
        canonicalized = self.collapse_effect_sensitive_case_wrapper(
            value,
            canonicalized,
            conditions,
            effect_summary,
        )
        if carrier_post_state_read is not None and expression_contains_post_state_reads(canonicalized):
            return canonicalized
        materialized_canonicalized = _materialize_existing_effect_value_carrier(
            canonicalized,
            conditions,
            effect_summary.effects,
            self.session().parameters,
        )
        original_location = canonicalize_expr_read_location(
            value,
            self.session().parameters,
        )
        if original_location is None:
            original_location = _find_unique_effect_location_for_value(
                value,
                conditions,
                effect_summary.effects,
                self.session().parameters,
            )
        carrier_matches_wrapped_object = (
            carrier_post_state_read is not None
            and original_location is not None
            and (
                self.expression_cases.expression_has_nontrivial_location_wrapper(value, original_location)
                or value.expr_type != ExpressionType.MEMORY
            )
        )
        if carrier_matches_wrapped_object:
            materialized_canonicalized = carrier_post_state_read
            drops_composite_wrapper = False
        else:
            drops_composite_wrapper = self.return_normalization.rewrite_drops_composite_location_wrapper(
                value,
                materialized_canonicalized,
                conditions,
            )
        if (
            not drops_composite_wrapper
            and original_location is not None
            and self.expression_cases.expression_has_nontrivial_location_wrapper(value, original_location)
            and isinstance(getattr(materialized_canonicalized, "runtime_ref", None), PostStateValueRef)
        ):
            distinct_read_locations = {
                location.stable_key()
                for node in _iter_expression_nodes(value, include_phi_conditions=False)
                for location in (
                    canonicalize_expr_read_location(
                        node,
                        self.session().parameters,
                    ),
                )
                if location is not None
            }
            if len(distinct_read_locations) == 1:
                lowered_materialized = lower_post_state_expression_for_smt(
                    materialized_canonicalized,
                    conditions,
                    effect_summary.effects,
                    self.session().parameters,
                )
                if lowered_materialized is None or not _expressions_equivalent_under_conditions(
                    lowered_materialized,
                    value,
                    conditions,
                    self.session().parameters,
                ):
                    drops_composite_wrapper = True
        if drops_composite_wrapper:
            wrapper_preserving = normalize_post_state_expression(
                value,
                conditions,
                effect_summary.effects,
                self.session().parameters,
                prefer_canonical_post_state=False,
                preserve_composite_location_wrappers=True,
            )
            canonicalized = wrapper_preserving if wrapper_preserving is not None else canonicalized
        else:
            if carrier_post_state_read is not None:
                canonicalized = carrier_post_state_read
            else:
                canonicalized = materialized_canonicalized
        canonicalized = self.prefer_lossless_materialized_post_state_roundtrip(
            canonicalized,
            value,
            conditions,
            effect_summary,
        )
        if expression_matches_stale_post_state_replay(
            value,
            canonicalized,
            conditions,
            effect_summary.effects,
            self.session().parameters,
        ):
            return canonicalized
        if self.return_normalization.should_replay_canonicalized_return(canonicalized, value):
            replayed = normalize_post_state_expression(
                canonicalized,
                conditions,
                effect_summary.effects,
                self.session().parameters,
                prefer_canonical_post_state=False,
            )
            if replayed is not None:
                canonicalized = replayed

        if self.symbolic_post_state_roundtrip_rejected(canonicalized, value, conditions, effect_summary):
            if self.debug_flag():
                self.debug_reporter.debug_print(
                    "Rejected symbolic post-state canonicalization due to non-equivalent round trip: "
                    f"{self.debug_reporter.debug_expr_summary(value)} -> "
                    f"{self.debug_reporter.debug_expr_summary(canonicalized)}"
                )
            fallback_replayed = None
            if carrier_post_state_read is not None:
                fallback_replayed = carrier_post_state_read
            if fallback_replayed is None and value.expr_type == ExpressionType.MEMORY:
                fallback_replayed = materialize_definite_post_state_expression(
                    value,
                    conditions,
                    effect_summary.effects,
                    self.session().parameters,
                    preserve_composite_location_wrappers=True,
                )
            if fallback_replayed is None or _expressions_equivalent(fallback_replayed, value):
                fallback_replayed = normalize_post_state_expression(
                    value,
                    conditions,
                    effect_summary.effects,
                    self.session().parameters,
                    prefer_canonical_post_state=False,
                    preserve_composite_location_wrappers=True,
                )
            return fallback_replayed if fallback_replayed is not None else value

        return canonicalized

    def prefer_lossless_materialized_post_state_roundtrip(
        self,
        canonicalized: Optional[Expression],
        original: Expression,
        conditions: List[Condition],
        effect_summary: EffectSummary,
    ) -> Optional[Expression]:
        if canonicalized is None:
            return None
        if original.expr_type == ExpressionType.MEMORY:
            return canonicalized
        if _expression_contains_observed_loads(original):
            return canonicalized
        if canonicalized.expr_type == ExpressionType.MEMORY:
            return canonicalized
        if not expression_contains_post_state_reads(canonicalized):
            return canonicalized

        carrier_post_state_read = promote_effect_value_carrier_to_post_state_read(
            original,
            conditions,
            effect_summary.effects,
            self.session().parameters,
            symbolic_post_state=True,
        )
        if (
            carrier_post_state_read is not None
            and _expressions_equivalent(canonicalized, carrier_post_state_read)
        ):
            return canonicalized

        lowered_roundtrip = lower_post_state_expression_for_smt(
            canonicalized,
            conditions,
            effect_summary.effects,
            self.session().parameters,
        )
        if lowered_roundtrip is None:
            return canonicalized
        if expression_contains_post_state_reads(lowered_roundtrip):
            return canonicalized
        if not _expressions_equivalent_under_conditions(
            lowered_roundtrip,
            original,
            conditions,
            self.session().parameters,
        ):
            return canonicalized
        return lowered_roundtrip

    def symbolic_post_state_roundtrip_rejected(
        self,
        canonicalized: Optional[Expression],
        original: Expression,
        conditions: List[Condition],
        effect_summary: EffectSummary,
    ) -> bool:
        if canonicalized is None or _expressions_equivalent(canonicalized, original):
            return False
        if not expression_contains_post_state_reads(canonicalized):
            return False
        lowered_roundtrip = lower_post_state_expression_for_smt(
            canonicalized,
            conditions,
            effect_summary.effects,
            self.session().parameters,
        )
        if lowered_roundtrip is None:
            return True

        comparison_targets = [original]
        if original.expr_type == ExpressionType.MEMORY:
            expected_roundtrip = materialize_definite_post_state_expression(
                original,
                conditions,
                effect_summary.effects,
                self.session().parameters,
                preserve_composite_location_wrappers=True,
            )
            if expected_roundtrip is not None:
                comparison_targets.insert(0, expected_roundtrip)
        if _expression_contains_observed_loads(original):
            observed_post_state = promote_observed_loads_to_post_state_reads(
                original,
                conditions,
                effect_summary.effects,
                self.session().parameters,
                symbolic_post_state=True,
            )
            if observed_post_state is not None:
                comparison_targets.append(observed_post_state)
                lowered_observed_post_state = lower_post_state_expression_for_smt(
                    observed_post_state,
                    conditions,
                    effect_summary.effects,
                    self.session().parameters,
                )
                if lowered_observed_post_state is not None:
                    comparison_targets.append(lowered_observed_post_state)
            observed_rewritten = rewrite_observed_loads_from_effects(
                original,
                conditions,
                effect_summary.effects,
                self.session().parameters,
            )
            if observed_rewritten is not None:
                comparison_targets.append(observed_rewritten)
            observed_roundtrip = normalize_post_state_expression(
                original,
                conditions,
                effect_summary.effects,
                self.session().parameters,
                prefer_canonical_post_state=False,
                preserve_composite_location_wrappers=True,
            )
            if observed_roundtrip is not None:
                comparison_targets.append(observed_roundtrip)

        for comparison_target in comparison_targets:
            if _expressions_equivalent_under_conditions(
                lowered_roundtrip,
                comparison_target,
                conditions,
                self.session().parameters,
            ):
                return False
        if self.expression_contains_stale_effect_value_for_post_state(
            original,
            canonicalized,
            conditions,
            effect_summary,
        ):
            return False
        return True

    def expression_contains_stale_effect_value_for_post_state(
        self,
        expr: Optional[Expression],
        target_post_state: Optional[Expression],
        conditions: List[Condition],
        effect_summary: EffectSummary,
    ) -> bool:
        if expr is None or target_post_state is None:
            return False

        candidates = [expr]
        if expr.expr_type == ExpressionType.PHI and expr.value:
            candidates.extend(
                value
                for _cond, value in expr.value
                if value is not None
            )

        for current in candidates:
            location = canonicalize_expr_read_location(current, self.session().parameters)
            if location is not None:
                promoted = promote_effect_value_match_to_post_state_read(
                    current,
                    location,
                    conditions,
                    effect_summary.effects,
                    self.session().parameters,
                    symbolic_post_state=True,
                )
                if promoted is not None and _expressions_equivalent(promoted, target_post_state):
                    return True
            if expression_matches_stale_post_state_replay(
                current,
                target_post_state,
                conditions,
                effect_summary.effects,
                self.session().parameters,
            ):
                return True
        return False

    def count_memory_reads(self, expr: Optional[Expression]) -> int:
        if expr is None:
            return 0
        count = 1 if expr.expr_type == ExpressionType.MEMORY else 0
        if expr.expr_type == ExpressionType.PHI and expr.value:
            return count + sum(self.count_memory_reads(value) for _cond, value in expr.value)
        for operand in getattr(expr, "operands", []) or []:
            count += self.count_memory_reads(operand)
        return count

    def concretize_readonly_loads(
        self,
        value: Expression,
        conditions: List[Condition],
        parameters: List[Dict],
    ) -> Expression:
        """Resolve simple read-only indexed loads into finite PHI chains when possible."""
        try:
            return concretize_readonly_loads(
                value,
                conditions,
                parameters,
                self.read_memory_value,
                image_base=self.program_value().getImageBase().getOffset(),
                debug=self.debug_flag(),
            )
        except Exception as exc:
            self.debug_reporter.debug_print(f"Readonly load concretization failed: {exc}")
            return value

    def read_memory_value(self, address_value: int, size_bytes: int) -> Optional[int]:
        """Read an unsigned integer from program memory."""
        if address_value < 0 or size_bytes <= 0:
            return None

        try:
            memory = self.program_value().getMemory()
            default_space = self.program_value().getAddressFactory().getDefaultAddressSpace()
            addr = default_space.getAddress(address_value)
            if addr is None:
                return None

            raw_bytes = []
            for offset in range(size_bytes):
                byte_val = memory.getByte(addr.add(offset))
                raw_bytes.append(int(byte_val) & 0xFF)

            is_big_endian = self.program_value().getLanguage().isBigEndian()
            ordered = raw_bytes if is_big_endian else list(reversed(raw_bytes))

            result = 0
            for byte_val in ordered:
                result = (result << 8) | byte_val
            return result
        except Exception:
            return None

    def apply_observable_effect_surface(
        self,
        result: FunctionReturnAnalysis,
        return_type_obj: Any,
        return_type: Optional[str],
    ) -> bool:
        """Compare non-void functions on ``stores ⊕ return value`` (Issue #13).

        A function that writes through a parameter pointer (or to a global) and
        returns something is observable through both; comparing the return value
        alone let two functions that only differ in what they store come out
        EQUIVALENT (raytrace constructors returning the sret pointer).  This is
        the void ``memory_effect`` surface generalised: the packed store summary
        (per-location presence flag and value, conditional on the store's path
        conditions) is concatenated with each return case's value, and the
        comparison surface becomes ``memory_effect`` with the combined width.

        When the effect summary is not trustworthy (``has_unsupported_call`` or
        any ``incomplete_reasons``) the surface is not built and the existing
        equivalence-blocking reasons keep such functions away from EQUIVALENT.
        When the summary is trustworthy but the surface cannot be composed
        (no return observation, return widths disagree, degenerate widths, or a
        global effect next to an address-bound global read) the summary is
        marked incomplete (Issue #104, Gap 5) so the return value alone is never
        used as the comparison surface.
        """
        if result is None:
            return False
        if return_type_obj is not None and self.parameters.is_void_type(return_type_obj):
            return False
        if not result.returns:
            effect_summary = getattr(result, "effect_summary", None)
            if (
                isinstance(effect_summary, EffectSummary)
                and not getattr(effect_summary, "has_unsupported_call", False)
                and not _incomplete_reason_tuple(effect_summary)
                and observable_store_effects(effect_summary)
            ):
                # Issue #104 (Gap 5): stores without any return observation.
                effect_summary.incomplete_reasons = (_EFFECT_SURFACE_COMPOSITION_REASON,)
            return False
        if getattr(result, "comparison_surface", None) is not None:
            return False
        effect_summary = getattr(result, "effect_summary", None)
        if effect_summary is None:
            return False
        if getattr(effect_summary, "has_unsupported_call", False):
            return False
        if tuple(getattr(effect_summary, "incomplete_reasons", ()) or ()):
            # An incomplete store model must not become a comparison surface:
            # a missing store on one side could only make the surfaces agree.
            return False
        effects = observable_store_effects(effect_summary)
        if not effects:
            return False
        from scripts.function_tracer_pcode.analysis.effects.summary import (
            _concat as concat_expressions,
            build_void_effect_summary_expr,
        )

        def _fail_closed(reason: str, detail: str) -> bool:
            # Issue #104 (Gap 5): observable stores exist but the combined
            # return + effect surface cannot be composed.  Falling back to the
            # return value alone would silently drop the stores, so record an
            # effect-summary blocker instead; the existing equivalence gates
            # then keep the pair away from EQUIVALENT.
            reasons = _incomplete_reason_tuple(effect_summary)
            if reason not in reasons:
                effect_summary.incomplete_reasons = tuple(sorted(reasons + (reason,)))
            self.debug_reporter.debug_print(
                f"Observable effect surface not composed ({detail}); marked {reason}"
            )
            return False

        if any(effect.location.base_ref.is_global() for effect in effects):
            for ret in result.returns:
                if expression_reads_unidentified_writable_memory(ret.value) or any(
                    expression_reads_unidentified_writable_memory(getattr(cond, "expression", None))
                    for cond in ret.conditions
                ):
                    return _fail_closed(
                        _EFFECT_GLOBAL_READ_IDENTITY_REASON,
                        "return observation reads writable memory without a global identity",
                    )

        effects_expr = build_void_effect_summary_expr(effects)
        if effects_expr is None:
            return _fail_closed(_EFFECT_SURFACE_COMPOSITION_REASON, "no effect expression")
        effect_bits = int(effects_expr.get_bit_width() or 0)
        return_widths = set()
        for ret in result.returns:
            if ret.value is None:
                return _fail_closed(_EFFECT_SURFACE_COMPOSITION_REASON, "return without value")
            return_widths.add(int(ret.value.get_bit_width() or 0))
        if len(return_widths) != 1:
            # Every return case must contribute the same width, otherwise the
            # combined surface has no single width.  The return-value surface
            # alone is not a complete observation once stores exist.
            return _fail_closed(
                _EFFECT_SURFACE_COMPOSITION_REASON,
                f"return widths disagree: {sorted(return_widths)}",
            )
        return_bits = return_widths.pop()
        if effect_bits <= 0 or return_bits <= 0:
            return _fail_closed(
                _EFFECT_SURFACE_COMPOSITION_REASON,
                f"degenerate widths effect={effect_bits} return={return_bits}",
            )
        rewritten = []
        for ret in result.returns:
            combined = concat_expressions(effects_expr, ret.value)
            rewritten.append(replace(ret, value=combined))
        result.returns = rewritten
        result.comparison_surface = ComparisonSurface(
            kind="memory_effect",
            explicit_bit_width=effect_bits + return_bits,
            use_sign_extension=False,
            evidence={
                "source": OBSERVABLE_EFFECT_SURFACE_SOURCE,
                "effect_count": len(effects),
                "effect_bits": effect_bits,
                "return_bits": return_bits,
                "declared_return_type": return_type,
            },
        )
        if "observable_effect_surface" not in result.analysis_notes:
            result.analysis_notes.append("observable_effect_surface")
        self.debug_reporter.debug_print(
            f"Observable effect surface: {len(effects)} store effect(s) ({effect_bits} bits) "
            f"combined with the {return_bits}-bit return value"
        )
        return True


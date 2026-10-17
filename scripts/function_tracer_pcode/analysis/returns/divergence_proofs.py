"""Guard / SCC divergence proofs and recursive SCC certificates."""

from __future__ import annotations

import hashlib
from typing import Any, Callable, Dict, List, Mapping, Optional, Sequence, Set, TYPE_CHECKING, Tuple
from scripts.function_tracer_pcode.core.analysis import FunctionReturnAnalysis
from scripts.function_tracer_pcode.core.expression import Condition, Expression, ExpressionType
from scripts.function_tracer_pcode.core.render_smt import expression_contains_unsupported_smt_ops
from scripts.function_tracer_pcode.core.structural import expression_key
from scripts.function_tracer_pcode.core.errors import AnalysisLimitation
from scripts.function_tracer_pcode.analysis.returns._shared import (
    ConditionNormalizer,
    ConditionSMTOracle,
)
from scripts.function_tracer_pcode.analysis.runtime_state import AnalysisRuntimeState
from scripts.function_tracer_pcode.analysis.returns.lifecycle import ProgramAccessService
from scripts.function_tracer_pcode.analysis.returns.debug_reporter import DebugReporter
from scripts.function_tracer_pcode.analysis.returns._api import (
    PcodeTracer,
    StructuralRecurrenceSummarizer,
)
from scripts.function_tracer_pcode.analysis.returns.condition_logic import ConditionLogicService
from scripts.function_tracer_pcode.analysis.returns.constant_values import ConstantValueService
from scripts.function_tracer_pcode.analysis.returns.control_recovery import BlockGraphService
from scripts.function_tracer_pcode.analysis.debug import summarize_condition

if TYPE_CHECKING:  # placeholder_algebra は本 module の純関数を import するため循環回避
    from scripts.function_tracer_pcode.analysis.returns.placeholder_algebra import PlaceholderAlgebraService


def condition_identity_key(condition: Condition) -> Tuple[Any, ...]:
    """条件の identity 鍵。純関数（facade 状態なし）。

    構造 key は「等しい ⇒ 構造が等しい」（`core/structural` の C-K1）なので、打ち
    切りを含む key もそのまま identity にする。比較できない key を `None` に潰すと、
    比較できない条件どうしがすべて同じ鍵になる（Issue #215）。
    """
    return (
        "condition",
        expression_key(getattr(condition, "expression", None)),
        bool(getattr(condition, "negated", False)),
    )


class DivergenceProofService:
    """ReturnAnalyzer から切り出した発散証明（SCC 非進行ガード・条件進行ガード鍵・CFG 循環）の collaborator。

    analyzer-lifetime mutable state: ``AnalysisRuntimeState`` owner を ``runtime_state`` 直接依存として保持し、
    直接呼び出しグラフとその完了ノード集合は ``self.runtime_state.direct_call_graph`` 等で owner 経由で都度読む
    （owner の identity は固定するが field は都度参照するため、facade property による field object の差し替えに
    追随する。グラフは解析中に facade 側で更新される）。configuration: ``program`` は従来どおり supplier 境界。
    条件論理・placeholder
    代数・定数値抽出・block グラフ走査（``BlockGraphService``）・program アクセス（``ProgramAccessService``）・
    デバッグ出力（``DebugReporter``）は各 collaborator を直接依存として受け取る。facade 経由の callback は残っていない。
    ``condition_identity_key`` は module 関数が実装で、PlaceholderAlgebraService も同じ関数を使う。
    """

    def __init__(
        self,
        *,
        runtime_state: "AnalysisRuntimeState",
        block_graph: BlockGraphService,
        program_access: ProgramAccessService,
        condition_logic: ConditionLogicService,
        placeholder_algebra: "PlaceholderAlgebraService",
        constant_values: ConstantValueService,
        debug_reporter: DebugReporter,
        program_value: Callable[..., Any],
    ) -> None:
        self.runtime_state = runtime_state
        self.block_graph = block_graph
        self.program_access = program_access
        self.condition_logic = condition_logic
        self.placeholder_algebra = placeholder_algebra
        self.constant_values = constant_values
        self.debug_reporter = debug_reporter
        self.program_value = program_value

    def recursive_scc_certificate(
        self,
        function_key: Optional[Tuple[object, ...]],
    ) -> Tuple[bool, Optional[str], Tuple[Tuple[object, ...], ...]]:
        """Return a certificate only for a fully enumerated recursive SCC."""

        if function_key is None or function_key not in self.runtime_state.direct_call_graph:
            return False, None, ()
        graph = self.runtime_state.direct_call_graph
        index = 0
        stack: List[Tuple[object, ...]] = []
        on_stack: Set[Tuple[object, ...]] = set()
        indices: Dict[Tuple[object, ...], int] = {}
        lowlinks: Dict[Tuple[object, ...], int] = {}
        components: List[Tuple[Tuple[object, ...], ...]] = []

        def visit(node: Tuple[object, ...]) -> None:
            nonlocal index
            indices[node] = index
            lowlinks[node] = index
            index += 1
            stack.append(node)
            on_stack.add(node)
            for target in graph.get(node, set()):
                if target not in graph:
                    continue
                if target not in indices:
                    visit(target)
                    lowlinks[node] = min(lowlinks[node], lowlinks[target])
                elif target in on_stack:
                    lowlinks[node] = min(lowlinks[node], indices[target])
            if lowlinks[node] != indices[node]:
                return
            component: List[Tuple[object, ...]] = []
            while stack:
                member = stack.pop()
                on_stack.remove(member)
                component.append(member)
                if member == node:
                    break
            components.append(tuple(component))

        for node in tuple(graph):
            if node not in indices:
                visit(node)
        component = next(
            (candidate for candidate in components if function_key in candidate),
            (),
        )
        recursive = len(component) > 1 or function_key in graph.get(function_key, set())
        complete = bool(component) and all(
            member in self.runtime_state.direct_call_graph_complete_nodes for member in component
        )
        if not recursive or not complete:
            return False, None, ()
        members = tuple(sorted(component, key=repr))
        identity = hashlib.sha256(repr(("call_graph_scc", members)).encode("utf-8")).hexdigest()
        return True, identity, members

    def prove_single_guard_nonprogress_region_must_diverge(
        self,
        high_function,
        analysis: FunctionReturnAnalysis,
        *,
        divergence_guard: Condition,
        param: Expression,
    ) -> Optional[Dict[str, Any]]:
        if high_function is None or divergence_guard is None:
            return None
        if expression_contains_unsupported_smt_ops(getattr(divergence_guard, "expression", None)):
            self.debug_reporter.debug_print("Outcome loop divergence proof declined: unsupported divergence guard")
            return None
        if not (
            self.condition_logic.conditions_equivalent([divergence_guard], [self.condition_logic.signed_positive_condition(param)])
            or self.condition_logic.condition_is_signed_positive_of_param(divergence_guard, param)
        ):
            self.debug_reporter.debug_print("Outcome loop divergence proof declined: divergence guard is not param positive")
            return None

        blocks = list(self.block_graph.iter_high_basic_blocks(high_function))
        if not blocks:
            self.debug_reporter.debug_print("Outcome loop divergence proof declined: no high-function blocks")
            return None
        if not self.high_function_has_cfg_cycle(high_function):
            self.debug_reporter.debug_print("Outcome loop divergence proof declined: no CFG cycle")
            return None

        tracer = None
        if self.program_value() is not None:
            try:
                tracer = self.program_access.make_tracer(high_function)
            except Exception:
                tracer = None
        cyclic_sccs = self.high_function_cyclic_sccs(blocks)
        if not cyclic_sccs:
            self.debug_reporter.debug_print("Outcome loop divergence proof declined: no cyclic SCC")
            return None

        for scc in cyclic_sccs:
            proof = self.prove_scc_must_diverge_under_guard(
                scc,
                all_blocks=blocks,
                divergence_guard=divergence_guard,
                param=param,
                tracer=tracer,
            )
            if proof is not None:
                cfg_blocks = tuple(sorted(
                    (self.block_graph.block_debug_key(block) for block in blocks), key=repr
                ))
                cfg_edges = tuple(sorted((
                    (self.block_graph.block_debug_key(block), self.block_graph.block_debug_key(successor))
                    for block in blocks
                    for successor in self.block_graph.block_successors(block)
                ), key=repr))
                proof.update(
                    {
                        "proof_kind": "single_guard_nonprogress_must_diverge",
                        "candidate_rule": "side_effect_free_nonprogress_loop_guard_complement",
                        "guard": "param_positive",
                        "return_partition": "param_nonpositive_return_zero",
                        "cfg_applicability_surface": (cfg_blocks, cfg_edges),
                    }
                )
                return proof
        return None

    def prove_scc_must_diverge_under_guard(
        self,
        scc: Sequence[Any],
        *,
        all_blocks: Sequence[Any],
        divergence_guard: Condition,
        param: Expression,
        tracer: Optional[PcodeTracer],
    ) -> Optional[Dict[str, Any]]:
        scc_set = set(scc or ())
        scc_keys = {self.block_graph.block_debug_key(block) for block in scc_set}
        if not scc_set:
            return None
        if any(self.block_graph.block_has_return_op(block) for block in scc_set):
            self.debug_reporter.debug_print("Outcome loop divergence proof declined: RETURN in candidate SCC")
            return None
        if any(self.block_graph.block_writes_outcome_guard_state(block) for block in scc_set):
            self.debug_reporter.debug_print("Outcome loop divergence proof declined: guard state write in SCC")
            return None
        if not self.scc_preserves_guard_dependencies(scc_set):
            self.debug_reporter.debug_print("Outcome loop divergence proof declined: guard dependency is redefined in SCC")
            return None

        internal_guarded_continue = False
        internal_unconditional_continue = False
        exit_proofs = []
        for block in scc_set:
            for successor in self.block_graph.block_successors(block):
                if self.block_graph.block_debug_key(successor) in scc_keys:
                    edge_condition = self.edge_condition_for_successor(block, successor, tracer)
                    if edge_condition is None:
                        internal_unconditional_continue = True
                    elif self.single_guard_condition_matches(edge_condition, divergence_guard, param):
                        internal_guarded_continue = True
                    continue

                edge_condition = self.edge_condition_for_successor(block, successor, tracer)
                if edge_condition is None:
                    self.debug_reporter.debug_print("Outcome loop divergence proof declined: SCC exit without edge guard")
                    return None
                if not self.single_guard_conditions_are_contradictory(divergence_guard, edge_condition, param):
                    if self.debug_reporter.debug_available():
                        self.debug_reporter.debug_print(
                            "Outcome loop divergence proof declined: SCC exit is feasible under divergence guard "
                            f"(divergence={summarize_condition(divergence_guard)}, "
                            f"exit={summarize_condition(edge_condition)})"
                        )
                    return None
                exit_proofs.append(
                    {
                        "source": self.block_graph.block_debug_key(block),
                        "target": self.block_graph.block_debug_key(successor),
                        "guard_relation": "divergence_guard_and_exit_guard_unsat",
                    }
                )

        entry_proofs = []
        has_guarded_entry = False
        has_unconditional_entry = False
        for block in all_blocks or ():
            if self.block_graph.block_debug_key(block) in scc_keys:
                continue
            for successor in self.block_graph.block_successors(block):
                if self.block_graph.block_debug_key(successor) not in scc_keys:
                    continue
                edge_condition = self.edge_condition_for_successor(block, successor, tracer)
                if edge_condition is None:
                    if self.block_graph.block_predecessor_count(block) != 0:
                        self.debug_reporter.debug_print("Outcome loop divergence proof declined: unconditional SCC entry is not from function entry")
                        return None
                    has_unconditional_entry = True
                    entry_proofs.append(
                        {
                            "source": self.block_graph.block_debug_key(block),
                            "target": self.block_graph.block_debug_key(successor),
                            "guard_relation": "unconditional_entry_then_internal_guard",
                        }
                    )
                elif self.single_guard_condition_matches(edge_condition, divergence_guard, param):
                    has_guarded_entry = True
                    entry_proofs.append(
                        {
                            "source": self.block_graph.block_debug_key(block),
                            "target": self.block_graph.block_debug_key(successor),
                            "guard_relation": "entry_guard_equivalent_to_divergence_guard",
                        }
                    )
                else:
                    if self.debug_reporter.debug_available():
                        self.debug_reporter.debug_print(
                            "Outcome loop divergence proof declined: SCC entry guard does not match divergence guard "
                            f"(divergence={summarize_condition(divergence_guard)}, "
                            f"entry={summarize_condition(edge_condition)})"
                        )
                    return None

        if not has_guarded_entry and not has_unconditional_entry:
            self.debug_reporter.debug_print("Outcome loop divergence proof declined: candidate SCC has no proved external entry")
            return None
        if has_guarded_entry:
            preservation_ok = internal_unconditional_continue or internal_guarded_continue
        elif has_unconditional_entry:
            preservation_ok = internal_guarded_continue
        else:
            preservation_ok = False
        if not preservation_ok:
            self.debug_reporter.debug_print("Outcome loop divergence proof declined: no guarded/invariant-preserving continue edge")
            return None

        return {
            "scc_blocks": [self.block_graph.block_debug_key(block) for block in scc_set],
            "entry_edges": entry_proofs,
            "exit_edges": exit_proofs,
            "side_effect_control_safety": {
                "forbidden_ops_absent": True,
                "return_ops_absent_in_scc": True,
                "guard_state_writes_absent": True,
            },
            "invariant_preservation": {
                "internal_guarded_continue": internal_guarded_continue,
                "internal_unconditional_continue": internal_unconditional_continue,
            },
        }

    def high_function_cyclic_sccs(self, blocks: Sequence[Any]) -> List[Tuple[Any, ...]]:
        key_to_block = {self.block_graph.block_debug_key(block): block for block in blocks or ()}
        block_keys = set(key_to_block)
        index_counter = 0
        stack: List[Any] = []
        on_stack: Set[Any] = set()
        indices: Dict[Any, int] = {}
        lowlinks: Dict[Any, int] = {}
        components: List[Tuple[Any, ...]] = []

        def strongconnect(block_key) -> None:
            nonlocal index_counter
            indices[block_key] = index_counter
            lowlinks[block_key] = index_counter
            index_counter += 1
            stack.append(block_key)
            on_stack.add(block_key)

            for successor in self.block_graph.block_successors(key_to_block[block_key]):
                successor_key = self.block_graph.block_debug_key(successor)
                if successor_key not in block_keys:
                    continue
                if successor_key not in indices:
                    strongconnect(successor_key)
                    lowlinks[block_key] = min(lowlinks[block_key], lowlinks[successor_key])
                elif successor_key in on_stack:
                    lowlinks[block_key] = min(lowlinks[block_key], indices[successor_key])

            if lowlinks[block_key] != indices[block_key]:
                return
            component = []
            while stack:
                current = stack.pop()
                on_stack.remove(current)
                component.append(current)
                if current == block_key:
                    break
            component_set = set(component)
            if len(component) > 1 or any(
                self.block_graph.block_debug_key(successor) in component_set
                for item in component
                for successor in self.block_graph.block_successors(key_to_block[item])
            ):
                components.append(tuple(key_to_block[item] for item in component))

        for block in blocks or ():
            key = self.block_graph.block_debug_key(block)
            if key not in indices:
                strongconnect(key)
        return components

    def scc_preserves_guard_dependencies(self, scc_set: Set[Any]) -> bool:
        guard_dependency_keys: Set[Tuple[Any, ...]] = set()
        for block in scc_set:
            cbranch = self.block_graph.first_high_block_cbranch(block)
            if cbranch is None:
                continue
            if getattr(cbranch, "condition_expr", None) is not None and not callable(getattr(cbranch, "getInput", None)):
                continue
            try:
                if int(getattr(cbranch, "getNumInputs", lambda: 0)() or 0) < 2:
                    return False
                condition_varnode = cbranch.getInput(1)
            except Exception:
                return False
            if not self.collect_guard_dependency_varnodes(
                condition_varnode,
                guard_dependency_keys,
                is_root=True,
                seen=set(),
            ):
                return False

        if not guard_dependency_keys:
            return True

        for block in scc_set:
            for op in self.block_graph.iter_high_block_ops(block):
                output = getattr(op, "getOutput", lambda: None)()
                if output is None:
                    continue
                output_key = self.varnode_guard_dependency_key(output)
                if output_key in guard_dependency_keys:
                    return False
        return True

    def collect_guard_dependency_varnodes(
        self,
        varnode,
        guard_dependency_keys: Set[Tuple[Any, ...]],
        *,
        is_root: bool,
        seen: Set[Tuple[Any, ...]],
    ) -> bool:
        if varnode is None:
            return False
        key = self.varnode_guard_dependency_key(varnode)
        if key in seen:
            return True
        seen.add(key)

        is_constant = getattr(varnode, "isConstant", lambda: False)
        try:
            if callable(is_constant) and is_constant():
                return True
        except Exception:
            return False

        try:
            def_op = varnode.getDef()
        except Exception:
            return False
        if def_op is None:
            guard_dependency_keys.add(key)
            return True

        if not is_root:
            guard_dependency_keys.add(key)

        mnemonic = getattr(def_op, "getMnemonic", lambda: None)()
        if mnemonic not in {
            "COPY",
            "CAST",
            "SUBPIECE",
            "INT_ZEXT",
            "INT_SEXT",
            "INT_EQUAL",
            "INT_NOTEQUAL",
            "INT_LESS",
            "INT_SLESS",
            "INT_LESSEQUAL",
            "INT_SLESSEQUAL",
            "BOOL_NEGATE",
            "BOOL_AND",
            "BOOL_OR",
            "BOOL_XOR",
        }:
            return False

        try:
            input_count = int(getattr(def_op, "getNumInputs", lambda: 0)() or 0)
        except Exception:
            return False
        for index in range(input_count):
            try:
                child = def_op.getInput(index)
            except Exception:
                return False
            if not self.collect_guard_dependency_varnodes(
                child,
                guard_dependency_keys,
                is_root=False,
                seen=seen,
            ):
                return False
        return True

    def varnode_guard_dependency_key(self, varnode) -> Tuple[Any, ...]:
        try:
            address = varnode.getAddress()
            offset = getattr(address, "getOffset", lambda: None)()
            space = getattr(getattr(address, "getAddressSpace", lambda: None)(), "getName", lambda: None)()
            size = getattr(varnode, "getSize", lambda: None)()
            if offset is not None and size is not None:
                return ("varnode", space, int(offset), int(size))
        except Exception:
            pass
        return ("varnode_object", id(varnode))

    def edge_condition_for_successor(
        self,
        block,
        successor,
        tracer: Optional[PcodeTracer],
    ) -> Optional[Condition]:
        edge_conditions = getattr(block, "_edge_conditions", None)
        if isinstance(edge_conditions, Mapping):
            for key in (successor, id(successor), self.block_graph.block_debug_key(successor)):
                condition = edge_conditions.get(key)
                if condition is not None:
                    return condition

        cbranch = self.block_graph.first_high_block_cbranch(block)
        if cbranch is None:
            return None
        expr = getattr(cbranch, "condition_expr", None)
        if expr is None:
            if tracer is None:
                return None
            try:
                if int(getattr(cbranch, "getNumInputs", lambda: 0)() or 0) < 2:
                    return None
                expr = tracer.trace_varnode(cbranch.getInput(1), use_cache=False)
            except Exception:
                return None
        if expr is None or expression_contains_unsupported_smt_ops(expr):
            return None

        true_out = getattr(block, "getTrueOut", lambda: None)()
        false_out = getattr(block, "getFalseOut", lambda: None)()
        if true_out is not None and self.block_graph.same_high_block(true_out, successor):
            return Condition(expr, False)
        if false_out is not None and self.block_graph.same_high_block(false_out, successor):
            return Condition(expr, True)
        relation = self.block_graph.direct_cbranch_successor_relation(cbranch, block, successor)
        if relation == "true":
            return Condition(expr, False)
        if relation == "false":
            return Condition(expr, True)
        return None

    def single_guard_condition_matches(
        self,
        condition: Condition,
        divergence_guard: Condition,
        param: Expression,
    ) -> bool:
        return (
            condition.equals(divergence_guard)
            or self.condition_logic.conditions_equivalent([condition], [divergence_guard])
            or (
                self.condition_logic.condition_is_signed_positive_of_param(condition, param)
                and self.condition_logic.condition_is_signed_positive_of_param(divergence_guard, param)
            )
        )

    def single_guard_conditions_are_contradictory(
        self,
        divergence_guard: Condition,
        edge_condition: Condition,
        param: Expression,
    ) -> bool:
        return (
            edge_condition.equals(divergence_guard.negate())
            or self.condition_logic.conditions_are_unsat([divergence_guard, edge_condition])
            or (
                self.condition_logic.condition_is_signed_positive_of_param(divergence_guard, param)
                and self.condition_logic.condition_is_signed_nonpositive_of_param(edge_condition, param)
            )
        )

    @staticmethod
    def tuple_field_from_structural_proof(
        proof: Tuple[Any, ...],
        field_name: str,
    ) -> Tuple[Any, ...]:
        for item in proof or ():
            if isinstance(item, tuple) and len(item) == 2 and item[0] == field_name:
                value = item[1]
                return tuple(value) if isinstance(value, (tuple, list)) else (value,)
        return ()

    @staticmethod
    def field_value_from_structural_proof(
        proof: Tuple[Any, ...],
        field_name: str,
    ) -> Any:
        for item in proof or ():
            if isinstance(item, tuple) and len(item) == 2 and item[0] == field_name:
                return item[1]
        return None

    @staticmethod
    def condition_identity_key(condition: Condition) -> Tuple[Any, ...]:
        return condition_identity_key(condition)

    def conditional_progress_guard_keys_from_structural_proof(
        self,
        proof: Tuple[Any, ...],
    ) -> Dict[int, Tuple[Any, ...]]:
        result: Dict[int, Tuple[Any, ...]] = {}
        for item in self.tuple_field_from_structural_proof(proof, "conditional_progress_guard_keys"):
            if not isinstance(item, tuple) or len(item) != 2:
                continue
            index, key = item
            if not isinstance(key, tuple):
                continue
            try:
                result[int(index)] = key
            except Exception:
                continue
        return result

    def condition_for_identity_key(
        self,
        key: Tuple[Any, ...],
        conditions: Sequence[Condition],
    ) -> Optional[Condition]:
        if not isinstance(key, tuple):
            return None
        for condition in conditions or ():
            if condition is not None and self.condition_identity_key(condition) == key:
                return condition
        return None

    def conditional_progress_guards_contradict_invariant(
        self,
        guard_keys: Dict[int, Tuple[Any, ...]],
        *,
        target_conditions: Sequence[Condition],
        invariant_conditions: Sequence[Condition],
    ) -> bool:
        if not guard_keys:
            return False
        for guard_key in guard_keys.values():
            guard = self.condition_for_identity_key(guard_key, target_conditions)
            if guard is None:
                return False
            try:
                if ConditionSMTOracle.conjunction_is_unsat([guard] + list(invariant_conditions or ())) is not True:
                    return False
            except AnalysisLimitation:
                # Issue #106 PR-106-0: 解析の限界は「回復可能な失敗」ではない。ここで
                # 握り潰すと pair の打ち切りが遅れるので、そのまま上へ返す。
                raise
            except Exception:
                return False
        return True

    def conditions_have_contradictory_pair(
        self,
        left: Sequence[Condition],
        right: Sequence[Condition],
    ) -> bool:
        for left_condition in left or ():
            if left_condition is None:
                continue
            for right_condition in right or ():
                if right_condition is None:
                    continue
                if (
                    left_condition.negate().equals(right_condition)
                    or right_condition.negate().equals(left_condition)
                    or ConditionNormalizer.are_equivalent(left_condition.negate(), right_condition)
                    or ConditionNormalizer.are_equivalent(right_condition.negate(), left_condition)
                ):
                    return True
                try:
                    if ConditionSMTOracle.conjunction_is_unsat([left_condition, right_condition]) is True:
                        return True
                except AnalysisLimitation:
                    # Issue #106 PR-106-0: 解析の限界は「回復可能な失敗」ではない。ここで
                    # 握り潰すと pair の打ち切りが遅れるので、そのまま上へ返す。
                    raise
                except Exception:
                    continue
        return False

    def state_phi_feeds_positive_loop_guard(
        self,
        high_function,
        *,
        summarizer: StructuralRecurrenceSummarizer,
        header_block,
        backedge_indices: Sequence[int],
        state_phi,
        state_placeholder: Expression,
        target_conditions: Sequence[Condition],
        allow_latch_progress_guard: bool,
    ) -> bool:
        state_output = getattr(state_phi, "getOutput", lambda: None)()
        if state_output is None:
            return False
        positive_guard = Expression.binary_op("INT_SLESS", Expression.constant(0, size=state_placeholder.size or 4), state_placeholder)
        positive_guard.size = 1
        candidate_blocks = [header_block]
        try:
            in_size = int(getattr(header_block, "getInSize", lambda: 0)() or 0)
        except Exception:
            in_size = 0
        for backedge_index in backedge_indices or ():
            if 0 <= int(backedge_index) < in_size:
                try:
                    predecessor = header_block.getIn(int(backedge_index))
                except Exception:
                    predecessor = None
                if predecessor is not None and predecessor not in candidate_blocks:
                    candidate_blocks.append(predecessor)
        header_key = self.block_graph.block_debug_key(header_block)
        for block in candidate_blocks:
            cbranch = summarizer._find_cbranch_op(block)
            if cbranch is None or summarizer._safe_pcode_input_count(cbranch) < 2:
                continue
            if block is not header_block:
                successor_keys = {self.block_graph.block_debug_key(successor) for successor in self.block_graph.block_successors(block)}
                if header_key not in successor_keys:
                    continue
            guard_expr = summarizer._build_pcode_expression(
                cbranch.getInput(1),
                placeholders={state_output: state_placeholder},
            )
            if guard_expr is None:
                continue
            if self.condition_logic.expressions_same_key(
                summarizer._canonicalize_expression(guard_expr),
                summarizer._canonicalize_expression(positive_guard),
            ):
                return True
            if allow_latch_progress_guard and self.expression_is_positive_after_unit_progress_guard(
                guard_expr,
                state_placeholder,
                target_conditions,
            ):
                return True
        return False

    def expression_is_positive_after_unit_progress_guard(
        self,
        expr: Optional[Expression],
        state_placeholder: Expression,
        conditions: Sequence[Condition],
    ) -> bool:
        current = expr
        while (
            current is not None
            and getattr(current, "expr_type", None) == ExpressionType.UNARY_OP
            and getattr(current, "operator", None) in {"COPY", "CAST", "SUBPIECE", "INT_ZEXT", "INT_SEXT"}
            and len(tuple(getattr(current, "operands", ()) or ())) == 1
        ):
            current = tuple(getattr(current, "operands", ()) or ())[0]
        if current is None or getattr(current, "expr_type", None) != ExpressionType.BINARY_OP:
            return False
        if getattr(current, "operator", None) != "INT_SLESS":
            return False
        operands = tuple(getattr(current, "operands", ()) or ())
        if len(operands) != 2 or self.constant_values.constant_int_value(operands[0]) != 0:
            return False
        right = operands[1]
        if self.placeholder_algebra.expression_is_placeholder_minus_one_under_conditions(
            right,
            state_placeholder,
            conditions,
        ):
            return True
        if getattr(right, "expr_type", None) != ExpressionType.BINARY_OP:
            return False
        if getattr(right, "operator", None) != "INT_SUB":
            return False
        right_operands = tuple(getattr(right, "operands", ()) or ())
        if len(right_operands) != 2:
            return False
        return self.condition_logic.expressions_same_key(right_operands[0], state_placeholder) and self.placeholder_algebra.expression_is_one_under_conditions(
            right_operands[1],
            conditions,
        )

    def reachable_cycle_keys(
        self,
        reachable: Set[Any],
        adjacency: Mapping[Any, Sequence[Any]],
    ) -> Set[Any]:
        visiting: Set[Any] = set()
        visited: Set[Any] = set()
        cycle_nodes: Set[Any] = set()

        def dfs(key: Any, path: List[Any]) -> None:
            if key in visiting:
                try:
                    start = path.index(key)
                    cycle_nodes.update(path[start:])
                except ValueError:
                    cycle_nodes.add(key)
                return
            if key in visited:
                return
            visiting.add(key)
            path.append(key)
            for successor in adjacency.get(key, ()) or ():
                if successor in reachable:
                    dfs(successor, path)
            path.pop()
            visiting.remove(key)
            visited.add(key)

        for key in sorted(reachable, key=str):
            dfs(key, [])
        return cycle_nodes

    def high_function_has_cfg_cycle(self, high_function) -> bool:
        blocks = list(self.block_graph.iter_high_basic_blocks(high_function))
        block_keys = {self.block_graph.block_debug_key(block) for block in blocks}
        visiting: Set[Any] = set()
        visited: Set[Any] = set()

        def visit(block) -> bool:
            key = self.block_graph.block_debug_key(block)
            if key in visiting:
                return True
            if key in visited:
                return False
            visiting.add(key)
            for succ in self.block_graph.block_successors(block):
                if self.block_graph.block_debug_key(succ) not in block_keys:
                    continue
                if visit(succ):
                    return True
            visiting.remove(key)
            visited.add(key)
            return False

        for block in blocks:
            if visit(block):
                return True
        return False


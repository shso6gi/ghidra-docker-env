# -*- coding: utf-8 -*-
"""式木全体のPHI展開モジュール（網羅性改善版）"""

from dataclasses import dataclass
from typing import Callable, List, Optional, Set, Dict, Tuple, Any, Hashable
from ..model import Expression, Condition, ExpressionType, StorageInfo, CallTargetRef, UnknownValueRef, CanonicalLocation
from ..analysis.condition import ConditionSimplifier, ConditionNormalizer
from ..analysis.debug import summarize_expression, summarize_condition
from ..config.settings import (
    EXPANDER_MAX_COMBINATION_ATTEMPTS,
    EXPANDER_MAX_OPERATION_CASES,
)
from ..analysis.effect_summary import (
    _reduce_expression_under_conditions,
    _resolve_call_target_ref,
    _recover_call_argument_expressions,
    _resolve_call_argument_expression,
    _expression_maps_to_parameter,
    resolve_call_targets,
    _expressions_equivalent,
    canonicalize_location,
    canonicalize_param_location,
    canonicalize_post_state_subexpressions,
    collapse_post_state_expr_to_canonical_memory,
    expression_contains_synthetic_location_reads,
    memory_expression_for_location,
    normalize_post_state_expression,
    rewrite_loads_from_effects,
    rewrite_location_read_from_effects,
    rewrite_observed_loads_from_effects,
)
from ..analysis.memory_resolver import concretize_readonly_loads


class ExpandedValue:
    """展開された値と条件のペア"""
    
    def __init__(self, value: Expression, conditions: List[Condition]):
        self.value = value
        self.conditions = conditions
    
    def is_valid(self) -> bool:
        """条件が矛盾していないかチェック"""
        return not ConditionSimplifier.is_contradiction(self.conditions)
    
    def get_condition_signature(self) -> Hashable:
        """
        条件のシグネチャを取得（重複排除用）
        
        条件を正規化して、ソート済みの文字列として返す
        """
        return ConditionNormalizer.conditions_signature(self.conditions)
    
    def __repr__(self):
        conds = [c.to_string() for c in self.conditions]
        return f"ExpandedValue(value={self.value.to_string()}, conds={conds})"


@dataclass(frozen=True)
class MultiequalBranchObservation:
    """Object-centric branch observation for a MULTIEQUAL input edge."""

    value: Expression
    conditions: Tuple[Condition, ...]
    predecessor_index: int
    input_object_key: Optional[Hashable]
    observed_location: Optional[CanonicalLocation]


class ExpressionExpander:
    """
    式木全体を展開し、PHIノードを解決する
    """
    
    # 展開の上限設定
    MAX_CASES_PER_MULTIEQUAL = 16  # 1つのMULTIEQUALから生成する最大ケース数
    COMMUTATIVE_ASSOCIATIVE_OPS = frozenset(
        [
            "INT_ADD", "ADD", "+",
            "INT_MULT", "MULT", "*",
            "INT_AND", "AND", "&",
            "INT_OR", "OR", "|",
            "INT_XOR", "XOR", "^",
        ]
    )
    
    def __init__(
        self,
        tracer,
        condition_tracker,
        debug: bool = False,
        call_resolver: Optional[Callable[[CallTargetRef, List[Expression]], Optional[List["ExpandedValue"]]]] = None,
        effect_summary=None,
        parameters: Optional[List[Dict[str, Any]]] = None,
        resolve_callee_parameters: Optional[Callable[[CallTargetRef], List[Dict[str, Any]]]] = None,
        read_memory_value: Optional[Callable[[int, int], Optional[int]]] = None,
        image_base: Optional[int] = None,
        record_deferred_call: Optional[Callable[[CallTargetRef, List[Expression]], Any]] = None,
    ):
        self.tracer = tracer
        self.condition_tracker = condition_tracker
        self.debug = debug
        self.call_resolver = call_resolver
        self.effect_summary = effect_summary
        self.parameters = list(parameters or [])
        self.resolve_callee_parameters = resolve_callee_parameters
        self.read_memory_value = read_memory_value
        self.image_base = image_base
        self.record_deferred_call = record_deferred_call
        self._expanding_ops: Set[str] = set()
        self._debug_message_limit = 4000
        self._debug_message_count = 0
        self._debug_suppressed = False
        self._max_operation_cases = int(EXPANDER_MAX_OPERATION_CASES)
        self._max_combination_attempts = int(EXPANDER_MAX_COMBINATION_ATTEMPTS)
    
    def _debug_print(self, msg: str, indent: int = 0):
        if not self.debug:
            return
        if self._debug_message_count >= self._debug_message_limit:
            if not self._debug_suppressed:
                prefix = "  " * indent
                print(
                    f"{prefix}[Expander] debug output suppressed after "
                    f"{self._debug_message_limit} messages"
                )
                self._debug_suppressed = True
            return
        self._debug_message_count += 1
        prefix = "  " * indent
        print(f"{prefix}[Expander] {msg}")

    def _debug_available(self) -> bool:
        return self.debug and self._debug_message_count < self._debug_message_limit

    def _debug_expr_summary(self, expr: Optional[Expression], max_depth: int = 4) -> str:
        """巨大式の full render を避けたデバッグ用サマリー。"""
        if not self._debug_available():
            return "<debug-suppressed>"
        return summarize_expression(expr, max_depth=max_depth)

    def _debug_condition_summary(self, condition: Optional[Condition], max_depth: int = 4) -> str:
        if not self._debug_available():
            return "<debug-suppressed>"
        return summarize_condition(condition, max_depth=max_depth)

    def _debug_expr(self, label: str, expr: Optional[Expression], indent: int = 0) -> None:
        if not self._debug_available():
            return
        self._debug_print(f"{label}{self._debug_expr_summary(expr)}", indent)

    def _normalize_expansion_conditions(
        self,
        conditions: List[Condition],
    ) -> List[Condition]:
        """PHI を含む条件も文脈に応じて簡約した上で展開に流す。"""
        if not conditions:
            return []
        return ConditionSimplifier.simplify_conditions(list(conditions))

    def _expansion_expression_signature(self, expr: Optional[Expression]):
        """展開中の重複排除に使う、可換結合演算を吸収した式シグネチャ。"""
        if expr is None:
            return ("none",)

        if (
            expr.expr_type == ExpressionType.BINARY_OP
            and expr.operator in self.COMMUTATIVE_ASSOCIATIVE_OPS
            and len(expr.operands) == 2
        ):
            flattened: List[Expression] = []
            self._collect_commutative_operands(expr, expr.operator, flattened)
            operand_sigs = sorted(
                self._expansion_expression_signature(operand) for operand in flattened
            )
            return (
                "commutative",
                expr.operator or "",
                int(expr.size or 0),
                int(expr.get_bit_width() or 0),
                tuple(operand_sigs),
            )

        return ConditionNormalizer.expression_signature(expr)

    def _collect_commutative_operands(
        self,
        expr: Expression,
        operator: str,
        out: List[Expression],
    ) -> None:
        if (
            expr.expr_type == ExpressionType.BINARY_OP
            and expr.operator == operator
            and len(expr.operands) == 2
        ):
            self._collect_commutative_operands(expr.operands[0], operator, out)
            self._collect_commutative_operands(expr.operands[1], operator, out)
            return
        out.append(expr)

    def _normalize_expanded_value(
        self,
        ev: ExpandedValue,
    ) -> ExpandedValue:
        normalized_conditions = ConditionSimplifier.simplify_conditions(list(ev.conditions))
        reduced_value = _reduce_expression_under_conditions(ev.value, normalized_conditions)
        normalized_value = reduced_value if reduced_value is not None else ev.value
        return ExpandedValue(normalized_value, normalized_conditions)

    def _prefer_expanded_value(
        self,
        candidate: ExpandedValue,
        incumbent: ExpandedValue,
    ) -> bool:
        candidate_unknown = candidate.value.expr_type == ExpressionType.UNKNOWN
        incumbent_unknown = incumbent.value.expr_type == ExpressionType.UNKNOWN
        if candidate_unknown != incumbent_unknown:
            return not candidate_unknown
        return len(candidate.conditions) < len(incumbent.conditions)

    def _finalize_combined_results(
        self,
        mnemonic: str,
        values: List[ExpandedValue],
        base_conditions: List[Condition],
        depth: int,
        over_budget: bool = False,
    ) -> List[ExpandedValue]:
        limit = self._max_operation_cases
        deduped = self._deduplicate_expanded_values(
            values,
            depth,
            limit=limit,
            label=f"{mnemonic} combinations",
        )

        if over_budget:
            budget_unknown = ExpandedValue(
                Expression.unknown(
                    f"{mnemonic}_budget_exceeded",
                    runtime_ref=UnknownValueRef.budget_exceeded(operation=mnemonic),
                ),
                list(base_conditions),
            )
            budget_key = (
                self._expansion_expression_signature(budget_unknown.value),
                budget_unknown.get_condition_signature(),
            )
            existing_keys = {
                (self._expansion_expression_signature(ev.value), ev.get_condition_signature())
                for ev in deduped
            }
            if budget_key not in existing_keys:
                deduped.append(budget_unknown)

        if deduped:
            return deduped

        if over_budget:
            return [
                ExpandedValue(
                    Expression.unknown(
                        f"{mnemonic}_budget_exceeded",
                        runtime_ref=UnknownValueRef.budget_exceeded(operation=mnemonic),
                    ),
                    list(base_conditions),
                )
            ]

        # All candidate combinations were contradictory. Emitting an UNKNOWN branch
        # here pollutes the surrounding control-flow summary with an impossible case.
        self._debug_print(
            f"  All {mnemonic} combinations contradictory under current conditions; dropping branch",
            depth,
        )
        return []

    def _coerce_value_to_output_size(self, value: Expression, output_size: int) -> Expression:
        """CALL 出力サイズに合わせて値式を正規化する。"""
        if value is None or output_size <= 0:
            return value

        current_size = getattr(value, "size", 0) or 0
        if current_size <= 0:
            value.size = output_size
            return value

        if current_size == output_size:
            return value

        # callee summary が内部で幅拡張された式を返しても、CALL 出力 varnode が
        # 実際の幅を決める。広すぎる値は下位バイトへ切り詰める。
        if current_size > output_size:
            truncated = Expression.binary_op(
                "SUBPIECE",
                value,
                Expression.constant(0, size=max(1, current_size)),
            )
            truncated.size = output_size
            return truncated

        return value
    
    def expand_from_varnode(
        self,
        varnode,
        base_conditions: List[Condition],
        depth: int = 0
    ) -> List[ExpandedValue]:
        """Varnodeから式を展開"""
        if varnode is None:
            return [ExpandedValue(Expression.unknown("null"), base_conditions)]
        
        if depth > 30:
            self._debug_print(f"Max depth reached", depth)
            return [ExpandedValue(Expression.unknown("max_depth"), base_conditions)]
        
        def_op = varnode.getDef()
        
        if def_op is None:
            value = self.tracer.trace_varnode(varnode, depth, use_cache=False)
            return [ExpandedValue(value, base_conditions)]
        
        mnemonic = def_op.getMnemonic()
        self._debug_print(f"Expanding {mnemonic} at depth {depth}", depth)
        
        if mnemonic == "MULTIEQUAL":
            # MULTIEQUALは制御フローの合流点
            return self._expand_multiequal(def_op, base_conditions, depth)
        
        elif mnemonic in ("COPY", "CAST"):
            if def_op.getNumInputs() >= 1:
                return self.expand_from_varnode(def_op.getInput(0), base_conditions, depth + 1)
            return [ExpandedValue(Expression.unknown(f"{mnemonic}_no_input"), base_conditions)]
        
        else:
            return self._expand_operation(def_op, base_conditions, depth)
    
    def _expand_multiequal(
        self,
        multiequal_op,
        base_conditions: List[Condition],
        depth: int
    ) -> List[ExpandedValue]:
        """MULTIEQUALを展開"""
        op_key = self.tracer._get_stable_op_key(multiequal_op)
        
        if op_key in self._expanding_ops:
            self._debug_print(f"Circular MULTIEQUAL detected: {op_key}", depth)
            return [ExpandedValue(Expression.unknown("phi_circular"), list(base_conditions))]
        
        self._expanding_ops.add(op_key)
        
        try:
            return self._expand_multiequal_internal(multiequal_op, base_conditions, depth)
        finally:
            self._expanding_ops.discard(op_key)
    
    def _expand_multiequal_internal(
        self,
        multiequal_op,
        base_conditions: List[Condition],
        depth: int
    ) -> List[ExpandedValue]:
        """
        MULTIEQUAL展開の内部処理（網羅性改善版）
        
        各MULTIEQUAL入力について、前任ブロックへの全有効パスを列挙し、
        それぞれを別の展開値として扱う。
        
        重要：値だけでなく条件も含めて重複排除を行う。
        """
        phi_parent = multiequal_op.getParent()
        if not phi_parent:
            return [ExpandedValue(Expression.unknown("phi_no_parent"), list(base_conditions))]
        
        num_inputs = multiequal_op.getNumInputs()
        in_size = phi_parent.getInSize()
        
        self._debug_print("=" * 50, depth)
        self._debug_print(f"MULTIEQUAL expansion: inputs={num_inputs}, in_edges={in_size}", depth)
        self._debug_print("=" * 50, depth)
        
        all_expanded: List[ExpandedValue] = []
        canonical_multiequal_location = self._infer_multiequal_location_for_expansion(
            multiequal_op,
            base_conditions,
            depth,
        )
        
        for i in range(num_inputs):
            input_varnode = multiequal_op.getInput(i)
            
            self._debug_print(f"Input[{i}] ----", depth)
            
            # 前任ブロック情報を取得
            if i >= in_size:
                self._debug_print(f"  No corresponding in_edge (i={i} >= in_size={in_size})", depth + 1)
                continue
            
            in_block = phi_parent.getIn(i)
            if not in_block:
                self._debug_print(f"  in_block is None", depth + 1)
                continue
            
            in_block_info = self.condition_tracker.get_block_by_hash(in_block)
            if not in_block_info:
                self._debug_print(f"  in_block_info not found", depth + 1)
                continue
            
            self._debug_print(f"  pred_block: index={in_block_info.index}", depth + 1)
            
            # 値をトレース（デバッグ用）
            try:
                input_conditions = []
                traced_value = self.tracer.trace_varnode(input_varnode, depth + 1, use_cache=False)
                traced_value = self._canonicalize_traced_expression(traced_value, input_conditions)
                self._debug_expr("  traced_value: ", traced_value, depth + 1)
                
                # SMT表現も取得（エラー時はスキップ）
                try:
                    smt_str = traced_value.to_smt()
                    if len(smt_str) > 100:
                        smt_str = smt_str[:100] + "..."
                    self._debug_print(f"  traced_smt: {smt_str}", depth + 1)
                except Exception as e:
                    self._debug_print(f"  traced_smt: (error: {e})", depth + 1)
            except Exception as e:
                self._debug_print(f"  traced_value: (error: {e})", depth + 1)
            
            # ★★★ 改善点：全有効パスを取得 ★★★
            all_valid_paths = self.condition_tracker.get_all_valid_paths_to_block(
                target_block=in_block_info
            )
            
            self._debug_print(f"  valid_paths: {len(all_valid_paths)}", depth + 1)
            
            # エッジ条件を取得（共通）
            edge_cond = self._get_edge_condition(in_block_info, phi_parent)
            if edge_cond:
                edge_str = ConditionNormalizer.get_simplified_string(edge_cond)
                self._debug_print(f"  edge_condition: {edge_str}", depth + 1)
            
            # 各パスについて展開
            cases_emitted = 0
            for path_idx, path_conditions in enumerate(all_valid_paths):
                # パス条件 + エッジ条件を結合
                input_conditions = list(base_conditions) + path_conditions.copy()
                if edge_cond:
                    input_conditions.append(edge_cond)
                input_conditions = self._normalize_expansion_conditions(input_conditions)
                
                if self.debug:
                    self._debug_print(f"  Path[{path_idx}]: {len(path_conditions)} condition(s)", depth + 1)
                    for pc in path_conditions:
                        pc_str = ConditionNormalizer.get_simplified_string(pc)
                        self._debug_print(f"    - {pc_str}", depth + 2)
                
                # 矛盾チェック
                if ConditionSimplifier.is_contradiction(input_conditions):
                    self._debug_print(f"  Path[{path_idx}] -> SKIP (contradictory)", depth + 1)
                    continue

                if canonical_multiequal_location is not None:
                    canonical_value = self._resolve_canonical_location_under_conditions(
                        canonical_multiequal_location,
                        input_conditions,
                        depth + 1,
                    )
                    if canonical_value is not None:
                        all_expanded.append(ExpandedValue(canonical_value, input_conditions))
                        cases_emitted += 1
                        if self.debug:
                            self._debug_expr(
                                f"  Path[{path_idx}] -> EMIT multiequal canonical: ",
                                canonical_value,
                                depth + 1,
                            )
                        continue

                if not self._varnode_requires_recursive_expansion(input_varnode):
                    canonical_value = self._trace_and_canonicalize_input_value(
                        input_varnode,
                        input_conditions,
                        depth + 1,
                    )
                    if canonical_value is not None:
                        all_expanded.append(ExpandedValue(canonical_value, input_conditions))
                        cases_emitted += 1
                        if self.debug:
                            self._debug_expr(
                                f"  Path[{path_idx}] -> EMIT canonicalized: ",
                                canonical_value,
                                depth + 1,
                            )
                        continue
                
                # 入力を再帰的に展開
                expanded_inputs = self._expand_input_varnode(
                    input_varnode, 
                    input_conditions, 
                    depth + 1
                )
                
                for ev in expanded_inputs:
                    if ev.is_valid():
                        all_expanded.append(ev)
                        cases_emitted += 1
                        if self.debug:
                            self._debug_expr(
                                f"  Path[{path_idx}] -> EMIT: ",
                                ev.value,
                                depth + 1,
                            )
                    else:
                        self._debug_print(
                            f"  Path[{path_idx}] -> SKIP (invalid after expansion)",
                            depth + 1
                        )
            
            self._debug_print(f"  cases_emitted: {cases_emitted}", depth + 1)
        
        if all_expanded:
            # ★★★ 改善点：値と条件の両方を考慮して重複排除 ★★★
            merged = self._deduplicate_expanded_values(all_expanded, depth)
            self._debug_print("=" * 50, depth)
            self._debug_print(f"MULTIEQUAL -> {len(merged)} branches (after dedup)", depth)
            self._debug_print("=" * 50, depth)
            return merged
        
        self._debug_print("=" * 50, depth)
        self._debug_print(f"MULTIEQUAL -> 0 branches (no valid branches)", depth)
        self._debug_print("=" * 50, depth)
        return [ExpandedValue(Expression.unknown("phi_no_valid_branch"), list(base_conditions))]
    
    def _deduplicate_expanded_values(
        self,
        values: List[ExpandedValue],
        depth: int,
        limit: Optional[int] = None,
        label: str = "expanded values",
    ) -> List[ExpandedValue]:
        """
        展開値の重複排除（値と条件の両方を考慮）
        
        Args:
            values: 展開値のリスト
            depth: デバッグ用の深さ
        
        Returns:
            重複排除後のリスト（上限あり）
        """
        if not values:
            return []
        
        self._debug_print(f"Deduplicating {len(values)} {label}...", depth)
        
        # (value_sig, condition_signature) でグループ化
        groups: Dict[Tuple[str, str], ExpandedValue] = {}

        for ev in values:
            normalized = self._normalize_expanded_value(ev)
            key = (
                self._expansion_expression_signature(normalized.value),
                normalized.get_condition_signature(),
            )
            current = groups.get(key)
            if current is None or self._prefer_expanded_value(normalized, current):
                groups[key] = normalized
        
        self._debug_print(f"  Grouped into {len(groups)} unique (value, condition) pairs", depth)
        
        # 各グループから代表を1つ選ぶ（条件が最も短いもの）
        result = list(groups.values())
        
        # 上限チェック
        applied_limit = self.MAX_CASES_PER_MULTIEQUAL if limit is None else limit
        if len(result) > applied_limit:
            self._debug_print(
                f"  WARNING: Too many cases ({len(result)}), limiting to {applied_limit}",
                depth
            )
            # 条件が短い順にソート
            result = sorted(result, key=lambda e: len(e.conditions))
            result = result[:applied_limit]
        
        self._debug_print(f"  Final result: {len(result)} unique cases", depth)
        return result

    def _infer_multiequal_location_for_expansion(
        self,
        multiequal_op,
        base_conditions: List[Condition],
        depth: int,
    ):
        if self.effect_summary is None or not getattr(self.effect_summary, "effects", None):
            return None
        if not self.parameters or self.condition_tracker is None:
            return None

        observations = self._collect_multiequal_branch_observations(
            multiequal_op,
            base_conditions,
            depth + 1,
        )
        if not observations:
            return None

        inferred = self._infer_multiequal_canonical_location(
            observations,
            depth + 1,
        )
        if inferred is not None and self.debug:
            candidate = memory_expression_for_location(inferred, self.parameters)
            if candidate is not None:
                self._debug_print(
                    "Using canonical MULTIEQUAL location for branch expansion: "
                    f"{self._debug_expr_summary(candidate)}",
                    depth,
                )
        return inferred

    def _resolve_canonical_location_under_conditions(
        self,
        location,
        conditions: List[Condition],
        depth: int,
    ) -> Optional[Expression]:
        if self.effect_summary is None or not getattr(self.effect_summary, "effects", None):
            return None
        if not self.parameters:
            return None

        candidate = memory_expression_for_location(location, self.parameters)
        if candidate is None:
            return None

        rewritten = rewrite_loads_from_effects(
            candidate,
            conditions,
            self.effect_summary.effects,
            self.parameters,
        )
        reduced = _reduce_expression_under_conditions(rewritten, conditions)
        resolved = reduced if reduced is not None else rewritten
        if self._expression_contains_unknown_or_call(resolved):
            return None
        if self._expression_contains_phi(resolved):
            if self.debug:
                self._debug_print(
                    "Canonical MULTIEQUAL location still contains PHI under current conditions",
                    depth,
                )
            return None
        return resolved
    
    def _expand_input_varnode(
        self,
        varnode,
        conditions: List[Condition],
        depth: int
    ) -> List[ExpandedValue]:
        """MULTIEQUAL入力のVarnodeを再帰的に展開"""
        if varnode is None:
            return [ExpandedValue(Expression.unknown("null"), conditions)]
        
        if depth > 30:
            self._debug_print(f"Max depth in input varnode", depth)
            value = self.tracer.trace_varnode(varnode, depth, use_cache=False)
            return [ExpandedValue(value, conditions)]
        
        # Varnodeのサイズを取得
        varnode_size = varnode.getSize()
        
        def_op = varnode.getDef()
        
        if def_op is None:
            value = self.tracer.trace_varnode(varnode, depth, use_cache=False)
            # サイズを確実に設定
            if value.size == 0:
                value.size = varnode_size
            return [ExpandedValue(value, conditions)]
        
        mnemonic = def_op.getMnemonic()
        
        if mnemonic == "MULTIEQUAL":
            collapsed = self._collapse_nested_multiequal_to_memory(def_op, conditions, depth)
            if collapsed is not None:
                return [ExpandedValue(collapsed, conditions)]
            # ネストされたMULTIEQUALを展開し、条件を組み合わせる
            self._debug_print(f"Nested MULTIEQUAL found", depth)
            nested_expanded = self._expand_multiequal(def_op, conditions, depth)
            result = []
            for ev in nested_expanded:
                combined_conditions = conditions + ev.conditions
                if not ConditionSimplifier.is_contradiction(combined_conditions):
                    # サイズを確実に設定
                    if ev.value.size == 0:
                        ev.value.size = varnode_size
                    result.append(ExpandedValue(ev.value, combined_conditions))
            return result if result else [ExpandedValue(Expression.unknown("nested_phi_fail"), conditions)]
        
        elif mnemonic in ("COPY", "CAST"):
            if def_op.getNumInputs() >= 1:
                result = self._expand_input_varnode(def_op.getInput(0), conditions, depth + 1)
                # サイズを更新（出力サイズを使用）
                output = def_op.getOutput()
                if output:
                    output_size = output.getSize()
                    for ev in result:
                        if ev.value.size == 0:
                            ev.value.size = output_size
                return result
            return [ExpandedValue(Expression.unknown(f"{mnemonic}_no_input"), conditions)]
        
        else:
            # 通常の演算 - 入力にMULTIEQUALがあるかチェックして展開
            result = self._expand_input_operation(def_op, conditions, depth)
            # 出力サイズを設定
            output = def_op.getOutput()
            if output:
                output_size = output.getSize()
                for ev in result:
                    if ev.value.size == 0:
                        ev.value.size = output_size
            return result

    def _collapse_nested_multiequal_to_memory(
        self,
        multiequal_op,
        conditions: List[Condition],
        depth: int,
    ) -> Optional[Expression]:
        if self.effect_summary is None or not getattr(self.effect_summary, "effects", None):
            return None
        if not self.parameters:
            return None

        resolved_post_state = self._resolve_nested_multiequal_via_effect_summary(
            multiequal_op,
            conditions,
            depth,
        )
        if resolved_post_state is not None:
            return resolved_post_state

        try:
            traced = self.tracer._trace_pcode_op(multiequal_op, depth, use_cache=False)
        except Exception:
            return None

        collapsed = collapse_post_state_expr_to_canonical_memory(
            traced,
            self.effect_summary.effects,
            self.parameters,
            return_conditions=conditions,
        )
        if collapsed is not None:
            self._debug_print(
                f"Collapsed nested MULTIEQUAL to canonical memory: {self._debug_expr_summary(collapsed)}",
                depth,
            )
        return collapsed

    def _resolve_nested_multiequal_via_effect_summary(
        self,
        multiequal_op,
        current_conditions: List[Condition],
        depth: int,
    ) -> Optional[Expression]:
        observations = self._collect_multiequal_branch_observations(
            multiequal_op,
            current_conditions,
            depth + 1,
        )
        if not observations:
            return None

        inferred_location = self._infer_multiequal_canonical_location(
            observations,
            depth + 1,
        )
        if inferred_location is None:
            if self._debug_available():
                branch_summaries = [
                    f"{self._debug_expr_summary(observation.value)} @ "
                    f"{[self._debug_condition_summary(c) for c in observation.conditions]}"
                    for observation in observations
                ]
                self._debug_print(
                    f"Effect-summary inference failed for nested MULTIEQUAL: {branch_summaries}",
                    depth,
                )
            return None

        candidate = memory_expression_for_location(inferred_location, self.parameters)
        if candidate is None:
            return None

        assert self.effect_summary is not None
        rewritten = rewrite_loads_from_effects(
            candidate,
            current_conditions,
            self.effect_summary.effects,
            self.parameters,
        )
        reduced = _reduce_expression_under_conditions(rewritten, current_conditions)
        resolved = reduced if reduced is not None else rewritten
        if self.debug:
            self._debug_print(
                "Resolved nested MULTIEQUAL via effect summary: "
                f"{self._debug_expr_summary(candidate)} -> {self._debug_expr_summary(resolved)}",
                depth,
            )
        return resolved

    def _collect_multiequal_branch_observations(
        self,
        multiequal_op,
        base_conditions: List[Condition],
        depth: int,
    ) -> List[MultiequalBranchObservation]:
        if not hasattr(multiequal_op, "getParent"):
            if self.debug:
                self._debug_print(
                    "Skipping effect-summary inference for nested MULTIEQUAL without parent block",
                    depth,
                )
            return []
        phi_parent = multiequal_op.getParent()
        if not phi_parent or self.condition_tracker is None:
            return []

        observations: List[MultiequalBranchObservation] = []
        num_inputs = multiequal_op.getNumInputs()
        in_size = phi_parent.getInSize()

        for i in range(num_inputs):
            input_varnode = multiequal_op.getInput(i)
            if i >= in_size:
                continue

            in_block = phi_parent.getIn(i)
            if not in_block:
                continue

            in_block_info = self.condition_tracker.get_block_by_hash(in_block)
            if not in_block_info:
                continue

            all_valid_paths = self.condition_tracker.get_all_valid_paths_to_block(
                target_block=in_block_info
            )
            edge_cond = self._get_edge_condition(in_block_info, phi_parent)

            for path_conditions in all_valid_paths:
                branch_conditions = list(base_conditions) + path_conditions.copy()
                if edge_cond:
                    branch_conditions.append(edge_cond)
                branch_conditions = self._normalize_expansion_conditions(branch_conditions)
                if ConditionSimplifier.is_contradiction(branch_conditions):
                    continue
                try:
                    branch_value = self.tracer.trace_varnode(
                        input_varnode,
                        depth,
                        use_cache=False,
                    )
                except Exception:
                    continue
                if self._expression_contains_unknown_or_call(branch_value):
                    continue
                observations.append(
                    MultiequalBranchObservation(
                        value=branch_value,
                        conditions=tuple(branch_conditions),
                        predecessor_index=getattr(in_block_info, "index", -1),
                        input_object_key=self._stable_multiequal_input_object_key(input_varnode),
                        observed_location=self._observed_location_for_expression(branch_value),
                    )
                )

        return observations

    def _infer_multiequal_canonical_location(
        self,
        observations,
        depth: int,
    ):
        if not observations or self.effect_summary is None:
            return None

        normalized_observations: List[MultiequalBranchObservation] = []
        for observation in observations:
            if isinstance(observation, MultiequalBranchObservation):
                normalized_observations.append(observation)
                continue
            value = getattr(observation, "value", None)
            conditions = tuple(getattr(observation, "conditions", ()) or ())
            if value is None:
                continue
            normalized_observations.append(
                MultiequalBranchObservation(
                    value=value,
                    conditions=conditions,
                    predecessor_index=-1,
                    input_object_key=None,
                    observed_location=self._observed_location_for_expression(value),
                )
            )

        observations = normalized_observations
        if not observations:
            return None

        observed_locations = [obs.observed_location for obs in observations if obs.observed_location is not None]
        if observed_locations:
            first = observed_locations[0]
            if all(location == first for location in observed_locations[1:]):
                if self.debug:
                    self._debug_print(
                        "Inferred MULTIEQUAL canonical location by unanimous object-centric "
                        f"branch observation: {first.base_param} steps={getattr(first, 'steps', ())} "
                        f"offset={first.offset}",
                        depth,
                    )
                return first

        candidate_locations = list({effect.location for effect in self.effect_summary.effects})
        for observed_location in observed_locations:
            if observed_location not in candidate_locations:
                candidate_locations.append(observed_location)
        candidate_locations.sort(
            key=lambda loc: (loc.base_param, getattr(loc, "steps", ()), loc.offset, loc.size),
        )

        for location in candidate_locations:
            candidate = memory_expression_for_location(location, self.parameters)
            if candidate is None:
                continue

            all_match = True
            for observation in observations:
                expected = rewrite_loads_from_effects(
                    candidate,
                    list(observation.conditions),
                    self.effect_summary.effects,
                    self.parameters,
                )
                reduced_expected = _reduce_expression_under_conditions(expected, list(observation.conditions))
                observed = _reduce_expression_under_conditions(observation.value, list(observation.conditions))
                observed = observed if observed is not None else observation.value
                reduced_expected = reduced_expected if reduced_expected is not None else expected
                if not _expressions_equivalent(observed, reduced_expected):
                    all_match = False
                    break

            if all_match:
                if self.debug:
                    self._debug_print(
                        f"Inferred MULTIEQUAL canonical location by branch match: {self._debug_expr_summary(candidate)}",
                        depth,
                    )
                return location

        return None

    def _stable_multiequal_input_object_key(self, varnode) -> Optional[Hashable]:
        if varnode is None:
            return None
        try:
            high_var = varnode.getHigh()
        except Exception:
            high_var = None
        if high_var is not None:
            try:
                representative = high_var.getRepresentative()
            except Exception:
                representative = None
            try:
                symbol = high_var.getSymbol()
                symbol_name = symbol.getName() if symbol is not None else None
            except Exception:
                symbol_name = None
            if representative is not None:
                try:
                    rep_addr = representative.getAddress()
                    rep_space = rep_addr.getAddressSpace().getName() if rep_addr is not None else "?"
                    rep_offset = representative.getOffset()
                    rep_size = representative.getSize()
                    return ("high", symbol_name, rep_space, rep_offset, rep_size)
                except Exception:
                    return ("high", symbol_name, id(representative))
            return ("high", symbol_name, id(high_var))

        try:
            addr = varnode.getAddress()
            space = addr.getAddressSpace().getName() if addr is not None else "?"
            return ("varnode", space, varnode.getOffset(), varnode.getSize())
        except Exception:
            return None

    def _observed_location_for_expression(
        self,
        expr: Optional[Expression],
    ) -> Optional[CanonicalLocation]:
        if expr is None or not self.parameters:
            return None
        runtime_ref = getattr(expr, "runtime_ref", None)
        if isinstance(runtime_ref, CanonicalLocation):
            return runtime_ref
        if expr.expr_type != ExpressionType.MEMORY or not expr.operands:
            return None
        return canonicalize_param_location(
            expr.operands[0],
            self.parameters,
            size=expr.size,
        )

    def _trace_and_canonicalize_input_value(
        self,
        varnode,
        conditions: List[Condition],
        depth: int,
    ) -> Optional[Expression]:
        if self.effect_summary is None or not getattr(self.effect_summary, "effects", None):
            return None
        if not self.parameters:
            return None

        try:
            traced = self.tracer.trace_varnode(varnode, depth, use_cache=False)
        except Exception:
            return None

        canonicalized = self._canonicalize_traced_expression(traced, conditions)
        if (
            traced is not None
            and canonicalized is traced
            and traced.expr_type == ExpressionType.MEMORY
        ):
            pruned_leaf = collapse_post_state_expr_to_canonical_memory(
                traced,
                self.effect_summary.effects,
                self.parameters,
                return_conditions=conditions,
            )
            if pruned_leaf is not None:
                reduced = _reduce_expression_under_conditions(pruned_leaf, conditions)
                canonicalized = reduced if reduced is not None else pruned_leaf
                if self.debug and not _expressions_equivalent(traced, canonicalized):
                    self._debug_print(
                        "Canonicalized MULTIEQUAL branch memory leaf: "
                        f"{self._debug_expr_summary(traced)} -> {self._debug_expr_summary(canonicalized)}",
                        depth,
                    )
        if canonicalized is traced:
            return None
        if self._expression_contains_unknown_or_call(canonicalized):
            return None
        if self._expression_contains_phi(canonicalized):
            return None
        return canonicalized

    def _varnode_requires_recursive_expansion(self, varnode) -> bool:
        if varnode is None:
            return False
        def_op = varnode.getDef()
        if def_op is None:
            return False
        return self._op_requires_recursive_expansion(def_op)

    def _canonicalize_traced_expression(
        self,
        expr: Expression,
        conditions: List[Condition],
    ) -> Expression:
        if self.effect_summary is None or not getattr(self.effect_summary, "effects", None):
            return expr
        if not self.parameters:
            return expr
        rewritten_observed = rewrite_observed_loads_from_effects(
            expr,
            conditions,
            self.effect_summary.effects,
            self.parameters,
        )
        observed_changed = (
            rewritten_observed is not expr
            and not _expressions_equivalent(rewritten_observed, expr)
        )
        if observed_changed:
            if self.debug:
                self._debug_print(
                    "Observed-load rewrite resolved: "
                    f"{self._debug_expr_summary(expr)} -> {self._debug_expr_summary(rewritten_observed)}",
                    0,
                )
            rewritten_base = rewritten_observed if rewritten_observed is not None else expr
            normalized = normalize_post_state_expression(
                rewritten_base,
                conditions,
                self.effect_summary.effects,
                self.parameters,
            )
            return normalized if normalized is not None else rewritten_base
        canonicalized = canonicalize_post_state_subexpressions(
            expr,
            conditions,
            self.effect_summary.effects,
            self.parameters,
            allow_memory_leaf_collapse=True,
        )
        rewrite_target = canonicalized if canonicalized is not None else expr
        rewritten_post_state = (
            rewrite_loads_from_effects(
                rewrite_target,
                conditions,
                self.effect_summary.effects,
                self.parameters,
            )
            if expression_contains_synthetic_location_reads(rewrite_target)
            else rewrite_target
        )
        reduced = _reduce_expression_under_conditions(
            rewritten_post_state if rewritten_post_state is not None else (canonicalized if canonicalized is not None else expr),
            conditions,
        )
        resolved = reduced if reduced is not None else expr
        if self.read_memory_value is not None and self.parameters:
            concretized = concretize_readonly_loads(
                resolved,
                conditions,
                self.parameters,
                self.read_memory_value,
                self.image_base,
                self.debug,
            )
            if concretized is not None:
                resolved = concretized
        return resolved

    def _expression_contains_unknown_or_call(self, expr: Optional[Expression]) -> bool:
        if expr is None:
            return False
        if expr.expr_type in (ExpressionType.UNKNOWN, ExpressionType.CALL):
            return True
        if expr.expr_type == ExpressionType.PHI and expr.value:
            for cond, value in expr.value:
                if cond is not None and self._expression_contains_unknown_or_call(cond.expression):
                    return True
                if self._expression_contains_unknown_or_call(value):
                    return True
            return False
        for operand in getattr(expr, "operands", []) or []:
            if self._expression_contains_unknown_or_call(operand):
                return True
        return False

    def _expression_contains_call(self, expr: Optional[Expression]) -> bool:
        if expr is None:
            return False
        if expr.expr_type == ExpressionType.CALL:
            return True
        if expr.expr_type == ExpressionType.PHI and expr.value:
            for cond, value in expr.value:
                if cond is not None and self._expression_contains_call(cond.expression):
                    return True
                if self._expression_contains_call(value):
                    return True
            return False
        for operand in getattr(expr, "operands", []) or []:
            if self._expression_contains_call(operand):
                return True
        return False

    def _expression_contains_phi(self, expr: Optional[Expression]) -> bool:
        if expr is None:
            return False
        if expr.expr_type == ExpressionType.PHI:
            return True
        if expr.expr_type == ExpressionType.PHI and expr.value:
            return True
        for operand in getattr(expr, "operands", []) or []:
            if self._expression_contains_phi(operand):
                return True
        return False

    def _expression_contains_budget_unknown(self, expr: Optional[Expression]) -> bool:
        if expr is None:
            return False
        if expr.expr_type == ExpressionType.UNKNOWN:
            runtime_ref = getattr(expr, "runtime_ref", None)
            if getattr(runtime_ref, "kind", None) == "budget_exceeded":
                return True
        if expr.expr_type == ExpressionType.PHI and expr.value:
            for cond, value in expr.value:
                if cond is not None and self._expression_contains_budget_unknown(cond.expression):
                    return True
                if self._expression_contains_budget_unknown(value):
                    return True
            return False
        for operand in getattr(expr, "operands", []) or []:
            if self._expression_contains_budget_unknown(operand):
                return True
        return False

    def _results_contain_budget_unknown(
        self,
        values: List[ExpandedValue],
    ) -> bool:
        return any(self._expression_contains_budget_unknown(ev.value) for ev in values)

    def _maybe_replace_budget_results_with_traced_fallback(
        self,
        pcode_op,
        values: List[ExpandedValue],
        base_conditions: List[Condition],
        depth: int,
        output_size: int = 0,
    ) -> List[ExpandedValue]:
        """
        展開予算で UNKNOWN を混ぜた場合は、P-code 直トレース式へ安全にフォールバックする。

        予算超過時の UNKNOWN は downstream で不可逆に汚染しやすい一方、トレーサが返す
        PHI/ITE 付き式は分岐を内包した exact summary なので、こちらを優先して保持する。
        """
        if not values or not self._results_contain_budget_unknown(values):
            return values

        traced_value = self._trace_operation_expression(
            pcode_op,
            base_conditions,
            depth,
            output_size=output_size,
        )
        if traced_value is None or self._expression_contains_call(traced_value):
            return values

        simplified_conditions = ConditionSimplifier.simplify_conditions(list(base_conditions))
        reduced_value = _reduce_expression_under_conditions(traced_value, simplified_conditions)
        normalized_value = reduced_value if reduced_value is not None else traced_value
        if self._expression_contains_call(normalized_value):
            return values
        if self._expression_contains_budget_unknown(normalized_value):
            return values
        fallback = ExpandedValue(normalized_value, simplified_conditions)
        if self.debug:
            self._debug_print(
                "Replacing budget-exceeded expansion with traced fallback expression",
                depth,
            )
            self._debug_expr("  fallback: ", normalized_value, depth + 1)
        return self._deduplicate_expanded_values(
            [fallback],
            depth,
            label=f"{pcode_op.getMnemonic()} traced budget fallback",
        )

    def _expand_expression_cases(
        self,
        expr: Optional[Expression],
        base_conditions: List[Condition],
        depth: int,
    ) -> List[ExpandedValue]:
        if expr is None:
            return []

        if expr.expr_type == ExpressionType.PHI and expr.value:
            expanded: List[ExpandedValue] = []
            prior_guards: List[Condition] = []
            for cond, value in expr.value:
                combined_conditions = list(base_conditions)
                for prior in prior_guards:
                    combined_conditions.append(prior.negate())
                if cond is not None:
                    combined_conditions.append(cond)
                    prior_guards.append(cond)
                simplified = ConditionSimplifier.simplify_conditions(combined_conditions)
                if ConditionSimplifier.is_contradiction(simplified):
                    continue
                expanded.extend(
                    self._expand_expression_cases(
                        value,
                        simplified,
                        depth + 1,
                    )
                )
            return self._deduplicate_expanded_values(expanded, depth) if expanded else []

        if expr.expr_type == ExpressionType.MEMORY and expr.operands:
            addr_cases = self._expand_expression_cases(expr.operands[0], base_conditions, depth + 1)
            if not addr_cases:
                return [ExpandedValue(expr, ConditionSimplifier.simplify_conditions(base_conditions))]
            expanded = []
            for addr_case in addr_cases:
                simplified = ConditionSimplifier.simplify_conditions(addr_case.conditions)
                if ConditionSimplifier.is_contradiction(simplified):
                    continue
                rebuilt = Expression.memory(
                    addr_case.value,
                    expr.size,
                    read_order_key=expr.read_order_key,
                )
                expanded.append(ExpandedValue(rebuilt, simplified))
            return self._deduplicate_expanded_values(expanded, depth) if expanded else []

        if expr.expr_type == ExpressionType.UNARY_OP and expr.operands:
            operand_cases = self._expand_expression_cases(expr.operands[0], base_conditions, depth + 1)
            if not operand_cases:
                return [ExpandedValue(expr, ConditionSimplifier.simplify_conditions(base_conditions))]
            expanded = []
            for operand_case in operand_cases:
                simplified = ConditionSimplifier.simplify_conditions(operand_case.conditions)
                if ConditionSimplifier.is_contradiction(simplified):
                    continue
                if expr.operator is None:
                    continue
                rebuilt = Expression.unary_op(expr.operator, operand_case.value)
                rebuilt.size = expr.size
                expanded.append(ExpandedValue(rebuilt, simplified))
            return self._deduplicate_expanded_values(expanded, depth) if expanded else []

        if expr.expr_type == ExpressionType.BINARY_OP and len(expr.operands) == 2:
            left_cases = self._expand_expression_cases(expr.operands[0], base_conditions, depth + 1)
            right_cases = self._expand_expression_cases(expr.operands[1], base_conditions, depth + 1)
            if not left_cases:
                left_cases = [ExpandedValue(expr.operands[0], ConditionSimplifier.simplify_conditions(base_conditions))]
            if not right_cases:
                right_cases = [ExpandedValue(expr.operands[1], ConditionSimplifier.simplify_conditions(base_conditions))]
            if expr.operator is None:
                return []
            expanded = self._combine_input_expansions_with_conditions(
                expr.operator,
                [left_cases, right_cases],
                [],
                depth,
                output_size=expr.size,
            )
            return self._deduplicate_expanded_values(expanded, depth) if expanded else []

        return [ExpandedValue(expr, ConditionSimplifier.simplify_conditions(base_conditions))]

    def _trace_operation_expression(
        self,
        pcode_op,
        conditions: List[Condition],
        depth: int,
        output_size: int = 0,
    ) -> Optional[Expression]:
        try:
            traced = self.tracer._trace_pcode_op(pcode_op, depth, use_cache=False)
        except Exception:
            return None

        canonicalized = self._canonicalize_traced_expression(traced, conditions)
        if (
            traced is not None
            and canonicalized is traced
            and traced.expr_type == ExpressionType.MEMORY
            and self.effect_summary is not None
            and getattr(self.effect_summary, "effects", None)
            and self.parameters
        ):
            collapsed = collapse_post_state_expr_to_canonical_memory(
                traced,
                self.effect_summary.effects,
                self.parameters,
                return_conditions=conditions,
            )
            if collapsed is not None:
                reduced = _reduce_expression_under_conditions(collapsed, conditions)
                canonicalized = reduced if reduced is not None else collapsed
        if output_size > 0 and getattr(canonicalized, "size", 0) == 0:
            canonicalized.size = output_size
        return canonicalized
    
    def _expand_input_operation(
        self,
        pcode_op,
        conditions: List[Condition],
        depth: int
    ) -> List[ExpandedValue]:
        """MULTIEQUAL入力内の演算を展開"""
        mnemonic = pcode_op.getMnemonic()
        num_inputs = pcode_op.getNumInputs()
        
        # 出力サイズを取得
        output = pcode_op.getOutput()
        output_size = output.getSize() if output else 0
        
        self._debug_print(f"Expanding operation {mnemonic} (depth={depth}, output_size={output_size})", depth)
        
        if mnemonic in ("CALL", "CALLIND"):
            return self._expand_call_operation(
                pcode_op,
                conditions,
                depth,
                output_size=output_size,
            )

        # MULTIEQUAL / CALL が含まれるかチェック
        requires_recursive_expansion = self._op_requires_recursive_expansion(pcode_op)

        if not requires_recursive_expansion:
            traced_value = self._trace_operation_expression(
                pcode_op,
                conditions,
                depth,
                output_size=output_size,
            )
            if traced_value is not None and not self._expression_contains_unknown_or_call(traced_value) and not self._expression_contains_phi(traced_value):
                self._debug_print(
                    f"  Direct operation trace resolved: {self._debug_expr_summary(traced_value)}",
                    depth,
                )
                return [ExpandedValue(traced_value, conditions)]
            if traced_value is not None and self._expression_contains_phi(traced_value):
                self._debug_print(
                    "  Direct operation trace still contains PHI, expanding traced expression cases",
                    depth,
                )
                expanded_traced = self._expand_expression_cases(
                    traced_value,
                    conditions,
                    depth + 1,
                )
                if expanded_traced:
                    return expanded_traced
                requires_recursive_expansion = True
            elif traced_value is not None:
                return [ExpandedValue(traced_value, conditions)]
            else:
                # 特別な展開が不要なら単純にトレース
                self._debug_print(f"  No recursive expansion target in inputs, simple trace", depth)
                value = self.tracer._trace_pcode_op(pcode_op, depth, use_cache=False)
                value = self._canonicalize_traced_expression(value, conditions)
                # 出力サイズを設定
                if value.size == 0 and output_size > 0:
                    value.size = output_size
                return [ExpandedValue(value, conditions)]

        self._debug_print(f"  Recursive expansion target found in inputs, expanding recursively", depth)
        
        # MULTIEQUALがあれば各入力を再帰的に展開
        input_expansions: List[List[ExpandedValue]] = []
        
        for i in range(num_inputs):
            input_varnode = pcode_op.getInput(i)
            # 各入力を再帰的に展開（条件は空で開始、後で組み合わせる）
            expanded = self._expand_input_varnode(input_varnode, [], depth + 1)
            input_expansions.append(expanded)
            self._debug_print(f"  Input[{i}] expanded to {len(expanded)} values", depth)
        
        # 組み合わせを生成
        output = pcode_op.getOutput()
        output_size = output.getSize() if output else 0
        combined = self._combine_input_expansions_with_conditions(
            mnemonic,
            input_expansions,
            conditions,
            depth,
            output_size=output_size,
            output_varnode=output,
            read_order_key=self.tracer._get_op_order_key(pcode_op) if mnemonic == "LOAD" else None,
        )
        return self._maybe_replace_budget_results_with_traced_fallback(
            pcode_op,
            combined,
            conditions,
            depth,
            output_size=output_size,
        )
    
    def _op_requires_recursive_expansion(self, pcode_op, depth: int = 0) -> bool:
        """PcodeOpの入力ツリーに再帰展開対象が含まれるかチェック"""
        if depth > 15:
            return False
        
        if pcode_op is None:
            return False
        
        mnemonic = pcode_op.getMnemonic()
        if mnemonic in {"MULTIEQUAL", "CALL", "CALLIND", "INDIRECT"}:
            return True
        
        for i in range(pcode_op.getNumInputs()):
            input_varnode = pcode_op.getInput(i)
            if input_varnode:
                input_def = input_varnode.getDef()
                if input_def and self._op_requires_recursive_expansion(input_def, depth + 1):
                    return True

        return False

    def _expand_call_operation(
        self,
        pcode_op,
        base_conditions: List[Condition],
        depth: int,
        output_size: int = 0,
    ) -> List[ExpandedValue]:
        """CALL/CALLIND を callee の return case に展開する。"""
        resolved_targets = resolve_call_targets(
            self.tracer,
            pcode_op,
            conditions=base_conditions,
            parameters=self.parameters,
            read_memory_value=self.read_memory_value,
            image_base=self.image_base,
            debug=self.debug,
        )
        if self.debug and resolved_targets:
            for target_ref, target_conditions in resolved_targets:
                cond_strs = [cond.to_string() for cond in target_conditions]
                self._debug_print(
                    f"Resolved {pcode_op.getMnemonic()} target -> {target_ref.display_name()} with conditions {cond_strs}",
                    depth,
                )

        if not resolved_targets or self.call_resolver is None:
            target_ref = _resolve_call_target_ref(self.tracer, pcode_op)
            target_label = target_ref.display_name() if target_ref is not None else "UNKNOWN_FUNC"
            explicit_args = [
                _resolve_call_argument_expression(
                    pcode_op.getInput(index),
                    self.tracer,
                    self.parameters,
                )
                for index in range(1, pcode_op.getNumInputs())
            ]
            deferred_unknown_ref = None
            deferred_unknown_label = None
            if self.record_deferred_call is not None and target_ref is not None:
                deferred_args = self._recover_deferred_call_arguments(
                    pcode_op,
                    target_ref,
                    explicit_args,
                )
                try:
                    deferred_unknown = self.record_deferred_call(target_ref, deferred_args)
                    if isinstance(deferred_unknown, str):
                        deferred_unknown_label = deferred_unknown
                    else:
                        deferred_unknown_ref = deferred_unknown
                        if hasattr(deferred_unknown, "display_name"):
                            deferred_unknown_label = deferred_unknown.display_name()
                except Exception:
                    deferred_unknown_ref = None
                    deferred_unknown_label = None
            self.tracer.emit_unknown_event(
                reason="call_out_of_scope",
                varnode=pcode_op.getOutput(),
                def_op=pcode_op,
                depth=depth,
                note=f"{pcode_op.getMnemonic()} target={target_label}",
                context="expander",
            )
            return [
                ExpandedValue(
                    Expression.unknown(
                        (
                            deferred_unknown_label
                            if deferred_unknown_label is not None
                            else f"call_out_of_scope:{target_label}"
                        ),
                        runtime_ref=deferred_unknown_ref,
                    ),
                    base_conditions,
                )
            ]

        arg_expansions: List[List[ExpandedValue]] = []
        explicit_input_varnodes = [
            pcode_op.getInput(index)
            for index in range(1, pcode_op.getNumInputs())
        ]
        canonical_explicit_args: List[Optional[Expression]] = []
        if self.parameters:
            for input_varnode in explicit_input_varnodes:
                try:
                    canonical_explicit_args.append(
                        _resolve_call_argument_expression(
                            input_varnode,
                            self.tracer,
                            self.parameters,
                        )
                    )
                except Exception:
                    canonical_explicit_args.append(None)

        for index in range(1, pcode_op.getNumInputs()):
            arg_expansions.append(
                self._expand_input_varnode(pcode_op.getInput(index), [], depth + 1)
            )

        result: List[ExpandedValue] = []
        fallback_args_by_target: Dict[CallTargetRef, List[Expression]] = {}

        def resolve_with_args(
            arg_index: int,
            current_args: List[Expression],
            current_conditions: List[Condition],
        ) -> None:
            if arg_index >= len(arg_expansions):
                for target_ref, target_conditions in resolved_targets:
                    merged_target_conditions = ConditionSimplifier.simplify_conditions(
                        current_conditions + target_conditions
                    )
                    if ConditionSimplifier.is_contradiction(merged_target_conditions):
                        continue

                    effective_args = list(current_args)
                    if self.parameters and canonical_explicit_args:
                        stabilized_args: List[Expression] = []
                        for index, arg in enumerate(effective_args):
                            input_varnode = (
                                explicit_input_varnodes[index]
                                if index < len(explicit_input_varnodes)
                                else None
                            )
                            canonical_arg = (
                                canonical_explicit_args[index]
                                if index < len(canonical_explicit_args)
                                else None
                            )
                            should_replace = (
                                input_varnode is not None
                                and getattr(input_varnode, "getDef", lambda: None)() is not None
                                and canonical_arg is not None
                                and canonical_arg.expr_type not in {ExpressionType.UNKNOWN, ExpressionType.CALL}
                                and not self._expression_contains_unknown_or_call(canonical_arg)
                                and (
                                    canonical_arg.expr_type != ExpressionType.VARIABLE
                                    or _expression_maps_to_parameter(canonical_arg, self.parameters)
                                )
                                and _expression_maps_to_parameter(arg, self.parameters)
                                and not _expressions_equivalent(arg, canonical_arg)
                            )
                            if should_replace:
                                assert canonical_arg is not None
                                if self.debug:
                                    self._debug_print(
                                        "Stabilized explicit CALL arg from original input: "
                                        f"{self._debug_expr_summary(arg)} -> {self._debug_expr_summary(canonical_arg)}",
                                        depth,
                                    )
                                stabilized_args.append(canonical_arg)
                            else:
                                stabilized_args.append(arg)
                        effective_args = stabilized_args
                    if self.resolve_callee_parameters is not None:
                        callee_parameters = list(self.resolve_callee_parameters(target_ref) or [])
                        if callee_parameters:
                            effective_args = _recover_call_argument_expressions(
                                pcode_op,
                                self.tracer,
                                self.parameters,
                                callee_parameters,
                                effective_args,
                            )
                    fallback_args_by_target.setdefault(
                        target_ref,
                        list(effective_args),
                    )

                    if self.call_resolver is None:
                        continue
                    resolved = self.call_resolver(target_ref, effective_args)
                    if not resolved:
                        if self.debug:
                            self._debug_print(
                                f"Call summary unavailable for resolved target '{target_ref.display_name()}'",
                                depth,
                            )
                        continue
                    for ev in resolved:
                        merged_conditions = ConditionSimplifier.simplify_conditions(
                            merged_target_conditions + ev.conditions
                        )
                        if ConditionSimplifier.is_contradiction(merged_conditions):
                            continue
                        value = self._coerce_value_to_output_size(ev.value, output_size)
                        result.append(ExpandedValue(value, merged_conditions))
                return

            for ev in arg_expansions[arg_index]:
                merged_conditions = current_conditions + ev.conditions
                if ConditionSimplifier.is_contradiction(merged_conditions):
                    continue
                resolve_with_args(
                    arg_index + 1,
                    current_args + [ev.value],
                    merged_conditions,
                )

        resolve_with_args(0, [], list(base_conditions))

        if result:
            return self._deduplicate_expanded_values(result, depth)

        fallback_target = self._select_deferred_call_target(resolved_targets, pcode_op)
        fallback_label = fallback_target.display_name()
        deferred_unknown_ref = None
        deferred_unknown_label = None
        if self.record_deferred_call is not None:
            deferred_args = fallback_args_by_target.get(fallback_target)
            if deferred_args is None:
                recovered_seed_args = [arg for arg in (canonical_explicit_args or []) if arg is not None]
                deferred_args = self._recover_deferred_call_arguments(
                    pcode_op,
                    fallback_target,
                    recovered_seed_args,
                )
            try:
                deferred_unknown = self.record_deferred_call(fallback_target, deferred_args)
                if isinstance(deferred_unknown, str):
                    deferred_unknown_label = deferred_unknown
                else:
                    deferred_unknown_ref = deferred_unknown
                    if hasattr(deferred_unknown, "display_name"):
                        deferred_unknown_label = deferred_unknown.display_name()
            except Exception:
                deferred_unknown_ref = None
                deferred_unknown_label = None
        self.tracer.emit_unknown_event(
            reason="call_out_of_scope",
            varnode=pcode_op.getOutput(),
            def_op=pcode_op,
            depth=depth,
            note=f"{pcode_op.getMnemonic()} target={fallback_label}",
            context="expander",
        )
        return [
            ExpandedValue(
                Expression.unknown(
                    (
                        deferred_unknown_label
                        if deferred_unknown_label is not None
                        else f"call_out_of_scope:{fallback_label}"
                    ),
                    runtime_ref=deferred_unknown_ref,
                ),
                base_conditions,
            )
        ]

    def _select_deferred_call_target(
        self,
        resolved_targets: List[Tuple[CallTargetRef, List[Condition]]],
        pcode_op,
    ) -> CallTargetRef:
        unique_targets = [
            target_ref
            for target_ref, _target_conditions in (resolved_targets or [])
            if target_ref is not None
        ]
        unique_keys = {target_ref.stable_key(): target_ref for target_ref in unique_targets}
        if len(unique_keys) == 1:
            return next(iter(unique_keys.values()))
        return _resolve_call_target_ref(self.tracer, pcode_op) or CallTargetRef.unknown()

    def _recover_deferred_call_arguments(
        self,
        pcode_op,
        target_ref: CallTargetRef,
        explicit_args: List[Expression],
    ) -> List[Expression]:
        deferred_args = list(explicit_args or [])
        if self.resolve_callee_parameters is None or target_ref is None:
            return deferred_args

        callee_parameters = list(self.resolve_callee_parameters(target_ref) or [])
        if not callee_parameters:
            return deferred_args

        recovered = _recover_call_argument_expressions(
            pcode_op,
            self.tracer,
            self.parameters,
            callee_parameters,
            deferred_args,
        )
        if recovered:
            return recovered
        return deferred_args

    def _infer_indirect_output_location(
        self,
        output_varnode,
        output_size: int,
    ):
        if output_varnode is None or output_size <= 0:
            return None

        storage_info = None
        try:
            storage_info = self.tracer._get_storage_info_from_varnode(output_varnode)
        except Exception:
            storage_info = None
        if storage_info is None:
            storage_info = self._fallback_storage_info_from_varnode(output_varnode, output_size)

        high_name = None
        try:
            high_var = output_varnode.getHigh()
            if high_var is not None:
                high_name = high_var.getName()
        except Exception:
            high_name = None

        probe_name = high_name or f"indirect_out_{id(output_varnode):x}"
        probe = Expression.variable(
            probe_name,
            size=output_size,
            storage_info=storage_info,
        )
        location = canonicalize_location(probe, self.parameters, size=output_size)
        if self.debug and location is None:
            self._debug_print(
                "Failed to infer INDIRECT output location: "
                f"name={probe_name} storage={storage_info}",
                0,
            )
        return location

    def _fallback_storage_info_from_varnode(
        self,
        varnode,
        output_size: int,
    ) -> Optional[StorageInfo]:
        if varnode is None:
            return None
        try:
            addr = varnode.getAddress()
            if addr is None:
                return None
            space = addr.getAddressSpace()
            if space is None:
                return None
            space_name = space.getName()
            size = max(1, int(output_size or varnode.getSize() or 0))
            if space_name == "stack":
                return StorageInfo(
                    is_register=False,
                    space_name="stack",
                    offset=int(varnode.getOffset()),
                    size=size,
                    size_bits=size * 8,
                )
            if space_name == "register":
                reg_name = None
                try:
                    reg = self.tracer.program.getRegister(addr, size)
                    reg_name = reg.getName() if reg is not None else None
                except Exception:
                    reg_name = None
                return StorageInfo(
                    is_register=True,
                    space_name="register",
                    offset=int(varnode.getOffset()),
                    size=size,
                    size_bits=size * 8,
                    register_name=reg_name,
                    base_register_name=reg_name,
                    base_register_offset=int(varnode.getOffset()),
                    base_register_size=size,
                    base_register_size_bits=size * 8,
                    bit_offset_in_base=0,
                )
        except Exception:
            return None
        return None

    def _resolve_indirect_post_state_read(
        self,
        output_varnode,
        fallback_expr: Expression,
        conditions: List[Condition],
        depth: int,
        output_size: int = 0,
    ) -> Expression:
        if self.effect_summary is None or not getattr(self.effect_summary, "effects", None):
            return fallback_expr
        if not self.parameters:
            return fallback_expr

        location = self._infer_indirect_output_location(output_varnode, output_size)
        if location is None:
            if self.debug:
                self._debug_print(
                    f"INDIRECT post-state read fell back to pre-state value: {self._debug_expr_summary(fallback_expr)}",
                    depth,
                )
            return fallback_expr

        resolved = rewrite_location_read_from_effects(
            location,
            fallback_expr,
            conditions,
            self.effect_summary.effects,
            self.parameters,
        )
        reduced = _reduce_expression_under_conditions(resolved, conditions)
        resolved = reduced if reduced is not None else resolved
        if self._expression_contains_unknown_or_call(resolved):
            return fallback_expr

        if self.debug and not _expressions_equivalent(resolved, fallback_expr):
            self._debug_print(
                f"Resolved INDIRECT post-state read via effect summary: {self._debug_expr_summary(fallback_expr)} -> {self._debug_expr_summary(resolved)}",
                depth,
            )
        return resolved
    
    def _expand_operation(
        self,
        pcode_op,
        base_conditions: List[Condition],
        depth: int
    ) -> List[ExpandedValue]:
        """通常の演算を展開（トップレベルから呼ばれる場合）"""
        mnemonic = pcode_op.getMnemonic()
        num_inputs = pcode_op.getNumInputs()
        
        self._debug_print(f"Operation {mnemonic} with {num_inputs} inputs", depth)
        
        if mnemonic in ("CALL", "CALLIND"):
            return self._expand_call_operation(
                pcode_op,
                base_conditions,
                depth,
            )

        # MULTIEQUAL / CALL が含まれるかチェック
        requires_recursive_expansion = self._op_requires_recursive_expansion(pcode_op)

        if not requires_recursive_expansion:
            traced_value = self._trace_operation_expression(
                pcode_op,
                base_conditions,
                depth,
            )
            if traced_value is not None and not self._expression_contains_unknown_or_call(traced_value) and not self._expression_contains_phi(traced_value):
                self._debug_print(
                    f"  Direct operation trace resolved: {self._debug_expr_summary(traced_value)}",
                    depth,
                )
                return [ExpandedValue(traced_value, base_conditions)]
            if traced_value is not None and self._expression_contains_phi(traced_value):
                self._debug_print(
                    "  Top-level direct trace still contains PHI, expanding traced expression cases",
                    depth,
                )
                expanded_traced = self._expand_expression_cases(
                    traced_value,
                    base_conditions,
                    depth + 1,
                )
                if expanded_traced:
                    return expanded_traced
                requires_recursive_expansion = True
            elif traced_value is not None:
                return [ExpandedValue(traced_value, base_conditions)]
            else:
                value = self.tracer._trace_pcode_op(pcode_op, depth, use_cache=False)
                return [ExpandedValue(value, base_conditions)]
        
        # 各入力を展開
        input_expansions: List[List[ExpandedValue]] = []
        
        for i in range(num_inputs):
            input_varnode = pcode_op.getInput(i)
            expanded = self.expand_from_varnode(input_varnode, [], depth + 1)
            input_expansions.append(expanded)
            
            if len(expanded) > 1:
                self._debug_print(f"  Input[{i}] has {len(expanded)} expansions", depth)
        
        output = pcode_op.getOutput()
        output_size = output.getSize() if output else 0
        combined = self._combine_input_expansions_with_conditions(
            mnemonic,
            input_expansions,
            base_conditions,
            depth,
            output_size=output_size,
            output_varnode=output,
            read_order_key=self.tracer._get_op_order_key(pcode_op) if mnemonic == "LOAD" else None,
        )
        return self._maybe_replace_budget_results_with_traced_fallback(
            pcode_op,
            combined,
            base_conditions,
            depth,
            output_size=output_size,
        )
    
    def _combine_input_expansions_with_conditions(
        self,
        mnemonic: str,
        input_expansions: List[List[ExpandedValue]],
        base_conditions: List[Condition],
        depth: int,
        output_size: int = 0,
        output_varnode=None,
        read_order_key: Optional[int] = None,
    ) -> List[ExpandedValue]:
        """入力の展開を組み合わせて結果を生成"""
        self._debug_print(f"Combining expansions for {mnemonic}", depth)

        normalized_inputs: List[List[ExpandedValue]] = []
        for index, expansions in enumerate(input_expansions):
            if len(expansions) > 1:
                normalized = self._deduplicate_expanded_values(
                    expansions,
                    depth + 1,
                    limit=self._max_operation_cases,
                    label=f"{mnemonic} input[{index}]",
                )
            else:
                normalized = expansions
            normalized_inputs.append(normalized)
        input_expansions = normalized_inputs
        
        if len(input_expansions) == 0:
            return [ExpandedValue(Expression.unknown(f"{mnemonic}_no_input"), base_conditions)]
        
        if len(input_expansions) == 1:
            result = []
            seen_keys: Set[Tuple[str, str]] = set()
            for ev in input_expansions[0]:
                combined_conds = base_conditions + ev.conditions
                pre_key = (
                    self._expansion_expression_signature(ev.value),
                    ConditionNormalizer.conditions_signature(combined_conds),
                )
                if pre_key in seen_keys:
                    continue
                seen_keys.add(pre_key)
                if not ConditionSimplifier.is_contradiction(combined_conds):
                    if mnemonic in ("INT_NEGATE", "INT_2COMP", "BOOL_NEGATE", "INT_ZEXT", "INT_SEXT"):
                        new_value = Expression.unary_op(mnemonic, ev.value)
                    else:
                        new_value = ev.value
                    result.append(ExpandedValue(new_value, combined_conds))
            return self._finalize_combined_results(
                mnemonic,
                result,
                base_conditions,
                depth,
            )
        
        if len(input_expansions) == 2:
            result_map: Dict[Tuple[str, str], ExpandedValue] = {}
            seen_pairs: Set[Tuple[str, str, str, str, int, Optional[int]]] = set()
            raw_attempts = 0
            novel_results = 0
            raw_attempt_limit = max(self._max_combination_attempts * 8, self._max_combination_attempts)
            for left_ev in input_expansions[0]:
                for right_ev in input_expansions[1]:
                    raw_attempts += 1
                    if raw_attempts > raw_attempt_limit:
                        self._debug_print(
                            f"  Combination raw-attempt budget exceeded at {raw_attempts} attempts; "
                            f"returning conservative summary",
                            depth,
                        )
                        return self._finalize_combined_results(
                            mnemonic,
                            list(result_map.values()),
                            base_conditions,
                            depth,
                            over_budget=True,
                        )

                    combined_conds = base_conditions + left_ev.conditions + right_ev.conditions
                    pre_key = (
                        self._expansion_expression_signature(left_ev.value),
                        self._expansion_expression_signature(right_ev.value),
                        ConditionNormalizer.conditions_signature(combined_conds),
                        mnemonic,
                        output_size,
                        read_order_key,
                    )
                    if pre_key in seen_pairs:
                        continue
                    seen_pairs.add(pre_key)
                    
                    if ConditionSimplifier.is_contradiction(combined_conds):
                        self._debug_print(f"  Combination contradictory, skip", depth)
                        continue
                    
                    if mnemonic == "LOAD":
                        new_value = Expression.memory(
                            right_ev.value,
                            output_size if output_size > 0 else 4,
                            read_order_key=read_order_key,
                        )
                    elif mnemonic == "INDIRECT":
                        new_value = self._resolve_indirect_post_state_read(
                            output_varnode,
                            left_ev.value,
                            combined_conds,
                            depth,
                            output_size=output_size if output_size > 0 else left_ev.value.size,
                        )
                    else:
                        new_value = Expression.binary_op(mnemonic, left_ev.value, right_ev.value)
                        if output_size > 0 and new_value.size == 0:
                            new_value.size = output_size
                    simplified_conds = ConditionSimplifier.simplify_conditions(combined_conds)
                    reduced_value = _reduce_expression_under_conditions(new_value, simplified_conds)
                    normalized_value = reduced_value if reduced_value is not None else new_value
                    normalized_ev = ExpandedValue(normalized_value, simplified_conds)
                    result_key = (
                        self._expansion_expression_signature(normalized_ev.value),
                        normalized_ev.get_condition_signature(),
                    )
                    existing = result_map.get(result_key)
                    if existing is not None:
                        if self._prefer_expanded_value(normalized_ev, existing):
                            result_map[result_key] = normalized_ev
                        continue
                    result_map[result_key] = normalized_ev
                    novel_results += 1
                    self._debug_expr("  Combined: ", normalized_ev.value, depth)
                    if novel_results > self._max_combination_attempts:
                        self._debug_print(
                            f"  Combination novelty budget exceeded at {novel_results} unique results; "
                            f"returning conservative summary",
                            depth,
                        )
                        return self._finalize_combined_results(
                            mnemonic,
                            list(result_map.values()),
                            base_conditions,
                            depth,
                            over_budget=True,
                        )

            return self._finalize_combined_results(
                mnemonic,
                list(result_map.values()),
                base_conditions,
                depth,
            )
        
        # 3つ以上の入力
        self._debug_print(f"  Too many inputs ({len(input_expansions)}), falling back", depth)
        first_expansions = input_expansions[0]
        result = []
        for ev in first_expansions:
            other_values = []
            for exp_list in input_expansions[1:]:
                if exp_list:
                    other_values.append(exp_list[0].value)
            
            all_values = [ev.value] + other_values
            new_value = Expression.call(mnemonic, all_values)
            combined_conds = base_conditions + ev.conditions
            result.append(ExpandedValue(new_value, combined_conds))
        
        return result if result else [ExpandedValue(Expression.unknown(f"{mnemonic}_fail"), base_conditions)]
    
    def _get_edge_condition(self, from_block_info, to_block) -> Optional[Condition]:
        """fromブロックからtoブロックへのエッジ条件を取得"""
        from_block = from_block_info.block
        
        if from_block.getOutSize() <= 1:
            return None
        
        if not from_block_info.has_conditional_branch():
            return None
        
        to_index = to_block.getIndex()
        
        true_out = from_block.getTrueOut()
        false_out = from_block.getFalseOut()
        
        true_index = true_out.getIndex() if true_out else -1
        false_index = false_out.getIndex() if false_out else -1
        
        condition = None
        if to_index == true_index:
            condition = Condition(from_block_info.branch_condition, negated=False)
        elif to_index == false_index:
            condition = Condition(from_block_info.branch_condition, negated=True)
        
        if self.debug and condition:
            cond_str = ConditionNormalizer.get_simplified_string(condition)
            self._debug_print(
                f"Edge: block {from_block_info.index} -> {to_index}: {cond_str}", 2
            )
        return condition

"""MULTIEQUAL (PHI) expansion: branch observations, path conditions and canonical location inference."""

from __future__ import annotations

from dataclasses import replace as dataclasses_replace
from typing import Any, Callable, Iterable, List, Optional, Dict, Tuple
from scripts.function_tracer_pcode.core import (
    Expression,
    Condition,
    ExpressionType,
    ExpansionBudgetTruncation,
    UnknownValueRef,
    CanonicalLocation,
)
from scripts.function_tracer_pcode.analysis.condition import (
    ConditionSimplifier,
    ConditionNormalizer,
)
from scripts.function_tracer_pcode.analysis.effects.summary import (
    _reduce_expression_under_conditions,
    _expressions_equivalent,
    canonicalize_param_location,
    collapse_post_state_expr_to_canonical_memory,
    memory_expression_for_location,
    rewrite_loads_from_effects,
)
from scripts.function_tracer_pcode.semantics.transform.expander_support import (
    _pcode_op_stable_key,
    _pcode_op_ref_from_tracer,
    ExpandedValue,
    MultiequalBranchObservation,
)


def replace_pcode_op_ref(
    truncation: ExpansionBudgetTruncation,
    pcode_op_ref,
) -> ExpansionBudgetTruncation:
    """tracker が返した原因へ、利用箇所の op 参照を付ける。

    tracker は経路列挙の原因だけを返し、どの MULTIEQUAL の展開で使われたかは知らない。
    利用側がここで結び付ける。
    """

    if pcode_op_ref is None or truncation.pcode_op_ref is not None:
        return truncation
    return dataclasses_replace(truncation, pcode_op_ref=pcode_op_ref)


class MultiequalExpansionMixin:
    """MULTIEQUAL (PHI) expansion: branch observations, path conditions and canonical location inference."""

    def _expand_multiequal(
        self,
        multiequal_op,
        base_conditions: List[Condition],
        depth: int
    ) -> List[ExpandedValue]:
        """MULTIEQUALを展開"""
        op_key = _pcode_op_stable_key(multiequal_op)
        
        if op_key in self._expanding_ops:
            self._debug_print(f"Circular MULTIEQUAL detected: {op_key}", depth)
            return [
                ExpandedValue(
                    Expression.unknown(
                        "phi_circular",
                        runtime_ref=UnknownValueRef.phi_circular(
                            pcode_op_ref=_pcode_op_ref_from_tracer(self.tracer, multiequal_op),
                        ),
                    ),
                    list(base_conditions),
                )
            ]
        
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
        
        各入力エッジの有効パスを条件付きの別ケースとして展開する。
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
        multiequal_pcode_op_ref = _pcode_op_ref_from_tracer(self.tracer, multiequal_op)
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
                self._debug_print("  in_block is None", depth + 1)
                continue
            
            in_block_info = self.condition_tracker.get_block_by_hash(in_block)
            if not in_block_info:
                self._debug_print("  in_block_info not found", depth + 1)
                continue
            
            self._debug_print(f"  pred_block: index={in_block_info.index}", depth + 1)
            
            self._debug_multiequal_input_trace(input_varnode, depth + 1)

            all_valid_paths, path_truncations = self._valid_paths_to_block_with_truncations(
                in_block_info
            )
            for truncation in path_truncations:
                self._record_expansion_budget_truncation(
                    replace_pcode_op_ref(truncation, multiequal_pcode_op_ref)
                )

            self._debug_print(f"  valid_paths: {len(all_valid_paths)}", depth + 1)

            edge_cond = self._get_edge_condition(in_block_info, phi_parent)
            if edge_cond:
                edge_str = ConditionNormalizer.get_simplified_string(edge_cond)
                self._debug_print(f"  edge_condition: {edge_str}", depth + 1)

            cases_emitted = 0
            for path_idx, path_conditions in enumerate(all_valid_paths):
                input_conditions = self._build_multiequal_path_conditions(
                    base_conditions,
                    path_conditions,
                    edge_cond,
                )
                if self.debug:
                    self._debug_print(f"  Path[{path_idx}]: {len(path_conditions)} condition(s)", depth + 1)
                    for pc in path_conditions:
                        pc_str = ConditionNormalizer.get_simplified_string(pc)
                        self._debug_print(f"    - {pc_str}", depth + 2)
                if ConditionSimplifier.object_centric_is_contradiction(input_conditions):
                    self._debug_print(f"  Path[{path_idx}] -> SKIP (contradictory)", depth + 1)
                    continue

                if canonical_multiequal_location is not None:
                    canonical_value = self._resolve_canonical_location_under_branch_expression(
                        input_varnode,
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
            merged = self._deduplicate_expanded_values(
                all_expanded,
                depth,
                pcode_op_ref=multiequal_pcode_op_ref,
            )
            self._debug_print("=" * 50, depth)
            self._debug_print(f"MULTIEQUAL -> {len(merged)} branches (after dedup)", depth)
            self._debug_print("=" * 50, depth)
            return merged
        
        self._debug_print("=" * 50, depth)
        self._debug_print("MULTIEQUAL -> 0 branches (no valid branches)", depth)
        self._debug_print("=" * 50, depth)
        return [ExpandedValue(Expression.unknown("phi_no_valid_branch"), list(base_conditions))]

    def _debug_multiequal_input_trace(
        self,
        input_varnode,
        depth: int,
    ) -> None:
        try:
            traced_value = self.tracer.trace_varnode(input_varnode, depth, use_cache=False)
            traced_value = self._canonicalize_traced_expression(traced_value, [])
            self._debug_expr("  traced_value: ", traced_value, depth)
            try:
                smt_str = traced_value.to_smt()
                if len(smt_str) > 100:
                    smt_str = smt_str[:100] + "..."
                self._debug_print(f"  traced_smt: {smt_str}", depth)
            except Exception as exc:
                self._debug_print(f"  traced_smt: (error: {exc})", depth)
        except Exception as exc:
            self._debug_print(f"  traced_value: (error: {exc})", depth)

    def _build_multiequal_path_conditions(
        self,
        base_conditions: List[Condition],
        path_conditions: Iterable[Condition],
        edge_cond: Optional[Condition],
    ) -> List[Condition]:
        combined_conditions = list(base_conditions) + list(path_conditions)
        if edge_cond is not None:
            combined_conditions.append(edge_cond)
        return self._normalize_expansion_conditions(combined_conditions)

    def _record_expansion_budget_truncation(
        self,
        truncation: Optional[ExpansionBudgetTruncation],
    ) -> None:
        """実際に上限で削った事実を局所記録に残し、sink へ即時転送する。

        利用面と所有 scope は sink 側が束縛する（展開器は原因だけを持つ）。
        """

        if truncation is None:
            return
        self._budget_truncations.append(truncation)
        sink = getattr(self, "_budget_sink", None)
        if callable(sink):
            sink(truncation)

    def _resolve_dedup_case_limit(self) -> int:
        """既定 dedup 上限。設定/クラス属性の 1 箇所だけを参照する。"""

        try:
            limit = int(self.MAX_CASES_PER_MULTIEQUAL)
        except (TypeError, ValueError):
            return 16
        return limit if limit >= 1 else 16

    def _valid_paths_to_block_with_truncations(
        self,
        target_block,
    ) -> Tuple[List[List[Condition]], Tuple[ExpansionBudgetTruncation, ...]]:
        """PHI 前任ブロックへの有効経路と、経路列挙で実際に起きた打ち切り原因。

        情報付き API を持たない tracker（テスト用 fake など）では従来どおり経路だけを
        返し、原因は空にする。entry 情報不足のような単なる inconclusive は原因を作らない。
        """

        # 型で判定する。``Mock`` のように任意の属性を生やす tracker では、属性の有無で
        # 情報付き API の有無を判断できないため。
        getter = getattr(
            type(self.condition_tracker),
            "get_all_valid_paths_to_block_with_truncations",
            None,
        )
        if callable(getter):
            paths, truncations = self.condition_tracker.get_all_valid_paths_to_block_with_truncations(
                target_block=target_block
            )
            return list(paths), tuple(truncations or ())
        return (
            list(self.condition_tracker.get_all_valid_paths_to_block(target_block=target_block)),
            (),
        )

    def _deduplicate_expanded_values(
        self,
        values: List[ExpandedValue],
        depth: int,
        limit: Optional[int] = None,
        label: str = "expanded values",
        pcode_op_ref: Optional[Any] = None,
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
        applied_limit = self._resolve_dedup_case_limit() if limit is None else limit
        if len(result) > applied_limit:
            self._debug_print(
                f"  WARNING: Too many cases ({len(result)}), limiting to {applied_limit}",
                depth
            )
            # Issue #131: ここが「件数上限で実際に削った」唯一の分岐。通常の重複排除・
            # 矛盾除去（上の grouping）とは区別して記録する。
            self._record_expansion_budget_truncation(
                ExpansionBudgetTruncation(
                    kind="dedup_case_limit",
                    label=label,
                    pcode_op_ref=pcode_op_ref,
                    dedup=(len(result), applied_limit, applied_limit),
                )
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
        if collapsed is not None and self._debug_available():
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

        reduced = _reduce_expression_under_conditions(candidate, current_conditions)
        resolved = reduced if reduced is not None else candidate
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

    def _observed_location_for_expression(
        self,
        expr: Optional[Expression],
    ) -> Optional[CanonicalLocation]:
        if expr is None or not self.parameters:
            return None
        runtime_ref = getattr(expr, "runtime_ref", None)
        if isinstance(runtime_ref, CanonicalLocation):
            return runtime_ref
        location = getattr(runtime_ref, "location", None)
        if isinstance(location, CanonicalLocation):
            return location
        if expr.expr_type != ExpressionType.MEMORY or not expr.operands:
            return None
        return canonicalize_param_location(
            expr.operands[0],
            self.parameters,
            size=expr.size,
        )

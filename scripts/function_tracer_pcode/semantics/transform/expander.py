# -*- coding: utf-8 -*-
"""式木全体のPHI展開モジュール（網羅性改善版）"""

from dataclasses import dataclass
import inspect
from typing import Callable, Hashable, Iterable, List, Optional, Set, Dict, Tuple, Any
from scripts.function_tracer_pcode.core import (
    Expression,
    Condition,
    ExpressionType,
    StorageInfo,
    CallTargetRef,
    UnknownValueRef,
    CanonicalLocation,
    ExpansionBudgetTruncation,
    PcodeOpRef,
)
from scripts.function_tracer_pcode.core.intrinsics import resolve_pcode_intrinsic
from scripts.function_tracer_pcode.analysis.condition import (
    ConditionSimplifier,
    ConditionNormalizer,
)
from scripts.function_tracer_pcode.analysis.debug import summarize_expression, summarize_condition
from scripts.function_tracer_pcode.config.settings import (
    EXPANDER_DEDUP_CASE_LIMIT,
    EXPANDER_MAX_COMBINATION_ATTEMPTS,
    EXPANDER_MAX_OPERATION_CASES,
)
from scripts.function_tracer_pcode.analysis.effects.summary import (
    _reduce_expression_under_conditions,
    _resolve_call_target_ref,
    _recover_call_argument_expressions,
    _resolve_call_argument_expression,
    _expression_maps_to_parameter,
    _expression_contains_observed_loads,
    canonicalize_expr_read_location,
    resolve_call_targets,
    _expressions_equivalent,
    canonicalize_location,
    canonicalize_param_location,
    canonicalize_post_state_subexpressions,
    collapse_post_state_expr_to_canonical_read,
    collapse_post_state_expr_to_canonical_memory,
    expression_contains_complex_location_reads,
    expression_contains_post_state_reads,
    locations_match,
    memory_expression_for_location,
    normalize_post_state_expression,
    rewrite_loads_from_effects,
    rewrite_location_read_from_effects,
    rewrite_observed_loads_from_effects,
    should_attempt_root_post_state_collapse,
)
from scripts.function_tracer_pcode.analysis.memory_resolver import concretize_readonly_loads
from scripts.function_tracer_pcode.semantics.transform.expander_multiequal import MultiequalExpansionMixin
from scripts.function_tracer_pcode.semantics.transform.expander_calls import CallExpansionMixin
from scripts.function_tracer_pcode.semantics.transform.expander_canonical import CanonicalizationMixin
from scripts.function_tracer_pcode.semantics.transform.expander_support import (
    _pcode_op_stable_key,
    _pcode_op_ref_from_tracer,
    ExpandedValue,
    MultiequalBranchObservation,
)


def _callable_accepts_positional_args(fn: Callable, count: int) -> bool:
    try:
        signature = inspect.signature(fn)
    except (TypeError, ValueError):
        return True
    positional_count = 0
    for param in signature.parameters.values():
        if param.kind == inspect.Parameter.VAR_POSITIONAL:
            return True
        if param.kind in {
            inspect.Parameter.POSITIONAL_ONLY,
            inspect.Parameter.POSITIONAL_OR_KEYWORD,
        }:
            positional_count += 1
    return positional_count >= count


class ExpressionExpander(MultiequalExpansionMixin, CallExpansionMixin, CanonicalizationMixin):
    """
    式木全体を展開し、PHIノードを解決する
    """
    
    # 展開の上限設定
    # 共通 dedup のケース数上限。設定 ``FT_EXPANDER_DEDUP_CASE_LIMIT`` の値をそのまま
    # 参照する互換名で、上限の設定源はここ 1 つ（二重設定にしない）。
    MAX_CASES_PER_MULTIEQUAL = EXPANDER_DEDUP_CASE_LIMIT
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
        record_deferred_call: Optional[
            Callable[[CallTargetRef, List[Expression], Optional[Expression], object], Any]
        ] = None,
        budget_sink: Optional[Callable[[ExpansionBudgetTruncation], None]] = None,
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
        self._record_deferred_call_accepts_pcode_ref = (
            record_deferred_call is not None
            and _callable_accepts_positional_args(record_deferred_call, 4)
        )
        self._expanding_ops: Set[Tuple[Any, ...]] = set()
        self._debug_message_limit = 4000
        self._debug_message_count = 0
        self._debug_suppressed = False
        self._max_operation_cases = int(EXPANDER_MAX_OPERATION_CASES)
        self._max_combination_attempts = int(EXPANDER_MAX_COMBINATION_ATTEMPTS)
        # Issue #131: 実際に上限で削った事実だけを sink へ即時転送する。局所 list は
        # 「この展開中に切り捨てが起きたか」を上位 collector の長さに依存せず判定する
        # ためのもの。
        self._budget_sink = budget_sink
        self._budget_truncations: List[ExpansionBudgetTruncation] = []
    
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
        """PHI 展開で使う raw object-centric condition basis。"""
        if not conditions:
            return []
        rewritten: List[Condition] = []
        source_conditions = list(conditions)
        for index, condition in enumerate(source_conditions):
            reduced_expr = _reduce_expression_under_conditions(
                condition.expression,
                source_conditions[:index] + source_conditions[index + 1 :],
            )
            rewritten.append(
                Condition(reduced_expr, condition.negated)
                if reduced_expr is not None
                else condition
            )
        return ConditionSimplifier.simplify_conditions_object_centric(rewritten)

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
        normalized_conditions = ConditionSimplifier.simplify_conditions_object_centric(
            list(ev.conditions)
        )
        return ExpandedValue(ev.value, normalized_conditions)

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
        pcode_op_ref=None,
    ) -> List[ExpandedValue]:
        limit = self._max_operation_cases
        deduped = self._deduplicate_expanded_values(
            values,
            depth,
            limit=limit,
            label=f"{mnemonic} combinations",
            # Issue #131: 同一関数内で同じ mnemonic・同じ件数の切り捨てが複数箇所で
            # 起きても別 event として識別できるよう、op が分かる経路では必ず渡す。
            pcode_op_ref=pcode_op_ref,
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
            self._debug_print("Max depth reached", depth)
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
            self._debug_print("Max depth in input varnode", depth)
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
            self._debug_print("Nested MULTIEQUAL found", depth)
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

    def _varnode_requires_recursive_expansion(self, varnode) -> bool:
        if varnode is None:
            return False
        def_op = varnode.getDef()
        if def_op is None:
            return False
        return self._op_requires_recursive_expansion(def_op)

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

        simplified_conditions = ConditionSimplifier.simplify_conditions_object_centric(
            list(base_conditions)
        )
        normalized_value = traced_value
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
            pcode_op_ref=_pcode_op_ref_from_tracer(self.tracer, pcode_op),
        )

    def _expand_expression_cases(
        self,
        expr: Optional[Expression],
        base_conditions: List[Condition],
        depth: int,
    ) -> List[ExpandedValue]:
        if expr is None:
            return []

        if (
            not self._expression_contains_unknown_or_call(expr)
            and not self._expression_contains_phi(expr)
            and (
                expression_contains_post_state_reads(expr)
                or _expression_contains_observed_loads(expr)
            )
        ):
            return [
                ExpandedValue(
                    expr,
                    ConditionSimplifier.simplify_conditions_object_centric(base_conditions),
                )
            ]

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
                simplified = ConditionSimplifier.simplify_conditions_object_centric(
                    combined_conditions
                )
                if ConditionSimplifier.object_centric_is_contradiction(simplified):
                    continue
                expanded.extend(
                    self._expand_expression_cases(
                        value,
                        simplified,
                        depth + 1,
                    )
                )
            return (
                self._deduplicate_expanded_values(
                    expanded, depth, label="PHI expression cases"
                )
                if expanded
                else []
            )

        if expr.expr_type == ExpressionType.MEMORY and expr.operands:
            addr_cases = self._expand_expression_cases(expr.operands[0], base_conditions, depth + 1)
            if not addr_cases:
                return [
                    ExpandedValue(
                        expr,
                        ConditionSimplifier.simplify_conditions_object_centric(base_conditions),
                    )
                ]
            expanded = []
            for addr_case in addr_cases:
                simplified = ConditionSimplifier.simplify_conditions_object_centric(
                    addr_case.conditions
                )
                if ConditionSimplifier.object_centric_is_contradiction(simplified):
                    continue
                rebuilt = Expression.memory(
                    addr_case.value,
                    expr.size,
                    read_order_key=expr.read_order_key,
                    runtime_ref=getattr(expr, "runtime_ref", None),
                )
                expanded.append(ExpandedValue(rebuilt, simplified))
            return (
                self._deduplicate_expanded_values(
                    expanded, depth, label="MEMORY expression cases"
                )
                if expanded
                else []
            )

        if expr.expr_type == ExpressionType.UNARY_OP and expr.operands:
            operand_cases = self._expand_expression_cases(expr.operands[0], base_conditions, depth + 1)
            if not operand_cases:
                return [
                    ExpandedValue(
                        expr,
                        ConditionSimplifier.simplify_conditions_object_centric(base_conditions),
                    )
                ]
            expanded = []
            for operand_case in operand_cases:
                simplified = ConditionSimplifier.simplify_conditions_object_centric(
                    operand_case.conditions
                )
                if ConditionSimplifier.object_centric_is_contradiction(simplified):
                    continue
                if expr.operator is None:
                    continue
                rebuilt = Expression.unary_op(expr.operator, operand_case.value)
                rebuilt.size = expr.size
                expanded.append(ExpandedValue(rebuilt, simplified))
            return (
                self._deduplicate_expanded_values(
                    expanded, depth, label="UNARY_OP expression cases"
                )
                if expanded
                else []
            )

        if expr.expr_type == ExpressionType.BINARY_OP and len(expr.operands) == 2:
            left_cases = self._expand_expression_cases(expr.operands[0], base_conditions, depth + 1)
            right_cases = self._expand_expression_cases(expr.operands[1], base_conditions, depth + 1)
            if not left_cases:
                left_cases = [
                    ExpandedValue(
                        expr.operands[0],
                        ConditionSimplifier.simplify_conditions_object_centric(base_conditions),
                    )
                ]
            if not right_cases:
                right_cases = [
                    ExpandedValue(
                        expr.operands[1],
                        ConditionSimplifier.simplify_conditions_object_centric(base_conditions),
                    )
                ]
            if expr.operator is None:
                return []
            expanded = self._combine_input_expansions_with_conditions(
                expr.operator,
                [left_cases, right_cases],
                [],
                depth,
                output_size=expr.size,
            )
            return (
                self._deduplicate_expanded_values(
                    expanded, depth, label=f"{expr.operator} expression cases"
                )
                if expanded
                else []
            )

        if expr.expr_type == ExpressionType.INTRINSIC and expr.operands:
            operand_cases = [
                self._expand_expression_cases(operand, base_conditions, depth + 1)
                for operand in expr.operands
            ]
            normalized_cases = []
            for operand, cases in zip(expr.operands, operand_cases):
                normalized_cases.append(
                    cases
                    or [
                        ExpandedValue(
                            operand,
                            ConditionSimplifier.simplify_conditions_object_centric(base_conditions),
                        )
                    ]
                )
            expanded = self._combine_input_expansions_with_conditions(
                expr.name or "INTRINSIC",
                normalized_cases,
                [],
                depth,
                output_size=expr.size,
                opcode=getattr(expr, "opcode", None),
            )
            return (
                self._deduplicate_expanded_values(
                    expanded, depth, label=f"{expr.name or 'INTRINSIC'} expression cases"
                )
                if expanded
                else []
            )

        return [
            ExpandedValue(
                expr,
                ConditionSimplifier.simplify_conditions_object_centric(base_conditions),
            )
        ]

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

        branch_sensitive_observed = None
        if (
            traced is not None
            and self.effect_summary is not None
            and getattr(self.effect_summary, "effects", None)
            and self.parameters
        ):
            rewritten_observed = rewrite_observed_loads_from_effects(
                traced,
                conditions,
                self.effect_summary.effects,
                self.parameters,
            )
            if (
                rewritten_observed is not None
                and not _expressions_equivalent(rewritten_observed, traced)
                and self._expression_contains_phi(rewritten_observed)
            ):
                branch_sensitive_observed = rewritten_observed

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
        if (
            branch_sensitive_observed is not None
            and not self._expression_contains_phi(canonicalized)
        ):
            return branch_sensitive_observed
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

        if requires_recursive_expansion and self._operation_may_benefit_from_whole_object_shortcut(pcode_op):
            traced_shortcut = self._expand_whole_operation_object_centrically(
                pcode_op,
                conditions,
                depth,
                output_size=output_size,
                context_label="input",
            )
            if traced_shortcut is not None:
                return traced_shortcut

        if not requires_recursive_expansion:
            traced_value = self._trace_operation_expression(
                pcode_op,
                conditions,
                depth,
                output_size=output_size,
            )
            if traced_value is not None and not self._expression_contains_unknown_or_call(traced_value) and not self._expression_contains_phi(traced_value):
                if self._debug_available():
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
                self._debug_print("  No recursive expansion target in inputs, simple trace", depth)
                value = self.tracer._trace_pcode_op(pcode_op, depth, use_cache=False)
                value = self._canonicalize_traced_expression(value, conditions)
                # 出力サイズを設定
                if value.size == 0 and output_size > 0:
                    value.size = output_size
                return [ExpandedValue(value, conditions)]

        self._debug_print("  Recursive expansion target found in inputs, expanding recursively", depth)
        
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
            opcode=getattr(pcode_op, "getOpcode", lambda: None)(),
            pcode_op_ref=_pcode_op_ref_from_tracer(self.tracer, pcode_op),
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

        if requires_recursive_expansion and self._operation_may_benefit_from_whole_object_shortcut(pcode_op):
            output = pcode_op.getOutput()
            output_size = output.getSize() if output else 0
            traced_shortcut = self._expand_whole_operation_object_centrically(
                pcode_op,
                base_conditions,
                depth,
                output_size=output_size,
                context_label="top-level",
            )
            if traced_shortcut is not None:
                return traced_shortcut

        if not requires_recursive_expansion:
            traced_value = self._trace_operation_expression(
                pcode_op,
                base_conditions,
                depth,
            )
            if traced_value is not None and not self._expression_contains_unknown_or_call(traced_value) and not self._expression_contains_phi(traced_value):
                if self._debug_available():
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
            opcode=getattr(pcode_op, "getOpcode", lambda: None)(),
            pcode_op_ref=_pcode_op_ref_from_tracer(self.tracer, pcode_op),
        )
        return self._maybe_replace_budget_results_with_traced_fallback(
            pcode_op,
            combined,
            base_conditions,
            depth,
            output_size=output_size,
        )

    def _operation_may_benefit_from_whole_object_shortcut(self, pcode_op, max_depth: int = 4) -> bool:
        if pcode_op is None or max_depth <= 0:
            return False
        target_mnemonics = {"INDIRECT", "LOAD", "MULTIEQUAL"}
        try:
            if str(pcode_op.getMnemonic()) in target_mnemonics:
                return True
        except Exception:
            pass
        seen_ops: Set[int] = set()
        try:
            num_inputs = int(pcode_op.getNumInputs())
        except Exception:
            num_inputs = 0
        for index in range(num_inputs):
            try:
                varnode = pcode_op.getInput(index)
            except Exception:
                continue
            if self._varnode_subgraph_contains_mnemonics(varnode, target_mnemonics, max_depth, seen_ops):
                return True
        return False

    def _varnode_subgraph_contains_mnemonics(
        self,
        varnode,
        target_mnemonics: Set[str],
        remaining_depth: int,
        seen_ops: Set[int],
    ) -> bool:
        if varnode is None or remaining_depth <= 0:
            return False
        try:
            def_op = varnode.getDef()
        except Exception:
            def_op = None
        if def_op is None:
            return False
        op_identity = id(def_op)
        if op_identity in seen_ops:
            return False
        seen_ops.add(op_identity)
        try:
            mnemonic = str(def_op.getMnemonic())
        except Exception:
            mnemonic = ""
        if mnemonic in target_mnemonics:
            return True
        try:
            num_inputs = int(def_op.getNumInputs())
        except Exception:
            num_inputs = 0
        for index in range(num_inputs):
            try:
                child = def_op.getInput(index)
            except Exception:
                continue
            if self._varnode_subgraph_contains_mnemonics(
                child,
                target_mnemonics,
                remaining_depth - 1,
                seen_ops,
            ):
                return True
        return False

    def _expand_whole_operation_object_centrically(
        self,
        pcode_op,
        base_conditions: List[Condition],
        depth: int,
        *,
        output_size: int = 0,
        context_label: str = "operation",
    ) -> Optional[List[ExpandedValue]]:
        """Prefer whole-operation traced expansion when it preserves correlated object-state reads.

        Recursive operand-by-operand expansion can lose the correlation between multiple
        reads that originate from the same post-state snapshot. Before we Cartesian-combine
        child expansions, try to expand the traced operation as one object graph.
        """
        traced_value = self._trace_operation_expression(
            pcode_op,
            base_conditions,
            depth,
            output_size=output_size,
        )
        if traced_value is None or self._expression_contains_unknown_or_call(traced_value):
            return None

        if not (
            self._expression_contains_phi(traced_value)
            or expression_contains_post_state_reads(traced_value)
            or _expression_contains_observed_loads(traced_value)
        ):
            return None

        expanded_traced = self._expand_expression_cases(
            traced_value,
            base_conditions,
            depth + 1,
        )
        if not expanded_traced:
            return None

        if self._debug_available():
            self._debug_print(
                f"Using whole-{context_label} object-centric expansion shortcut: "
                f"{self._debug_expr_summary(traced_value)} -> {len(expanded_traced)} case(s)",
                depth,
            )
        return self._deduplicate_expanded_values(
            expanded_traced,
            depth,
            label=f"{pcode_op.getMnemonic()} whole-{context_label} cases",
            pcode_op_ref=_pcode_op_ref_from_tracer(self.tracer, pcode_op),
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
        opcode: Optional[int] = None,
        pcode_op_ref=None,
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
                    pcode_op_ref=pcode_op_ref,
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
                if not ConditionSimplifier.object_centric_is_contradiction(combined_conds):
                    if mnemonic in (
                        "INT2FLOAT",
                        "INT_NEGATE",
                        "INT_2COMP",
                        "BOOL_NEGATE",
                        "INT_ZEXT",
                        "INT_SEXT",
                    ):
                        new_value = Expression.unary_op(mnemonic, ev.value)
                        if mnemonic in ("INT2FLOAT", "INT_ZEXT", "INT_SEXT") and output_size > 0:
                            # Conversion width is the P-code output Varnode
                            # width, not the input width inherited by unary_op().
                            new_value.size = output_size
                    else:
                        new_value = ev.value
                    result.append(ExpandedValue(new_value, combined_conds))
            return self._finalize_combined_results(
                mnemonic,
                result,
                base_conditions,
                depth,
                pcode_op_ref=pcode_op_ref,
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
                            pcode_op_ref=pcode_op_ref,
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
                    
                    if (
                        ConditionSimplifier.object_centric_is_contradiction(combined_conds)
                        or ConditionSimplifier.is_contradiction(combined_conds)
                    ):
                        self._debug_print("  Combination contradictory, skip", depth)
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
                        new_value = self._build_combined_operation_expression(
                            mnemonic,
                            [left_ev.value, right_ev.value],
                            output_size=output_size,
                            opcode=opcode,
                        )
                    simplified_conds = ConditionSimplifier.simplify_conditions_object_centric(
                        combined_conds
                    )
                    normalized_value = new_value
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
                            pcode_op_ref=pcode_op_ref,
                        )

            return self._finalize_combined_results(
                mnemonic,
                list(result_map.values()),
                base_conditions,
                depth,
                pcode_op_ref=pcode_op_ref,
            )
        
        # 3つ以上の入力は intrinsic として保持しつつ、条件は全組み合わせで構成する
        self._debug_print(f"  Combining n-ary operation ({len(input_expansions)} inputs)", depth)
        result_map = {}
        novel_results = 0

        from itertools import product

        for variant_tuple in product(*input_expansions):
            combined_conds: List[Condition] = list(base_conditions)
            operands: List[Expression] = []
            for expanded in variant_tuple:
                combined_conds.extend(expanded.conditions)
                operands.append(expanded.value)

            if ConditionSimplifier.object_centric_is_contradiction(combined_conds):
                continue

            simplified_conds = ConditionSimplifier.simplify_conditions_object_centric(
                combined_conds
            )
            new_value = self._build_combined_operation_expression(
                mnemonic,
                operands,
                output_size=output_size,
                opcode=opcode,
            )
            normalized_value = new_value
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
            if novel_results > self._max_combination_attempts:
                return self._finalize_combined_results(
                    mnemonic,
                    list(result_map.values()),
                    base_conditions,
                    depth,
                    over_budget=True,
                    pcode_op_ref=pcode_op_ref,
                )

        return list(result_map.values()) or [ExpandedValue(Expression.unknown(f"{mnemonic}_fail"), base_conditions)]

    def _build_combined_operation_expression(
        self,
        mnemonic: str,
        operands: List[Expression],
        *,
        output_size: int = 0,
        opcode: Optional[int] = None,
    ) -> Expression:
        intrinsic = resolve_pcode_intrinsic(opcode=opcode, mnemonic=mnemonic)
        if intrinsic is not None:
            expr = Expression.intrinsic(
                intrinsic.mnemonic,
                operands,
                size=output_size,
                opcode=intrinsic.opcode,
            )
        elif len(operands) == 1:
            expr = operands[0]
        elif len(operands) == 2:
            expr = Expression.binary_op(mnemonic, operands[0], operands[1])
        else:
            expr = Expression.intrinsic(
                mnemonic,
                operands,
                size=output_size,
                opcode=opcode,
            )
        if output_size > 0 and getattr(expr, "size", 0) == 0:
            expr.size = output_size
        return expr
    
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

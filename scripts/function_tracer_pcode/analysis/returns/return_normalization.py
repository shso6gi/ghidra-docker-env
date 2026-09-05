"""Stateless method implementations extracted from ``scripts.function_tracer_pcode.analysis.returns.analyzer``."""

from __future__ import annotations

from typing import Any, Callable, Dict, List, Optional, Tuple
from scripts.function_tracer_pcode.core.analysis import FunctionReturnAnalysis
from scripts.function_tracer_pcode.core.expression import Condition, Expression, ExpressionType
from scripts.function_tracer_pcode.core.structural import StructuralKey
from scripts.function_tracer_pcode.analysis.returns._shared import (
    ConditionSimplifier,
    ConditionTracker,
    PcodeTracer,
    _PCODE_CALL_OPCODES,
    _PCODE_OPCODE_BY_MNEMONIC,
    _PCODE_VALUE_PASSTHROUGH_OPCODES,
    _SIGNED_COMPARE_TO_UNSIGNED,
    _TrackedReturnValue,
    _UNSIGNED_COMPARE_TO_SIGNED,
    _expressions_equivalent,
    _reduce_expression_under_conditions,
    canonicalize_expr_read_location,
    expression_contains_post_state_reads,
    expression_matches_stale_post_state_replay,
    locations_match,
    promote_effect_value_match_to_post_state_read,
)
from scripts.function_tracer_pcode.analysis.returns.debug_reporter import DebugReporter
from scripts.function_tracer_pcode.analysis.returns.expression_cases import ExpressionCaseService
from scripts.function_tracer_pcode.analysis.returns.condition_logic import ConditionLogicService
from scripts.function_tracer_pcode.analysis.returns.stack_protector import StackProtectorService
from scripts.function_tracer_pcode.analysis.returns.pcode_sites import PcodeSiteService
from scripts.function_tracer_pcode.analysis.returns.control_recovery import ReturnPathSelectionService
from scripts.function_tracer_pcode.analysis.returns.phi_origins import expression_contains_phi


class ReturnNormalizationService:
    """ReturnAnalyzer から切り出した return 値正規化（分割正規化・符号書き換え・tracked value 書き換え）の collaborator。

    facade 状態のうち読むのは現在パラメータ / 現在 effect summary / debug フラグで、いずれも引数なし
    supplier として注入し呼び出し時に読む。式ケース・条件論理・stack-protector・p-code site の各 collaborator は
    直接依存。PHI 含有判定は ``phi_origins.expression_contains_phi``（純関数）を import する。
    未抽出 family（lifecycle / effect_integration / return_extraction / parameters / control_recovery /
    call_recovery）が所有する helper は facade 経由で遅延 dispatch する callable として注入する。
    """

    def __init__(
        self,
        *,
        return_paths: ReturnPathSelectionService,
        expression_cases: ExpressionCaseService,
        condition_logic: ConditionLogicService,
        stack_protector: StackProtectorService,
        pcode_sites: PcodeSiteService,
        debug_reporter: DebugReporter,
        count_memory_reads: Callable[..., Any],
        propagate_indirect_return_effect: Callable[..., Any],
        normalize_return_value_with_effect_summary: Callable[..., Any],
        tracked_return_value_is_affected_by_op: Callable[..., Any],
        merge_equivalent_return_infos: Callable[..., Any],
        exclusivize_return_regions: Callable[..., Any],
        deduplicate_tracked_return_values: Callable[..., Any],
        propagate_passthrough_input_from_op: Callable[..., Any],
        normalize_return_callother_userops: Callable[..., Any],
        current_parameters_value: Callable[..., Any],
        current_effect_summary_value: Callable[..., Any],
        debug_flag: Callable[..., Any],
    ) -> None:
        self.return_paths = return_paths
        self.expression_cases = expression_cases
        self.condition_logic = condition_logic
        self.stack_protector = stack_protector
        self.pcode_sites = pcode_sites
        self.debug_reporter = debug_reporter
        self.count_memory_reads = count_memory_reads
        self.propagate_indirect_return_effect = propagate_indirect_return_effect
        self.normalize_return_value_with_effect_summary = normalize_return_value_with_effect_summary
        self.tracked_return_value_is_affected_by_op = tracked_return_value_is_affected_by_op
        self.merge_equivalent_return_infos = merge_equivalent_return_infos
        self.exclusivize_return_regions = exclusivize_return_regions
        self.deduplicate_tracked_return_values = deduplicate_tracked_return_values
        self.propagate_passthrough_input_from_op = propagate_passthrough_input_from_op
        self.normalize_return_callother_userops = normalize_return_callother_userops
        self.current_parameters_value = current_parameters_value
        self.current_effect_summary_value = current_effect_summary_value
        self.debug_flag = debug_flag

    def normalize_return_partition(self, analysis: FunctionReturnAnalysis) -> None:
        if analysis is None:
            return
        self.normalize_return_callother_userops(analysis)
        analysis.returns = self.stack_protector.strip_stack_protector_only_conditions(analysis.returns)
        if "control_region_return_recovery" not in analysis.analysis_notes:
            analysis.returns = self.exclusivize_return_regions(analysis.returns)
        analysis.returns = self.merge_equivalent_return_infos(analysis.returns)

    def rewrite_expression_signedness(
        self,
        expr: Optional[Expression],
        preferred: Dict[Tuple[StructuralKey, int], str],
    ) -> Tuple[Optional[Expression], bool]:
        if expr is None:
            return None, False

        changed = False
        rebuilt = expr

        if expr.expr_type == ExpressionType.PHI and expr.value:
            rewritten_branches = []
            branch_changed = False
            for cond, value in expr.value:
                rewritten_cond = cond
                if cond is not None:
                    cond_expr, cond_changed = self.rewrite_expression_signedness(
                        cond.expression,
                        preferred,
                    )
                    rewritten_cond = Condition(cond_expr, cond.negated)
                    branch_changed = branch_changed or cond_changed
                rewritten_value, value_changed = self.rewrite_expression_signedness(
                    value,
                    preferred,
                )
                branch_changed = branch_changed or value_changed
                rewritten_branches.append((rewritten_cond, rewritten_value))
            if branch_changed:
                rebuilt = expr.clone_with(value=rewritten_branches)
                changed = True
        elif getattr(expr, "operands", None):
            rewritten_operands = []
            operand_changed = False
            for operand in expr.operands:
                rewritten_operand, child_changed = self.rewrite_expression_signedness(
                    operand,
                    preferred,
                )
                rewritten_operands.append(rewritten_operand)
                operand_changed = operand_changed or child_changed
            if operand_changed:
                rebuilt = expr.clone_with(operands=rewritten_operands)
                changed = True

        if (
            rebuilt.expr_type == ExpressionType.BINARY_OP
            and rebuilt.operator in set(_UNSIGNED_COMPARE_TO_SIGNED) | set(_SIGNED_COMPARE_TO_UNSIGNED)
        ):
            fact = ConditionSimplifier.extract_scalar_constraint(Condition(rebuilt, False))
            if fact is not None:
                desired = preferred.get(fact.key)
                if desired == "signed" and rebuilt.operator in _UNSIGNED_COMPARE_TO_SIGNED:
                    rebuilt = rebuilt.clone_with(operator=_UNSIGNED_COMPARE_TO_SIGNED[rebuilt.operator])
                    changed = True
                elif desired == "unsigned" and rebuilt.operator in _SIGNED_COMPARE_TO_UNSIGNED:
                    rebuilt = rebuilt.clone_with(operator=_SIGNED_COMPARE_TO_UNSIGNED[rebuilt.operator])
                    changed = True

        return rebuilt, changed

    def rewrite_tracked_return_values_for_op(
        self,
        tracked_values: List[_TrackedReturnValue],
        pcode_op,
        *,
        tracer: Optional[PcodeTracer],
        condition_tracker: Optional[ConditionTracker],
        path_conditions: Optional[List[Condition]] = None,
        current_function=None,
    ) -> Optional[List[_TrackedReturnValue]]:
        rewritten: List[_TrackedReturnValue] = []
        for tracked in tracked_values:
            updated = self.rewrite_single_tracked_return_value_for_op(
                tracked,
                pcode_op,
                tracer=tracer,
                condition_tracker=condition_tracker,
                path_conditions=path_conditions,
                current_function=current_function,
            )
            if updated is None:
                return None
            rewritten.extend(updated)
        return self.deduplicate_tracked_return_values(rewritten)

    def rewrite_single_tracked_return_value_for_op(
        self,
        tracked: _TrackedReturnValue,
        pcode_op,
        *,
        tracer: Optional[PcodeTracer],
        condition_tracker: Optional[ConditionTracker],
        path_conditions: Optional[List[Condition]] = None,
        current_function=None,
    ) -> Optional[List[_TrackedReturnValue]]:
        if not self.tracked_return_value_is_affected_by_op(
            tracked,
            pcode_op,
            tracer=tracer,
            current_function=current_function,
        ):
            return [tracked]

        opcode = self.pcode_sites.get_pcode_opcode(pcode_op)
        if opcode in _PCODE_CALL_OPCODES:
            return None

        if opcode in _PCODE_VALUE_PASSTHROUGH_OPCODES:
            propagated = self.propagate_passthrough_input_from_op(pcode_op, tracer)
            return propagated if propagated else None

        if opcode == _PCODE_OPCODE_BY_MNEMONIC["MULTIEQUAL"]:
            propagated = self.return_paths.propagate_multiequal_input_for_return_path(
                pcode_op,
                tracer=tracer,
                condition_tracker=condition_tracker,
                path_conditions=path_conditions,
            )
            return propagated if propagated else None

        if opcode == _PCODE_OPCODE_BY_MNEMONIC["INDIRECT"]:
            propagated = self.propagate_indirect_return_effect(
                tracked,
                pcode_op,
                tracer=tracer,
            )
            return propagated if propagated else None

        return None

    def normalize_bound_parameter_values(
        self,
        bound_parameter_values: Optional[Dict[int, Expression]],
    ) -> Dict[int, Expression]:
        normalized: Dict[int, Expression] = {}
        for index, expr in (bound_parameter_values or {}).items():
            try:
                normalized_index = int(index)
            except Exception:
                continue
            if normalized_index < 0 or expr is None:
                continue
            normalized[normalized_index] = self.expression_cases.clone_expression(expr)
        return normalized

    def normalize_bound_parameter_storage_values(
        self,
        bound_parameter_storage_values: Optional[Dict[Tuple[Any, ...], Expression]],
    ) -> Dict[Tuple[Any, ...], Expression]:
        normalized: Dict[Tuple[Any, ...], Expression] = {}
        for key, expr in (bound_parameter_storage_values or {}).items():
            if key is None or expr is None:
                continue
            try:
                normalized_key = tuple(key)
            except Exception:
                continue
            if not normalized_key:
                continue
            normalized[normalized_key] = self.expression_cases.clone_expression(expr)
        return normalized

    def rewrite_drops_composite_location_wrapper(
        self,
        original: Optional[Expression],
        rewritten: Optional[Expression],
        conditions: List[Condition],
    ) -> bool:
        if original is None or rewritten is None:
            return False
        if original.expr_type not in {
            ExpressionType.BINARY_OP,
            ExpressionType.UNARY_OP,
            ExpressionType.CALL,
            ExpressionType.INTRINSIC,
        }:
            return False

        original_location = canonicalize_expr_read_location(
            original,
            self.current_parameters_value(),
        )
        rewritten_location = canonicalize_expr_read_location(
            rewritten,
            self.current_parameters_value(),
        )
        if (
            original_location is None
            or rewritten_location is None
            or not locations_match(original_location, rewritten_location, conditions)
        ):
            return False
        if not self.expression_cases.is_direct_location_carrier(rewritten):
            return False
        current_effect_summary = self.current_effect_summary_value()
        if (
            current_effect_summary is not None
            and (
                (
                    promote_effect_value_match_to_post_state_read(
                        original,
                        original_location,
                        conditions,
                        current_effect_summary.effects,
                        self.current_parameters_value(),
                        symbolic_post_state=True,
                    )
                    is not None
                )
                or expression_matches_stale_post_state_replay(
                    original,
                    rewritten,
                    conditions,
                    current_effect_summary.effects,
                    self.current_parameters_value(),
                )
            )
        ):
            return False
        return self.expression_cases.expression_has_nontrivial_location_wrapper(
            original,
            original_location,
        )

    def normalize_expanded_return_value(
        self,
        value: Expression,
        conditions: List[Condition],
    ) -> Expression:
        normalized_value = value
        started_with_phi = expression_contains_phi(value)
        effect_summary = self.current_effect_summary_value()
        has_effects = effect_summary is not None and bool(effect_summary.effects)

        if started_with_phi:
            reduced_value = _reduce_expression_under_conditions(value, conditions)
            reduced_value = self.condition_logic.reduce_phi_expression_under_conditions_with_smt(
                reduced_value if reduced_value is not None else value,
                conditions,
            )
            if reduced_value is not None:
                normalized_value = reduced_value
            if self.debug_flag() and normalized_value is not value:
                self.debug_reporter.debug_print(
                    "Reduced PHI-bearing expanded return under active conditions: "
                    f"{self.debug_reporter.debug_expr_summary(value)} -> {self.debug_reporter.debug_expr_summary(normalized_value)}"
                )

        substituted_value = self.condition_logic.substitute_parameter_constants_under_conditions(
            normalized_value,
            conditions,
        )
        if substituted_value is not None and substituted_value is not normalized_value:
            normalized_value = substituted_value
            if self.debug_flag():
                self.debug_reporter.debug_print(
                    "Specialized expanded return under exact parameter conditions: "
                    f"{self.debug_reporter.debug_expr_summary(value)} -> {self.debug_reporter.debug_expr_summary(normalized_value)}"
                )
        assignments = self.condition_logic.parameter_constant_assignments_from_conditions(conditions)
        evaluated_value = self.condition_logic.evaluate_expression_under_parameter_assignments(
            normalized_value,
            assignments,
        )
        if evaluated_value is not None and evaluated_value is not normalized_value:
            normalized_value = evaluated_value
            if self.debug_flag():
                self.debug_reporter.debug_print(
                    "Evaluated expanded return PHI selectors under exact parameter conditions: "
                    f"{self.debug_reporter.debug_expr_summary(value)} -> {self.debug_reporter.debug_expr_summary(normalized_value)}"
                )

        if has_effects:
            assert effect_summary is not None
            canonicalized = self.normalize_return_value_with_effect_summary(
                normalized_value,
                conditions,
                effect_summary,
            )
            if canonicalized is not None:
                if self.debug_flag() and canonicalized is not normalized_value:
                    self.debug_reporter.debug_print(
                        "Normalized expanded return with definite post-state replay: "
                        f"{self.debug_reporter.debug_expr_summary(normalized_value)} -> "
                        f"{self.debug_reporter.debug_expr_summary(canonicalized)}"
                    )
                normalized_value = canonicalized

        return normalized_value

    def should_replay_canonicalized_return(
        self,
        canonicalized: Optional[Expression],
        original: Expression,
    ) -> bool:
        return (
            canonicalized is not None
            and not _expressions_equivalent(canonicalized, original)
            and not expression_contains_post_state_reads(canonicalized)
            and self.count_memory_reads(canonicalized) > self.count_memory_reads(original)
        )


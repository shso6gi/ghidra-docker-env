# -*- coding: utf-8 -*-
"""Bounded fallback refinement for unresolved recursive call sites."""

from __future__ import annotations

import inspect
from dataclasses import replace
from typing import (
    Any,
    Callable,
    Dict,
    FrozenSet,
    List,
    Mapping,
    NamedTuple,
    Optional,
    Sequence,
    Set,
    Tuple,
)

from scripts.function_tracer_pcode.core.evidence_authority import record_function_unary_evidence
from scripts.function_tracer_pcode.core.operand_derivation import OperandDerivationRefused
from scripts.function_tracer_pcode.core import (
    CallTargetRef,
    Condition,
    DeferredCallInfo,
    Expression,
    ExpressionType,
    FunctionReturnAnalysis,
    ReturnInfo,
    ReturnPathEvidence,
)
from scripts.function_tracer_pcode.analysis.condition import (
    ConditionSimplifier,
    ConditionNormalizer,
)
from scripts.function_tracer_pcode.analysis.effects.call_boundary import (
    CallSite,
    CalleeTimeline,
    import_callee_condition,
    import_callee_expression,
)
from scripts.function_tracer_pcode.analysis.effects.summary import (
    _build_parameter_replacements,
    _call_arguments_width_safe_for_callee_analysis,
    _coerce_argument_to_callee_parameter,
    _coerce_storage_info,
    _enumerate_constant_expression_branches,
    _resolve_parameter_descriptor,
    _storage_infos_match,
    substitute_condition,
    substitute_expression,
)
from scripts.function_tracer_pcode.analysis.returns.summary_returns import (
    _return_region_summary_proof_id_from_evidence,
    summary_return_acceptance_proof_id_from_evidence,
)


class ExpressionExpansion(NamedTuple):
    """1 つの展開結果と、その値を作るために採用した callee の provenance。

    Issue #131: ``callees`` は展開に寄与した callee 解析の識別子（``id()``）の集合。
    中間展開に持たせておき、最終的に caller の refined return 集合へ残ったものだけを
    採用済み callee として確定する。
    """

    value: Optional[Expression]
    conditions: List[Condition]
    callees: FrozenSet[int] = frozenset()


class ConditionExpansion(NamedTuple):
    """条件列 1 通りと、その条件列を作るために採用した callee の provenance。"""

    conditions: List[Condition]
    callees: FrozenSet[int] = frozenset()


def _unexpanded(expr: Optional[Expression]) -> ExpressionExpansion:
    """展開できなかった（= callee を採用していない）式をそのまま返す。"""

    return ExpressionExpansion(expr, [], frozenset())


def _analysis_entry_offset(analysis: Optional[FunctionReturnAnalysis]) -> Optional[int]:
    """解析した関数の入口（deferred call が caller 自身の op かを見分ける: Issue #281）。"""

    function_ref = getattr(analysis, "function_ref", None)
    return getattr(function_ref, "entry_offset", None)


def _runtime_expression_signature(expr: Optional[Expression]):
    if expr is None:
        return ("none",)
    return ConditionNormalizer.expression_signature(expr)


def _runtime_conditions_signature(conditions: Sequence[Condition]):
    return ConditionNormalizer.conditions_signature(conditions)


def _expression_is_fully_resolved(expr: Optional[Expression]) -> bool:
    if expr is None:
        return True
    if expr.expr_type in {ExpressionType.UNKNOWN, ExpressionType.CALL}:
        return False
    if expr.expr_type == ExpressionType.PHI and expr.value:
        for cond, value in expr.value:
            if cond is not None and not _expression_is_fully_resolved(cond.expression):
                return False
            if not _expression_is_fully_resolved(value):
                return False
        return True
    for operand in getattr(expr, "operands", []) or []:
        if not _expression_is_fully_resolved(operand):
            return False
    return True


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


def _return_info_is_concrete_fallback(ret: Optional[ReturnInfo]) -> bool:
    if ret is None or not _expression_is_fully_resolved(getattr(ret, "value", None)):
        return False
    for condition in getattr(ret, "conditions", []) or []:
        if condition is None or not _expression_is_fully_resolved(condition.expression):
            return False
    return True


def _expression_contains_deferred_call_ref(expr: Optional[Expression]) -> bool:
    if expr is None:
        return False
    if expr.expr_type == ExpressionType.UNKNOWN:
        runtime_ref = getattr(expr, "runtime_ref", None)
        return getattr(runtime_ref, "deferred_call_ref", None) is not None
    if expr.expr_type == ExpressionType.PHI and expr.value:
        for cond, value in expr.value:
            if cond is not None and _expression_contains_deferred_call_ref(cond.expression):
                return True
            if _expression_contains_deferred_call_ref(value):
                return True
        return False
    for operand in getattr(expr, "operands", []) or []:
        if _expression_contains_deferred_call_ref(operand):
            return True
    return False


def _return_info_contains_deferred_call_ref(ret: Optional[ReturnInfo]) -> bool:
    if ret is None:
        return False
    if _expression_contains_deferred_call_ref(getattr(ret, "value", None)):
        return True
    for condition in getattr(ret, "conditions", []) or []:
        if condition is not None and _expression_contains_deferred_call_ref(condition.expression):
            return True
    return False


class BoundedCallRefiner:
    """
    未解決 CALL プレースホルダを、有限回の inlining で保守的に展開する。

    - fuel により無限再帰を防止
    - max_cases により分岐爆発を防止
    - 解けない部分は UNKNOWN のまま保持
    """

    def __init__(
        self,
        analysis_provider: Callable[..., Optional[FunctionReturnAnalysis]],
        *,
        max_unroll: int = 2,
        max_cases: int = 128,
        debug: bool = False,
        on_callee_adopted: Optional[Callable[[FunctionReturnAnalysis], None]] = None,
    ):
        self.analysis_provider = analysis_provider
        self.max_unroll = max(0, int(max_unroll))
        self.max_cases = max(1, int(max_cases))
        self.debug = debug
        # Issue #131: callee の戻り値を実際に caller の展開へ採用した地点で呼ばれる。
        # provider が返しただけの候補（引数 alignment 失敗、width 安全性違反、条件
        # 矛盾、展開不成立）では呼ばない。
        self.on_callee_adopted = on_callee_adopted
        self._reset_callee_provenance()
        self._analysis_provider_accepts_args = _callable_accepts_positional_args(
            analysis_provider,
            2,
        )

    def _debug(self, message: str) -> None:
        if self.debug:
            print(f"[BoundedCallRefiner] {message}")

    def _record_note(self, analysis: Optional[FunctionReturnAnalysis], note: str) -> None:
        if analysis is None or not note:
            return
        if note not in analysis.analysis_notes:
            analysis.analysis_notes.append(note)

    def _reset_callee_provenance(self) -> None:
        """1 回の ``refine_analysis`` 分の callee provenance 台帳を初期化する。"""

        # token -> callee 解析（token 発行元を強参照で保持し、id の再利用を防ぐ）
        self._callee_by_token: Dict[int, FunctionReturnAnalysis] = {}
        # id(ReturnInfo) -> (ReturnInfo, callee token 集合)
        self._return_info_callees: Dict[
            int, Tuple[ReturnInfo, FrozenSet[int]]
        ] = {}

    def _callee_provenance_token(
        self,
        callee_analysis: FunctionReturnAnalysis,
    ) -> FrozenSet[int]:
        """callee 解析 1 件に対応する provenance token を発行する。"""

        if callee_analysis is None:
            return frozenset()
        token = id(callee_analysis)
        self._callee_by_token[token] = callee_analysis
        return frozenset({token})

    def _register_return_info_callees(
        self,
        return_info: ReturnInfo,
        callees: FrozenSet[int],
    ) -> None:
        if not callees:
            return
        key = id(return_info)
        existing = self._return_info_callees.get(key)
        merged = (existing[1] | callees) if existing is not None else callees
        self._return_info_callees[key] = (return_info, merged)

    def _callees_of_return_info(self, return_info: ReturnInfo) -> FrozenSet[int]:
        entry = self._return_info_callees.get(id(return_info))
        return entry[1] if entry is not None else frozenset()

    def _notify_adopted_callees(self, adopted_returns: Sequence[ReturnInfo]) -> None:
        """最終的に caller の refined return 集合へ残った callee だけを通知する。

        Issue #131: ``results.append`` 時点ではまだ中間展開なので通知しない。
        ``_return_info_is_concrete_fallback`` による除外・caller 側 ``max_cases`` での
        打ち切り・dedup を通過して ``analysis.returns`` に残ったものだけを採用とみなす。

        PR-B: この通知は診断ではなく、採用した callee の切り捨て marker を caller へ
        伝搬して EQ/NOT_EQ を閉じる semantic 経路。失敗を握り潰すと「callee 由来の
        値は採用したが不完全性だけ失われた」状態になるため、例外はそのまま伝播させる
        （呼び出し側は refined returns を公開する前にこれを完了させる）。
        """

        if self.on_callee_adopted is None:
            return
        adopted_tokens: Set[int] = set()
        for return_info in adopted_returns or ():
            adopted_tokens |= self._callees_of_return_info(return_info)
        for token in sorted(adopted_tokens):
            self._notify_callee_adopted(self._callee_by_token.get(token))

    def _notify_callee_adopted(self, callee_analysis: Optional[FunctionReturnAnalysis]) -> None:
        """採用が確定した callee を 1 度だけ通知する（失敗は握り潰さない）。"""

        if self.on_callee_adopted is None or callee_analysis is None:
            return
        self.on_callee_adopted(callee_analysis)

    def _provide_analysis(
        self,
        target: object,
        args: Optional[Sequence[Expression]] = None,
    ) -> Optional[FunctionReturnAnalysis]:
        if self._analysis_provider_accepts_args:
            return self.analysis_provider(target, args)
        return self.analysis_provider(target)

    def refine_analysis(self, analysis: FunctionReturnAnalysis) -> bool:
        self._reset_callee_provenance()
        if analysis is None or not analysis.returns or not analysis.deferred_calls or self.max_unroll <= 0:
            return False
        analysis.normalize_deferred_calls()

        original_signature = self._analysis_signature(analysis.returns)
        refined_returns: List[ReturnInfo] = []

        for ret in analysis.returns:
            expanded = self._expand_return_info(ret, analysis, self.max_unroll, set())
            contains_deferred_call = _return_info_contains_deferred_call_ref(ret)
            if contains_deferred_call:
                concrete_expanded = [
                    candidate
                    for candidate in expanded
                    if _return_info_is_concrete_fallback(candidate)
                ]
                has_unresolved_expansion = (
                    len(concrete_expanded) != len(expanded)
                    or len(expanded) >= self.max_cases
                )
                if has_unresolved_expansion:
                    remaining_slots = max(0, self.max_cases - len(refined_returns))
                    concrete_limit = max(0, remaining_slots - 1)
                    refined_returns.extend(concrete_expanded[:concrete_limit])
                else:
                    refined_returns.extend(concrete_expanded)
            else:
                refined_returns.extend(expanded)
                has_unresolved_expansion = False

            if contains_deferred_call and has_unresolved_expansion:
                refined_returns.append(ret)
                self._record_note(
                    analysis,
                    "bounded_call_refinement_preserved_unresolved_deferred_call",
                )
            if len(refined_returns) >= self.max_cases:
                refined_returns = refined_returns[: self.max_cases]
                break

        if analysis.unknown_event_count or analysis.incomplete_control_flow:
            refined_returns.extend(
                ret
                for ret in (analysis.returns or [])
                if _return_info_is_concrete_fallback(ret)
            )

        deduped = self._deduplicate_return_infos(refined_returns)
        if not deduped:
            return False

        # Issue #131: ここで初めて「最終的に採用された callee」が確定する。
        # PR-B: marker 伝搬は採用した意味入力の一部なので、refined returns を公開する
        # 前に完了させる。伝搬が失敗した場合は ``analysis.returns`` を置き換えないまま
        # 例外が伝播し、callee 由来の値だけが採用された状態は残らない。
        self._notify_adopted_callees(deduped)
        analysis.returns = deduped
        analysis.deferred_calls = self._filter_deferred_calls_in_use(analysis)

        changed = original_signature != self._analysis_signature(analysis.returns)
        if changed and "bounded_call_refinement" not in analysis.analysis_notes:
            analysis.analysis_notes.append("bounded_call_refinement")
        return changed

    def _analysis_signature(self, return_infos: Sequence[ReturnInfo]) -> Tuple[Tuple[object, object], ...]:
        signature = []
        for ret in return_infos or []:
            signature.append(
                (
                    _runtime_expression_signature(ret.value),
                    _runtime_conditions_signature(ret.conditions),
                )
            )
        return tuple(signature)

    def _expand_return_info(
        self,
        ret: ReturnInfo,
        analysis: FunctionReturnAnalysis,
        fuel: int,
        trail: Set[Tuple[object, ...]],
    ) -> List[ReturnInfo]:
        condition_states = self._expand_conditions(ret.conditions, analysis, fuel, trail)
        value_states = self._expand_expression(ret.value, analysis, fuel, trail)

        results: List[ReturnInfo] = []
        for conds, condition_callees in condition_states:
            for value_expr, extra_conditions, value_callees in value_states:
                merged_conditions = ConditionSimplifier.simplify_conditions(
                    list(conds) + list(extra_conditions)
                )
                if ConditionSimplifier.is_contradiction(merged_conditions):
                    continue
                return_path_evidence = getattr(ret, "return_path_evidence", None)
                if isinstance(return_path_evidence, ReturnPathEvidence):
                    target_guard_keys = (tuple(sorted(
                        (condition.structural_key() for condition in merged_conditions), key=repr
                    )),)
                    original_key = return_path_evidence.stable_key()
                    return_path_evidence = replace(
                        return_path_evidence,
                        path_guard_keys=target_guard_keys,
                        guard_rewrite_proof_keys=(
                            (
                                "bounded_refinement_guard_rewrite_v1",
                                original_key,
                                target_guard_keys,
                            ),
                        ),
                    )
                expanded_info = ReturnInfo(
                    address=ret.address,
                    value=value_expr,
                    conditions=merged_conditions,
                    branch_index=ret.branch_index,
                    pcode_identity=ret.pcode_identity,
                    pcode_order=ret.pcode_order,
                    pcode_time=ret.pcode_time,
                    pcode_op_ref=getattr(ret, "pcode_op_ref", None),
                    return_value_pcode_op_refs=tuple(
                        getattr(ret, "return_value_pcode_op_refs", ()) or ()
                    ),
                    return_path_evidence=return_path_evidence,
                )
                # Issue #131: この ReturnInfo を作るのに採用した callee を覚えておく。
                # 最終 ``analysis.returns`` に残ったものだけを後で採用済みとする。
                self._register_return_info_callees(
                    expanded_info,
                    condition_callees | value_callees,
                )
                results.append(expanded_info)
                if len(results) >= self.max_cases:
                    return results[: self.max_cases]
        return results

    def _expand_conditions(
        self,
        conditions: Sequence[Condition],
        analysis: FunctionReturnAnalysis,
        fuel: int,
        trail: Set[Tuple[object, ...]],
    ) -> List[ConditionExpansion]:
        states: List[ConditionExpansion] = [ConditionExpansion([], frozenset())]

        for condition in conditions or []:
            next_states: List[ConditionExpansion] = []
            expansions = self._expand_expression(condition.expression, analysis, fuel, trail)
            for prefix, prefix_callees in states:
                for expr, extra_conditions, expr_callees in expansions:
                    merged = ConditionSimplifier.simplify_conditions(
                        list(prefix) + extra_conditions + [Condition(expr, condition.negated)]
                    )
                    if ConditionSimplifier.is_contradiction(merged):
                        continue
                    next_states.append(
                        ConditionExpansion(merged, prefix_callees | expr_callees)
                    )
                    if len(next_states) >= self.max_cases:
                        break
                if len(next_states) >= self.max_cases:
                    break
            if not next_states:
                return []
            states = self._deduplicate_condition_sets(next_states)
        return states

    def _expand_expression(
        self,
        expr: Expression,
        analysis: FunctionReturnAnalysis,
        fuel: int,
        trail: Set[Tuple[object, ...]],
    ) -> List[ExpressionExpansion]:
        deferred = self._lookup_deferred_call(expr, analysis)
        if deferred is not None:
            deferred_key = deferred.identity_key()
            if fuel <= 0 or deferred_key in trail:
                return [_unexpanded(expr)]
            unfolded = self._expand_deferred_call(
                deferred,
                analysis,
                fuel - 1,
                trail | {deferred_key},
            )
            return unfolded or [_unexpanded(expr)]

        if expr is None:
            return [_unexpanded(expr)]

        if expr.expr_type in {
            ExpressionType.CONSTANT,
            ExpressionType.PARAMETER,
            ExpressionType.VARIABLE,
            ExpressionType.UNKNOWN,
            ExpressionType.LITERAL,
        }:
            return [_unexpanded(expr)]

        if expr.expr_type == ExpressionType.PHI and expr.value:
            return self._expand_phi_expression(expr, analysis, fuel, trail)

        if not expr.operands:
            return [_unexpanded(expr)]

        states: List[Tuple[List[Expression], List[Condition], FrozenSet[int]]] = [
            ([], [], frozenset())
        ]
        for operand in expr.operands:
            operand_expansions = self._expand_expression(operand, analysis, fuel, trail)
            next_states: List[Tuple[List[Expression], List[Condition], FrozenSet[int]]] = []
            for built_operands, built_conditions, built_callees in states:
                for new_operand, extra_conditions, operand_callees in operand_expansions:
                    next_states.append(
                        (
                            built_operands + [new_operand],
                            built_conditions + extra_conditions,
                            built_callees | operand_callees,
                        )
                    )
                    if len(next_states) >= self.max_cases:
                        break
                if len(next_states) >= self.max_cases:
                    break
            states = next_states
            if not states:
                return [_unexpanded(expr)]

        results: List[ExpressionExpansion] = []
        for operands, extra_conditions, state_callees in states[: self.max_cases]:
            merged_conditions = ConditionSimplifier.simplify_conditions(extra_conditions)
            if ConditionSimplifier.is_contradiction(merged_conditions):
                continue
            try:
                rebuilt = expr.derive_with_operands(operands)
            except OperandDerivationRefused as refusal:
                # Issue #281: 候補の一部だけを捨てない。ref を保てない派生が 1 つでもあれば、この node の
                # 展開をまるごとあきらめ、元の式（producer が作った、ref と operand が整合した値。展開しない
                # ときに使う値と同じ）に戻る。他の候補だけを残すと、拒否した候補の値が黙って消える
                self._record_operand_derivation_refusal(analysis, refusal)
                return [_unexpanded(expr)]
            results.append(
                ExpressionExpansion(rebuilt, merged_conditions, state_callees)
            )

        return results or [_unexpanded(expr)]

    def _expand_phi_expression(
        self,
        expr: Expression,
        analysis: FunctionReturnAnalysis,
        fuel: int,
        trail: Set[Tuple[object, ...]],
    ) -> List[ExpressionExpansion]:
        states: List[
            Tuple[List[Tuple[Optional[Condition], Expression]], List[Condition], FrozenSet[int]]
        ] = [([], [], frozenset())]
        for branch_condition, branch_value in expr.value or []:
            condition_expansions: List[
                Tuple[Optional[Condition], List[Condition], FrozenSet[int]]
            ]
            if branch_condition is None:
                condition_expansions = [(None, [], frozenset())]
            else:
                condition_expansions = [
                    (
                        Condition(condition_expr, branch_condition.negated),
                        extra_conditions,
                        condition_callees,
                    )
                    for condition_expr, extra_conditions, condition_callees in self._expand_expression(
                        branch_condition.expression,
                        analysis,
                        fuel,
                        trail,
                    )
                ]
            value_expansions = self._expand_expression(branch_value, analysis, fuel, trail)
            next_states: List[
                Tuple[List[Tuple[Optional[Condition], Expression]], List[Condition], FrozenSet[int]]
            ] = []
            for built_branches, built_conditions, built_callees in states:
                for new_condition, condition_extra, condition_callees in condition_expansions:
                    for new_value, value_extra, value_callees in value_expansions:
                        merged_extra = ConditionSimplifier.simplify_conditions(
                            list(built_conditions) + list(condition_extra) + list(value_extra)
                        )
                        if ConditionSimplifier.is_contradiction(merged_extra):
                            continue
                        next_states.append(
                            (
                                built_branches + [(new_condition, new_value)],
                                merged_extra,
                                built_callees | condition_callees | value_callees,
                            )
                        )
                        if len(next_states) >= self.max_cases:
                            break
                    if len(next_states) >= self.max_cases:
                        break
                if len(next_states) >= self.max_cases:
                    break
            states = next_states
            if not states:
                return [_unexpanded(expr)]

        results: List[ExpressionExpansion] = []
        for branches, extra_conditions, state_callees in states[: self.max_cases]:
            rebuilt = Expression.phi(branches)
            rebuilt.size = expr.size
            results.append(
                ExpressionExpansion(rebuilt, list(extra_conditions), state_callees)
            )
        return self._deduplicate_expression_expansions(results) or [_unexpanded(expr)]

    def _expand_deferred_call(
        self,
        deferred: DeferredCallInfo,
        caller_analysis: FunctionReturnAnalysis,
        fuel: int,
        trail: Set[Tuple[object, ...]],
    ) -> List[ExpressionExpansion]:
        try:
            return self._expand_deferred_call_candidates(deferred, caller_analysis, fuel, trail)
        except OperandDerivationRefused as refusal:
            # Issue #281: callee の式を caller の引数へ置き換える派生が ref を保てない。callee の元の式は
            # caller の文脈では別の値（callee の parameter を指す）なので、その node だけを元に戻すことは
            # できない。候補の一部だけを捨てると、その target の値が黙って消える。呼び出しの展開を
            # まるごとやめ、呼び出し側は展開しない deferred call（`_unexpanded`）を使う
            self._record_operand_derivation_refusal(caller_analysis, refusal)
            return []

    def _expand_deferred_call_candidates(
        self,
        deferred: DeferredCallInfo,
        caller_analysis: FunctionReturnAnalysis,
        fuel: int,
        trail: Set[Tuple[object, ...]],
    ) -> List[ExpressionExpansion]:
        results: List[ExpressionExpansion] = []
        candidates = self._resolve_deferred_call_candidates(
            deferred
        )
        if not candidates:
            self._record_note(caller_analysis, "bounded_call_refinement_deferred_target_unresolved")
            self._debug(
                f"Skipped deferred call '{deferred.deferred_call_ref.display_name()}': "
                "no resolved callee analysis"
            )
            return []

        had_alignment_failure = False
        had_return_expansion = False
        # 展開の evidence は、呼び出しの展開がまるごと確定してから記録する（後の候補の派生が拒否されたら
        # 展開ごと使わないので、先に記録した evidence が使われない展開を指してしまう。Issue #281）
        pending_evidence: List[Dict[str, Any]] = []

        def _flush_pending_evidence() -> None:
            for evidence in pending_evidence:
                self._record_bounded_call_refinement_expansion_evidence(**evidence)
            pending_evidence.clear()

        for _target_ref, target_conditions, callee_analysis in candidates:
            already_specialized = self._analysis_is_fully_argument_specialized(callee_analysis)
            if already_specialized:
                aligned_arguments = []
                replacements = {}
            else:
                aligned_arguments = self._align_deferred_arguments_to_callee(
                    deferred,
                    caller_analysis.parameters,
                    callee_analysis.parameters,
                )
                if len(aligned_arguments) < len(callee_analysis.parameters):
                    had_alignment_failure = True
                    self._debug(
                        f"Skipped deferred call '{deferred.deferred_call_ref.display_name()}': expected "
                        f"{len(callee_analysis.parameters)} args, got {len(aligned_arguments)}"
                    )
                    continue
                if not _call_arguments_width_safe_for_callee_analysis(
                    callee_analysis,
                    aligned_arguments,
                ):
                    had_alignment_failure = True
                    self._debug(
                        f"Skipped deferred call '{deferred.deferred_call_ref.display_name()}': "
                        "partial-width argument is used as a full-width callee value"
                    )
                    continue

                replacements = _build_parameter_replacements(
                    callee_analysis.parameters,
                    aligned_arguments,
                )
            # Issue #281: callee の式の memory 読み出しは callee の時間軸の上にある。caller の呼び出し位置へ
            # 移してから（callee の parameter の言葉のまま）引数へ置き換える。移せなければ
            # `CallBoundaryRefused` で、`_expand_deferred_call` が呼び出しの展開をまるごとやめる。
            # 以前はここで callee の post-state の読み出しを、置き換えた callee の effect と caller の parameter で
            # lowering していた。callee の effect の後の状態は caller の言葉で表せない（`call_boundary`）ので、
            # その読み出しは境界で拒否され、lowering は行わない
            site = CallSite.for_deferred_call(
                deferred,
                _analysis_entry_offset(caller_analysis),
            )
            timeline = CalleeTimeline.from_effect_summary(
                getattr(callee_analysis, "effect_summary", None),
                callee_analysis.parameters,
            )
            candidate_result_count = 0

            for ret in callee_analysis.returns:
                substituted_value = substitute_expression(
                    import_callee_expression(ret.value, site, timeline),
                    replacements,
                    callee_analysis.parameters,
                )
                substituted_conditions = [
                    substitute_condition(
                        import_callee_condition(cond, site, timeline),
                        replacements,
                        callee_analysis.parameters,
                    )
                    for cond in ret.conditions
                ]

                condition_sets = self._expand_conditions(
                    substituted_conditions,
                    callee_analysis,
                    fuel,
                    trail,
                )
                value_states = self._expand_expression(
                    substituted_value,
                    callee_analysis,
                    fuel,
                    trail,
                )

                for conds, nested_condition_callees in (
                    condition_sets or [ConditionExpansion([], frozenset())]
                ):
                    for value_expr, extra_conditions, nested_value_callees in value_states:
                        merged_conditions = ConditionSimplifier.simplify_conditions(
                            list(target_conditions) + list(conds) + list(extra_conditions)
                        )
                        if ConditionSimplifier.is_contradiction(merged_conditions):
                            continue
                        callee_provenance = (
                            self._callee_provenance_token(callee_analysis)
                            | nested_condition_callees
                            | nested_value_callees
                        )
                        had_return_expansion = True
                        candidate_result_count += 1
                        # Issue #131: ここはまだ中間展開。provenance だけ積んでおき、
                        # 最終 ``analysis.returns`` に残ったかどうかは refine_analysis
                        # の最後で確定する。
                        results.append(
                            ExpressionExpansion(
                                value_expr,
                                merged_conditions,
                                callee_provenance,
                            )
                        )
                        if len(results) >= self.max_cases:
                            _flush_pending_evidence()
                            self._record_note(
                                caller_analysis,
                                "bounded_call_refinement_deferred_expanded",
                            )
                            return results[: self.max_cases]
            if candidate_result_count:
                pending_evidence.append(
                    dict(
                        caller_analysis=caller_analysis,
                        deferred=deferred,
                        target_ref=_target_ref,
                        target_conditions=target_conditions,
                        callee_analysis=callee_analysis,
                        aligned_arguments=aligned_arguments,
                        result_count=candidate_result_count,
                    )
                )

        _flush_pending_evidence()
        if results:
            self._record_note(caller_analysis, "bounded_call_refinement_deferred_expanded")
        elif had_alignment_failure:
            self._record_note(caller_analysis, "bounded_call_refinement_argument_alignment_failed")
        elif not had_return_expansion:
            self._record_note(caller_analysis, "bounded_call_refinement_return_summary_unusable")
        return self._deduplicate_expression_expansions(results)

    def _resolve_deferred_call_candidates(
        self,
        deferred: DeferredCallInfo,
    ) -> List[Tuple[CallTargetRef, List[Condition], FunctionReturnAnalysis]]:
        candidates: List[Tuple[CallTargetRef, List[Condition], FunctionReturnAnalysis]] = []
        seen = set()

        def add_candidate(target_ref: CallTargetRef, conditions: Sequence[Condition]) -> None:
            call_arguments = list(getattr(deferred, "arguments", ()) or ())
            callee_analysis = None
            if call_arguments:
                callee_analysis = self._provide_analysis(target_ref, call_arguments)
            if callee_analysis is None:
                callee_analysis = self._provide_analysis(target_ref, None)
            if callee_analysis is None or not callee_analysis.returns:
                return
            key = (
                target_ref.stable_key(),
                _runtime_conditions_signature(conditions),
            )
            if key in seen:
                return
            seen.add(key)
            candidates.append((target_ref, list(conditions), callee_analysis))

        if deferred.call_target_expr is not None:
            for branch_conditions, address_value in _enumerate_constant_expression_branches(
                deferred.call_target_expr
            ):
                add_candidate(
                    CallTargetRef.from_code_address(address_value),
                    ConditionSimplifier.simplify_conditions(branch_conditions),
                )

        if deferred.target_ref is not None and not deferred.target_ref.is_unknown():
            add_candidate(deferred.target_ref, [])

        return candidates

    def _analysis_is_fully_argument_specialized(
        self,
        analysis: Optional[FunctionReturnAnalysis],
    ) -> bool:
        if analysis is None:
            return False
        parameter_count = len(getattr(analysis, "parameters", ()) or ())
        if parameter_count <= 0:
            return False
        scope_key = getattr(analysis, "analysis_scope_key", None)
        if not isinstance(scope_key, tuple) or len(scope_key) < 4:
            return False
        bound_by_index = scope_key[2] if isinstance(scope_key[2], tuple) else ()
        bound_by_storage = scope_key[3] if isinstance(scope_key[3], tuple) else ()
        return max(len(bound_by_index), len(bound_by_storage)) >= parameter_count

    def _align_deferred_arguments_to_callee(
        self,
        deferred: DeferredCallInfo,
        caller_parameters: Sequence[Dict],
        callee_parameters: Sequence[Dict],
    ) -> List[Expression]:
        arguments = list(getattr(deferred, "arguments", []) or [])
        if not callee_parameters:
            return arguments

        if self._deferred_arguments_are_pcode_callsite_ordered(deferred):
            if len(arguments) < len(callee_parameters):
                return []
            aligned: List[Expression] = []
            for argument, callee_param in zip(arguments, callee_parameters):
                coerced = _coerce_argument_to_callee_parameter(argument, callee_param)
                aligned.append(coerced if coerced is not None else argument)
            return aligned

        if len(arguments) == 1 and len(callee_parameters) == 1:
            return list(arguments)
        aligned: List[Expression] = []
        used_argument_indexes: Set[int] = set()
        for callee_param in callee_parameters:
            best_index = None
            best_score = 0
            ambiguous_best = False
            for index, argument in enumerate(arguments):
                if index in used_argument_indexes:
                    continue
                score = self._callee_argument_match_score(
                    argument,
                    caller_parameters,
                    callee_param,
                )
                if score > best_score:
                    best_score = score
                    best_index = index
                    ambiguous_best = False
                elif score == best_score and score > 0:
                    ambiguous_best = True
            if best_index is not None and best_score >= 50 and not ambiguous_best:
                used_argument_indexes.add(best_index)
                aligned.append(arguments[best_index])
                continue

        return aligned

    def _deferred_arguments_are_pcode_callsite_ordered(
        self,
        deferred: Optional[DeferredCallInfo],
    ) -> bool:
        deferred_ref = getattr(deferred, "deferred_call_ref", None)
        pcode_ref = getattr(deferred_ref, "pcode_op_ref", None)
        if pcode_ref is None:
            return False
        mnemonic = getattr(pcode_ref, "mnemonic", None)
        if mnemonic is None:
            return False
        return str(mnemonic).upper() in {"CALL", "CALLIND"}

    def _callee_argument_match_score(
        self,
        argument: Optional[Expression],
        caller_parameters: Sequence[Dict],
        callee_param: Dict,
    ) -> int:
        if argument is None:
            return 0

        caller_param = _resolve_parameter_descriptor(argument, caller_parameters)
        if caller_param is None:
            return 0
        caller_storage = _coerce_storage_info(caller_param.get("storage")) if caller_param is not None else None
        callee_storage = _coerce_storage_info(callee_param.get("storage"))
        if caller_storage is not None and callee_storage is not None and _storage_infos_match(
            caller_storage,
            callee_storage,
        ):
            return 100
        return 0

    def _lookup_deferred_call(
        self,
        expr: Optional[Expression],
        analysis: FunctionReturnAnalysis,
    ) -> Optional[DeferredCallInfo]:
        if expr is None or expr.expr_type != ExpressionType.UNKNOWN:
            return None
        runtime_ref = getattr(expr, "runtime_ref", None)
        deferred_call_ref = getattr(runtime_ref, "deferred_call_ref", None)
        deferred_key = (
            deferred_call_ref.stable_key()
            if hasattr(deferred_call_ref, "stable_key")
            else None
        )
        if deferred_key is not None:
            return (analysis.deferred_calls or {}).get(deferred_key)
        return None

    def _record_operand_derivation_refusal(
        self,
        analysis: Optional[FunctionReturnAnalysis],
        refusal: OperandDerivationRefused,
    ) -> None:
        self._record_note(
            analysis,
            f"bounded_call_refinement_operand_derivation_refused:{refusal.reason}:{refusal.ref_type}",
        )
        self._debug(f"Kept an unexpanded node: {refusal}")

    def _deduplicate_condition_sets(
        self,
        condition_sets: Sequence[ConditionExpansion],
    ) -> List[ConditionExpansion]:
        seen: Dict[Any, int] = {}
        result: List[ConditionExpansion] = []
        for conditions, callees in condition_sets:
            key = _runtime_conditions_signature(conditions)
            index = seen.get(key)
            if index is not None:
                # 同じ条件列は同じ意味なので、provenance は和集合にして残す。
                merged = result[index]
                result[index] = ConditionExpansion(
                    merged.conditions, merged.callees | callees
                )
                continue
            seen[key] = len(result)
            result.append(ConditionExpansion(list(conditions), callees))
            if len(result) >= self.max_cases:
                break
        return result

    def _deduplicate_expression_expansions(
        self,
        expansions: Sequence[ExpressionExpansion],
    ) -> List[ExpressionExpansion]:
        seen: Dict[Any, int] = {}
        result: List[ExpressionExpansion] = []
        for expr, conditions, callees in expansions:
            key = (
                _runtime_expression_signature(expr),
                _runtime_conditions_signature(conditions),
            )
            index = seen.get(key)
            if index is not None:
                merged = result[index]
                result[index] = ExpressionExpansion(
                    merged.value, merged.conditions, merged.callees | callees
                )
                continue
            seen[key] = len(result)
            result.append(ExpressionExpansion(expr, list(conditions), callees))
            if len(result) >= self.max_cases:
                break
        return result

    def _deduplicate_return_infos(
        self,
        return_infos: Sequence[ReturnInfo],
    ) -> List[ReturnInfo]:
        seen: Dict[Any, ReturnInfo] = {}
        result: List[ReturnInfo] = []
        for ret in return_infos:
            key = (
                ret.pcode_identity or ret.address,
                ret.branch_index,
                _runtime_expression_signature(ret.value),
                _runtime_conditions_signature(ret.conditions),
            )
            representative = seen.get(key)
            if representative is not None:
                # 意味的に同一の return case なので、落とした側の callee provenance は
                # 代表へ引き継ぐ（同じ結果がその callee からも得られている）。
                self._register_return_info_callees(
                    representative, self._callees_of_return_info(ret)
                )
                continue
            seen[key] = ret
            result.append(ret)
            if len(result) >= self.max_cases:
                break
        return result

    def _filter_deferred_calls_in_use(
        self,
        analysis: FunctionReturnAnalysis,
    ) -> Dict[Tuple[object, ...], DeferredCallInfo]:
        used: Set[Tuple[object, ...]] = set()
        used_targets: Set[Tuple[Any, ...]] = set()

        def visit_expression(expr: Optional[Expression]) -> None:
            if expr is None:
                return
            if expr.expr_type == ExpressionType.UNKNOWN:
                runtime_ref = getattr(expr, "runtime_ref", None)
                deferred_call_ref = getattr(runtime_ref, "deferred_call_ref", None)
                deferred_key = (
                    deferred_call_ref.stable_key()
                    if hasattr(deferred_call_ref, "stable_key")
                    else None
                )
                if deferred_key is not None:
                    used.add(deferred_key)
                target_ref = getattr(runtime_ref, "target_ref", None)
                target_key = (
                    target_ref.stable_key()
                    if hasattr(target_ref, "stable_key")
                    else None
                )
                if target_key is not None:
                    used_targets.add(target_key)
                return
            if expr.expr_type == ExpressionType.PHI and expr.value:
                for cond, value in expr.value:
                    if cond is not None:
                        visit_expression(cond.expression)
                    visit_expression(value)
                return
            for operand in expr.operands or []:
                visit_expression(operand)

        for ret in analysis.returns:
            visit_expression(ret.value)
            for cond in ret.conditions:
                visit_expression(cond.expression)

        candidates: List[
            Tuple[
                Tuple[object, ...],
                Tuple[object, ...],
                DeferredCallInfo,
                Optional[Tuple[Any, ...]],
            ]
        ] = []
        target_candidate_counts: Dict[Tuple[Any, ...], int] = {}
        for key, info in analysis.deferred_calls.items():
            info_ref = getattr(info, "deferred_call_ref", None)
            info_key = (
                info_ref.stable_key()
                if hasattr(info_ref, "stable_key")
                else key
            )
            info_target_ref = getattr(info, "target_ref", None)
            info_target_key = (
                info_target_ref.stable_key()
                if hasattr(info_target_ref, "stable_key")
                else None
            )
            candidates.append((key, info_key, info, info_target_key))
            if info_target_key is not None:
                target_candidate_counts[info_target_key] = target_candidate_counts.get(info_target_key, 0) + 1

        filtered: Dict[Tuple[object, ...], DeferredCallInfo] = {}
        for key, info_key, info, info_target_key in candidates:
            if key in used or info_key in used or (
                info_target_key is not None
                and info_target_key in used_targets
                and target_candidate_counts.get(info_target_key, 0) == 1
            ):
                filtered[info_key] = info
        return filtered

    def _record_bounded_call_refinement_expansion_evidence(
        self,
        *,
        caller_analysis: FunctionReturnAnalysis,
        deferred: DeferredCallInfo,
        target_ref: CallTargetRef,
        target_conditions: Sequence[Condition],
        callee_analysis: FunctionReturnAnalysis,
        aligned_arguments: Sequence[Expression],
        result_count: int,
    ) -> None:
        if caller_analysis is None or deferred is None or callee_analysis is None:
            return
        if int(result_count or 0) <= 0:
            return
        callee_effect_summary = getattr(callee_analysis, "effect_summary", None)
        if callee_effect_summary is None:
            self._debug("Skipped bounded refinement evidence: callee effect summary missing")
            return
        callee_effect_clean = (
            not getattr(callee_effect_summary, "effects", None)
            and not getattr(callee_effect_summary, "has_unsupported_call", False)
            and not getattr(callee_effect_summary, "incomplete_reasons", None)
        )
        if not callee_effect_clean:
            self._debug("Skipped bounded refinement evidence: callee effect summary not clean")
            return
        callee_requires_completed_summary_proof = self._callee_requires_completed_summary_proof(
            callee_analysis
        )
        callee_completed_proof_ids = self._callee_summary_completion_proof_ids(
            callee_analysis
        )
        callee_completed_proof_evidence_ids = self._callee_summary_completion_evidence_ids(
            callee_analysis
        )
        if callee_requires_completed_summary_proof and not (
            callee_completed_proof_ids or callee_completed_proof_evidence_ids
        ):
            self._debug(
                "Skipped bounded refinement evidence: summary-derived callee lacks completed proof refs"
            )
            return
        pcode_key = self._deferred_call_pcode_key(deferred)
        callee_key = self._call_target_key_for_analysis(target_ref, caller_analysis)
        argument_exprs = tuple(aligned_arguments or getattr(deferred, "arguments", ()) or ())
        argument_signature = tuple(_runtime_expression_signature(arg) for arg in argument_exprs)
        callee_partition_key = self._analysis_signature(getattr(callee_analysis, "returns", ()) or ())
        object_target_key = (
            "bounded_call_refinement_expansion",
            self._analysis_entry_key(caller_analysis),
            self._normalize_nested_tuple(pcode_key),
            self._normalize_nested_tuple(callee_key),
            argument_signature,
            self._analysis_entry_key(callee_analysis),
            callee_partition_key,
            _runtime_conditions_signature(target_conditions),
            int(result_count),
            int(self.max_unroll),
        )
        existing = tuple(getattr(caller_analysis, "completed_recovery_proof_evidence", ()) or ())
        if any(
            isinstance(item, dict)
            and self._normalize_nested_tuple(item.get("object_target_key")) == object_target_key
            and item.get("evidence_kind") == "bounded_call_refinement_expansion"
            for item in existing
        ):
            return
        content = {
            "object_derived": True,
            "status": "complete",
            "object_target_key": object_target_key,
            "callsite_pcode_key": self._normalize_nested_tuple(pcode_key),
            "callee_identity": self._normalize_nested_tuple(callee_key),
            "argument_signature": argument_signature,
            "callee_analysis_entry": self._analysis_entry_key(callee_analysis),
            "callee_return_partition_key": callee_partition_key,
            "callee_return_case_count": len(getattr(callee_analysis, "returns", ()) or ()),
            "callee_summary_requires_completed_proof": callee_requires_completed_summary_proof,
            "callee_completed_proof_ids": callee_completed_proof_ids,
            "callee_completed_proof_evidence_ids": callee_completed_proof_evidence_ids,
            "callee_effect_summary_clean": True,
            "target_conditions_key": _runtime_conditions_signature(target_conditions),
            "result_count": int(result_count),
            "max_unroll": int(self.max_unroll),
            "dependency_cycle": False,
            "truncated": False,
        }
        record = {
            "object_derived": True,
            "status": "complete",
            "evidence_kind": "bounded_call_refinement_expansion",
            "proof_stage": "bounded_call_refinement",
            "object_target_key": object_target_key,
            "proof_source": "bounded_call_refinement_deferred_expanded",
            "proof_content": content,
        }
        record_function_unary_evidence(caller_analysis, record)
        self._debug("Recorded bounded refinement expansion evidence")

    @staticmethod
    def _callee_requires_completed_summary_proof(
        callee_analysis: FunctionReturnAnalysis,
    ) -> bool:
        for ret in getattr(callee_analysis, "returns", ()) or ():
            if str(getattr(ret, "return_kind", "exact") or "exact") == "summary_derived":
                return True
            if getattr(ret, "summary_transition_evidence_key", None) is not None:
                return True
            if getattr(ret, "summary_candidate_source_key", None) is not None:
                return True
        return False

    @classmethod
    def _callee_summary_completion_proof_ids(
        cls,
        callee_analysis: FunctionReturnAnalysis,
    ) -> Tuple[Any, ...]:
        return cls._callee_summary_completion_evidence_ids(callee_analysis)

    @classmethod
    def _callee_summary_completion_evidence_ids(
        cls,
        callee_analysis: FunctionReturnAnalysis,
    ) -> Tuple[Any, ...]:
        accepted = []
        for item in getattr(callee_analysis, "completed_recovery_proof_evidence", ()) or ():
            if not isinstance(item, Mapping):
                continue
            proof_id = cls._validated_summary_completion_proof_id(item)
            if proof_id is not None:
                accepted.append(proof_id)
        return tuple(accepted)

    @classmethod
    def _validated_summary_completion_proof_id(
        cls,
        evidence: Mapping[str, Any],
    ) -> Optional[Tuple[Any, ...]]:
        proof_id = _return_region_summary_proof_id_from_evidence(evidence)
        if proof_id is not None:
            return cls._normalize_nested_tuple(proof_id)
        proof_id = summary_return_acceptance_proof_id_from_evidence(evidence)
        if proof_id is not None:
            return cls._normalize_nested_tuple(proof_id)
        return None

    @staticmethod
    def _normalize_nested_tuple(value: Any) -> Any:
        if isinstance(value, list):
            return tuple(BoundedCallRefiner._normalize_nested_tuple(item) for item in value)
        if isinstance(value, tuple):
            return tuple(BoundedCallRefiner._normalize_nested_tuple(item) for item in value)
        return value

    @staticmethod
    def _stable_key_or_none(value: Any) -> Optional[Tuple[Any, ...]]:
        stable_key = getattr(value, "stable_key", None)
        if callable(stable_key):
            try:
                key = stable_key()
            except (AttributeError, TypeError, ValueError, RecursionError):
                return None
            return key if isinstance(key, tuple) else None
        return None

    def _deferred_call_pcode_key(self, deferred: DeferredCallInfo) -> Optional[Tuple[Any, ...]]:
        deferred_ref = getattr(deferred, "deferred_call_ref", None)
        return self._stable_key_or_none(getattr(deferred_ref, "pcode_op_ref", None))

    def _call_target_key_for_analysis(
        self,
        target_ref: Any,
        analysis: Optional[FunctionReturnAnalysis],
    ) -> Any:
        key = self._stable_key_or_none(target_ref)
        binary_id = getattr(analysis, "binary_id", None) if analysis is not None else None
        if not binary_id or not isinstance(key, tuple) or not key:
            return key
        kind = key[0]
        if kind == "function" and len(key) >= 3 and key[2] is not None:
            return ("function", str(binary_id), key[2])
        if kind == "code_address" and len(key) >= 3 and key[2] is not None:
            return ("code_address", str(binary_id), key[2])
        if kind == "unknown":
            return ("unknown", str(binary_id))
        return key

    def _analysis_entry_key(self, analysis: Optional[FunctionReturnAnalysis]) -> Tuple[Any, ...]:
        if analysis is None:
            return ("analysis", None, None, None)
        function_ref_key = self._stable_key_or_none(getattr(analysis, "function_ref", None))
        if function_ref_key is not None:
            binary_id = getattr(analysis, "binary_id", None)
            if binary_id and function_ref_key[0] == "function" and len(function_ref_key) >= 3:
                return ("function", str(binary_id), function_ref_key[2])
            return function_ref_key
        return (
            "analysis",
            getattr(analysis, "binary_id", None),
            getattr(analysis, "function_name", None),
            getattr(analysis, "entry_point", None),
        )

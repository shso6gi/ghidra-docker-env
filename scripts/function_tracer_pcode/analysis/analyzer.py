# -*- coding: utf-8 -*-
"""Return解析メインモジュール（符号性検出統合版）"""

import re
from dataclasses import dataclass
from contextlib import contextmanager
from functools import cmp_to_key
from typing import Iterable, List, Dict, Optional, Any, Set, Tuple, Sequence, cast

from ..model.expression import Expression, ExpressionType, Condition
from ..model.call_target import CallTargetRef, coerce_call_target_ref
from ..model.structural import StructuralKey, expression_key_safe
from ..model.storage import StorageInfo
from ..model.analysis import (
    ComparisonSurface,
    DeferredCallInfo,
    ReturnInfo,
    FunctionReturnAnalysis,
    SignednessResult,
)
from ..model.runtime_refs import (
    AddressValueRef,
    DeferredCallRef,
    PcodeOpRef,
    PostStateValueRef,
    ReadonlyReductionRef,
    UnknownValueRef,
)
from ..model.signature import (
    get_declared_type_signedness,
    is_void_data_type,
)
from ..config.settings import (
    BOUNDED_CALL_MAX_CASES,
    BOUNDED_CALL_REFINEMENT_ENABLED,
    BOUNDED_CALL_UNROLL_LIMIT,
)
from . import PcodeTracer
from .bounded_refinement import BoundedCallRefiner
from .condition import ConditionTracker, ConditionSimplifier, ConditionNormalizer
from .condition.bitvector import eval_constant_raw
from .debug import summarize_expression
from .signedness import SignednessDetector
from .effect_summary import (
    CanonicalLocation,
    EffectSummary,
    _build_parameter_replacements,
    _expression_location_ref,
    _expression_reads_location,
    _enumerate_constant_expression_branches,
    _expression_contains_observed_loads,
    _iter_expression_nodes,
    _materialize_existing_effect_value_carrier,
    _strip_materialized_post_state_value_refs,
    _expressions_equivalent,
    _expressions_equivalent_under_conditions,
    _find_matching_effect_value,
    _find_unique_effect_location_for_value,
    _resolve_call_argument_expression,
    _resolve_call_target_ref,
    _reduce_expression_under_conditions,
    _replay_definite_active_effects_for_location,
    canonicalize_expr_read_location,
    expression_contains_post_state_reads,
    expression_matches_stale_post_state_replay,
    lower_post_state_expression_for_smt,
    materialize_definite_post_state_expression,
    normalize_post_state_expression,
    locations_match,
    promote_effect_value_carrier_to_post_state_read,
    promote_effect_value_match_to_post_state_read,
    promote_observed_loads_to_post_state_reads,
    resolve_definite_post_state_read_for_location,
    resolve_call_targets,
    rewrite_loads_from_effects,
    rewrite_observed_loads_from_effects,
    summarize_store_effects,
    substitute_condition,
    substitute_expression,
)
from .memory_resolver import concretize_readonly_loads
from .recurrence_summary import StructuralRecurrenceSummarizer
from .switch import build_switch_dispatch_summaries


_PCODE_OPCODE_BY_MNEMONIC = {
    "COPY": 1,
    "LOAD": 2,
    "STORE": 3,
    "BRANCH": 4,
    "CBRANCH": 5,
    "BRANCHIND": 6,
    "CALL": 7,
    "CALLIND": 8,
    "RETURN": 10,
    "INT_ZEXT": 17,
    "INT_SEXT": 18,
    "MULTIEQUAL": 60,
    "INDIRECT": 61,
    "PIECE": 62,
    "SUBPIECE": 63,
    "CAST": 64,
}

_PCODE_CALL_OPCODES = {
    _PCODE_OPCODE_BY_MNEMONIC["CALL"],
    _PCODE_OPCODE_BY_MNEMONIC["CALLIND"],
}

_PCODE_BRANCHLIKE_OPCODES = {
    _PCODE_OPCODE_BY_MNEMONIC["BRANCH"],
    _PCODE_OPCODE_BY_MNEMONIC["CBRANCH"],
    _PCODE_OPCODE_BY_MNEMONIC["BRANCHIND"],
}

_PCODE_VALUE_PASSTHROUGH_OPCODES = {
    _PCODE_OPCODE_BY_MNEMONIC["COPY"],
    _PCODE_OPCODE_BY_MNEMONIC["CAST"],
    _PCODE_OPCODE_BY_MNEMONIC["INT_ZEXT"],
    _PCODE_OPCODE_BY_MNEMONIC["INT_SEXT"],
    _PCODE_OPCODE_BY_MNEMONIC["SUBPIECE"],
}

_UNSIGNED_COMPARE_TO_SIGNED = {
    "INT_LESS": "INT_SLESS",
    "INT_LESSEQUAL": "INT_SLESSEQUAL",
}

_SIGNED_COMPARE_TO_UNSIGNED = {
    "INT_SLESS": "INT_LESS",
    "INT_SLESSEQUAL": "INT_LESSEQUAL",
}


@dataclass
class _TrackedReturnValue:
    """RETURN provenance の逆追跡対象。"""

    varnode: Optional[Any] = None
    storage: Optional[StorageInfo] = None
    producer_op: Optional[Any] = None


@dataclass(frozen=True)
class _EffectRewritePrecision:
    matched_effect_locations: int
    post_state_reads: int
    object_centric_unknowns: int
    opaque_unknowns: int
    downstream_unresolved_values: int
    observed_loads: int
    phi_nodes: int


class ReturnAnalyzer:
    """関数のReturn値を解析"""

    def __init__(self, program, debug: bool = False):
        self.program = program
        self.debug = debug
        self._decompiler = None
        self._current_parameters: List[Dict] = []
        self._current_effect_summary: Optional[EffectSummary] = None
        self._effect_summary_cache: Dict[Tuple[Any, ...], Any] = {}
        self._effect_summary_parameter_cache: Dict[Tuple[Any, ...], List[Dict]] = {}
        self._call_analysis_cache: Dict[Tuple[Any, ...], Optional[FunctionReturnAnalysis]] = {}
        self._local_target_cache: Dict[Tuple[object, ...], Optional[List[Any]]] = {}
        self._current_deferred_calls: Dict[Tuple[Any, ...], DeferredCallInfo] = {}
        self._deferred_call_counter: int = 0
        self._analysis_in_progress: Dict[Tuple[Any, ...], FunctionReturnAnalysis] = {}
        self._return_path_entry_cache: Dict[Tuple[Any, ...], Optional[List[Tuple[List[Any], List[Condition]]]]] = {}
        self._current_blocked_return_path_conditions: List[List[Condition]] = []
        self._bounded_call_refinement_enabled = bool(BOUNDED_CALL_REFINEMENT_ENABLED)
        self._bounded_call_unroll_limit = int(BOUNDED_CALL_UNROLL_LIMIT)
        self._bounded_call_max_cases = int(BOUNDED_CALL_MAX_CASES)
        self._last_function_lookup_error: Optional[str] = None
        self._current_function_prototype = None
    
    def _debug_print(self, msg: str, indent: int = 0):
        if self.debug:
            prefix = "  " * indent
            print(f"{prefix}[ReturnAnalyzer] {msg}")

    def _program_is_big_endian(self) -> Optional[bool]:
        language_getter = getattr(self.program, "getLanguage", None)
        if not callable(language_getter):
            return None
        try:
            language = language_getter()
            is_big_endian = getattr(language, "isBigEndian", None)
            if callable(is_big_endian):
                return bool(is_big_endian())
        except Exception:
            return None
        return None

    def _debug_expr_summary(self, expr: Optional[Expression], max_depth: int = 4) -> str:
        return summarize_expression(expr, max_depth=max_depth)

    def _debug_expr_identity_summary(
        self,
        expr: Optional[Expression],
        max_depth: int = 3,
    ) -> str:
        if expr is None:
            return "None"

        runtime_ref = getattr(expr, "runtime_ref", None)
        read_order_key = getattr(expr, "read_order_key", None)
        runtime_tag = type(runtime_ref).__name__ if runtime_ref is not None else "None"
        try:
            structural_key = expression_key_safe(
                expr,
                include_memory_read_order=True,
            )
        except Exception:
            structural_key = None
        return (
            f"{summarize_expression(expr, max_depth=max_depth)} "
            f"[type={expr.expr_type.name}, size={expr.size}, "
            f"read_order={read_order_key}, runtime_ref={runtime_tag}:{runtime_ref}, "
            f"structural={structural_key}]"
        )

    def _coerce_optional_int(self, value: object) -> Optional[int]:
        if value is None or isinstance(value, bool):
            return None
        if isinstance(value, int):
            return value
        try:
            return int(cast(Any, value))
        except Exception:
            return None

    def _describe_pcode_site(
        self,
        pcode_op,
        fallback_address: Optional[str] = None,
        *,
        identity_prefix: Optional[str] = None,
    ) -> Dict[str, Optional[object]]:
        address = fallback_address or "unknown"
        pcode_identity: Optional[str] = None
        pcode_order: Optional[int] = None
        pcode_time: Optional[int] = None

        seq = getattr(pcode_op, "getSeqnum", lambda: None)() if pcode_op is not None else None
        if seq is not None:
            try:
                target = seq.getTarget()
                if target is not None:
                    address = str(target)
            except Exception:
                target = None
            pcode_order = self._coerce_optional_int(getattr(seq, "getOrder", lambda: None)())
            pcode_time = self._coerce_optional_int(getattr(seq, "getTime", lambda: None)())

            if pcode_time is not None:
                pcode_identity = f"{address}:t{pcode_time}"
            elif pcode_order is not None:
                pcode_identity = f"{address}:o{pcode_order}"
            elif address:
                pcode_identity = address
        elif identity_prefix:
            pcode_identity = f"{identity_prefix}:{address}"

        return {
            "address": address,
            "pcode_identity": pcode_identity,
            "pcode_order": pcode_order,
            "pcode_time": pcode_time,
        }

    def _pcode_op_identity_key(self, pcode_op) -> Optional[Tuple[Any, ...]]:
        if pcode_op is None:
            return None

        site = self._describe_pcode_site(pcode_op)
        output = getattr(pcode_op, "getOutput", lambda: None)()
        output_key = self._varnode_location_key(output)
        if output_key is None and output is not None:
            output_key = ("id", id(output))

        mnemonic = None
        try:
            mnemonic = str(pcode_op.getMnemonic())
        except Exception:
            mnemonic = None

        identity = (
            site.get("address"),
            site.get("pcode_time"),
            site.get("pcode_order"),
            mnemonic,
            output_key,
        )
        if identity[0] is None and identity[1] is None and identity[2] is None and identity[3] is None:
            return None
        return identity

    def _pcode_ops_match(self, lhs, rhs) -> bool:
        if lhs is rhs:
            return True
        lhs_key = self._pcode_op_identity_key(lhs)
        rhs_key = self._pcode_op_identity_key(rhs)
        if lhs_key is None or rhs_key is None:
            return False
        return lhs_key == rhs_key

    def _return_site_key(self, ret_info: ReturnInfo) -> str:
        return ret_info.site_key()

    def _make_return_info(
        self,
        *,
        address: str,
        value: Expression,
        conditions: List[Condition],
        branch_index: Optional[int] = None,
        site_metadata: Optional[Dict[str, Optional[object]]] = None,
    ) -> ReturnInfo:
        site_metadata = site_metadata or {}
        return ReturnInfo(
            address=address,
            value=value,
            conditions=list(conditions or []),
            branch_index=branch_index,
            pcode_identity=cast(Optional[str], site_metadata.get("pcode_identity")),
            pcode_order=self._coerce_optional_int(site_metadata.get("pcode_order")),
            pcode_time=self._coerce_optional_int(site_metadata.get("pcode_time")),
        )

    def _expression_contains_equivalent_subexpr(
        self,
        expr: Optional[Expression],
        target: Optional[Expression],
    ) -> bool:
        if expr is None or target is None:
            return False
        if _expressions_equivalent(expr, target):
            return True
        for operand in getattr(expr, "operands", []) or []:
            if self._expression_contains_equivalent_subexpr(operand, target):
                return True
        if expr.expr_type == ExpressionType.PHI and expr.value:
            for cond, value in expr.value:
                if cond is not None and self._expression_contains_equivalent_subexpr(cond.expression, target):
                    return True
                if self._expression_contains_equivalent_subexpr(value, target):
                    return True
        return False

    @contextmanager
    def _analysis_context(
        self,
        parameters: List[Dict],
        effect_summary: Optional[EffectSummary],
        function_prototype=None,
    ):
        """Temporarily bind per-analysis state and restore the parent context on exit."""
        previous_parameters = self._current_parameters
        previous_effect_summary = self._current_effect_summary
        previous_deferred_calls = self._current_deferred_calls
        previous_function_prototype = self._current_function_prototype
        self._current_parameters = parameters
        self._current_effect_summary = effect_summary
        self._current_deferred_calls = {}
        self._current_function_prototype = function_prototype
        try:
            yield
        finally:
            self._current_parameters = previous_parameters
            self._current_effect_summary = previous_effect_summary
            self._current_deferred_calls = previous_deferred_calls
            self._current_function_prototype = previous_function_prototype
    
    def _get_decompiler(self):
        if self._decompiler is None:
            from ghidra.app.decompiler import DecompInterface # type: ignore[import]
            self._decompiler = DecompInterface()
            self._decompiler.openProgram(self.program)
        return self._decompiler

    @contextmanager
    def _program_transaction(self, description: str):
        start_transaction = getattr(self.program, "startTransaction", None)
        end_transaction = getattr(self.program, "endTransaction", None)
        if not callable(start_transaction) or not callable(end_transaction):
            yield
            return

        tx_id = start_transaction(description)
        try:
            yield
            end_transaction(tx_id, True)
        except Exception:
            end_transaction(tx_id, False)
            raise
    
    def dispose(self):
        if self._decompiler is not None:
            try:
                self._decompiler.dispose()
            except Exception as exc:
                exc_text = str(exc).lower()
                if "jvm is not running" not in exc_text and "java virtual machine is not running" not in exc_text:
                    raise
            finally:
                self._decompiler = None
    
    def _dump_return_infos(self, analysis: FunctionReturnAnalysis):
        """
        ReturnInfo一覧をダンプ（デバッグ用）
        
        各ReturnInfoについて以下を出力：
        - branch_index（分岐識別子）
        - address（アドレス）
        - value（式の文字列表現とSMT表現）
        - conditions（簡約後の条件リスト）
        """
        if not self.debug:
            return
        
        self._debug_print("=" * 60)
        self._debug_print(f"ReturnInfo dump for {analysis.function_name}")
        self._debug_print(f"Total return candidates: {len(analysis.returns)}")
        if analysis.analysis_notes:
            self._debug_print(f"Analysis notes: {analysis.analysis_notes}")
        self._debug_print("=" * 60)
        
        for i, ret_info in enumerate(analysis.returns):
            self._debug_print(f"[{i}] branch_index={ret_info.branch_index}")
            self._debug_print(f"    address: {ret_info.address}", 1)
            if ret_info.pcode_identity is not None:
                self._debug_print(f"    pcode_identity: {ret_info.pcode_identity}", 1)
            if ret_info.pcode_time is not None or ret_info.pcode_order is not None:
                self._debug_print(
                    f"    seq(time={ret_info.pcode_time}, order={ret_info.pcode_order})",
                    1,
                )
            
            # 値の文字列表現
            try:
                value_str = self._debug_expr_summary(ret_info.value)
                self._debug_print(f"    value: {value_str}", 1)
            except Exception as e:
                self._debug_print(f"    value: (error converting to string: {e})", 1)
            
            # SMT表現（エラー時はスキップ）- 引数なし
            try:
                smt_str = ret_info.value.to_smt()
                # 長すぎる場合は切り詰め
                if len(smt_str) > 300:
                    smt_str = smt_str[:300] + "..."
                self._debug_print(f"    smt: {smt_str}", 1)
            except Exception as e:
                self._debug_print(f"    smt: (error: {e})", 1)
            
            # 条件リスト（簡約版）
            if ret_info.conditions:
                try:
                    cond_strs = [ConditionSimplifier.get_simplified_condition_string(c) 
                                for c in ret_info.conditions]
                    self._debug_print(f"    conditions({len(ret_info.conditions)}): {cond_strs}", 1)
                except Exception as e:
                    self._debug_print(f"    conditions: (error: {e})", 1)
            else:
                self._debug_print(f"    conditions: (unconditional/always)", 1)
        
        self._debug_print("=" * 60)
        
        # 条件カバレッジの簡易チェック
        self._check_condition_coverage(analysis)
    
    def _check_condition_coverage(self, analysis: FunctionReturnAnalysis):
        """
        条件カバレッジの簡易チェック
        
        各パラメータについて、正・負・ゼロのケースが存在するかをヒューリスティックに確認
        """
        if not self.debug or not analysis.returns:
            return
        
        self._debug_print("Condition coverage check:")
        
        # パラメータ名を収集
        param_names = [p.get('name', f'param_{i}') for i, p in enumerate(analysis.parameters)]
        
        if not param_names:
            return
        
        # 各パラメータについて、どのような条件が存在するか確認
        for param_name in param_names:
            has_zero_check = False
            has_positive_check = False
            has_negative_check = False
            param_referenced = False
            
            for ret_info in analysis.returns:
                for cond in ret_info.conditions:
                    if not self._condition_mentions_param(cond, param_name):
                        continue
                    param_referenced = True
                    is_zero, is_pos, is_neg = self._classify_param_condition(cond, param_name)
                    has_zero_check = has_zero_check or is_zero
                    has_positive_check = has_positive_check or is_pos
                    has_negative_check = has_negative_check or is_neg
                    
            if not param_referenced:
                self._debug_print(f"  {param_name}: not referenced in conditions")
                continue
            
            coverage_info = []
            if has_zero_check:
                coverage_info.append("zero")
            if has_positive_check:
                coverage_info.append("positive")
            if has_negative_check:
                coverage_info.append("negative")
            
            if coverage_info:
                self._debug_print(f"  {param_name}: {', '.join(coverage_info)} checks found", 1)
            else:
                self._debug_print(f"  {param_name}: no explicit checks", 1)

    def _condition_mentions_param(self, condition: Condition, param_name: str) -> bool:
        """条件が指定パラメータ変数を参照するか判定（to_string 非依存）。"""
        expression = condition.expression
        if expression is None:
            return False
        try:
            return param_name in expression.get_all_variables()
        except Exception:
            return False

    def _expression_is_zero_constant(self, expr: Optional[Expression]) -> bool:
        """式が 0 定数、または同値なゼロ表現か判定（to_string 非依存）。"""
        if expr is None:
            return False
        if expr.expr_type == ExpressionType.CONSTANT:
            try:
                return int(expr.value) == 0
            except Exception:
                return False
        if expr.expr_type == ExpressionType.LITERAL:
            try:
                return int(expr.value) == 0
            except Exception:
                return False
        if expr.expr_type == ExpressionType.UNARY_OP and expr.operator in {"INT_2COMP", "INT_NEGATE"}:
            if not expr.operands:
                return False
            return self._expression_is_zero_constant(expr.operands[0])
        return False

    @staticmethod
    def _expression_has_param(expr: Optional[Expression], param_name: str) -> bool:
        """式の内部に指定パラメータが含まれるかを判定。"""
        if expr is None:
            return False
        try:
            return param_name in expr.get_all_variables()
        except Exception:
            return False

    def _decompose_comparison_condition(
        self,
        condition: Condition,
    ) -> Optional[Tuple[bool, str, Expression, Expression]]:
        """条件を比較式 `(negated, op, left, right)` に展開。"""
        expr = condition.expression
        negated = bool(condition.negated)
        while expr is not None and expr.expr_type == ExpressionType.UNARY_OP:
            if expr.operator == "BOOL_NEGATE":
                negated = not negated
                expr = expr.operands[0] if expr.operands else None
                continue
            break
        if expr is None or expr.expr_type != ExpressionType.BINARY_OP or len(expr.operands) < 2:
            return None
        return (
            negated,
            expr.operator or "",
            expr.operands[0],
            expr.operands[1],
        )

    def _classify_param_condition(
        self,
        condition: Condition,
        param_name: str,
    ) -> Tuple[bool, bool, bool]:
        """
        条件を零・正・負チェックへ分類（display 文字列不使用）。
        
        戻り値: (has_zero_check, has_positive_check, has_negative_check)
        """
        decompose = self._decompose_comparison_condition(condition)
        if decompose is None:
            return False, False, False

        negated, op, left, right = decompose
        has_pos = False
        has_neg = False
        has_zero = False

        left_param = self._expression_has_param(left, param_name)
        right_param = self._expression_has_param(right, param_name)
        left_zero = self._expression_is_zero_constant(left)
        right_zero = self._expression_is_zero_constant(right)

        if op in {"INT_EQUAL", "INT_NOTEQUAL"}:
            if (left_zero and right_param) or (right_zero and left_param):
                has_zero = True
            return has_zero, has_pos, has_neg

        if not (
            (left_param and right_zero) or (right_param and left_zero)
        ):
            return has_zero, has_pos, has_neg

        relation_positive_on_zero = op in {"INT_LESSEQUAL", "INT_SLESSEQUAL", "INT_LESS", "INT_SLESS"}
        if not relation_positive_on_zero:
            return has_zero, has_pos, has_neg

        # op が param < 0 系の場合
        if left_param and right_zero:
            if op in {"INT_LESS", "INT_SLESS"}:
                # param < 0
                has_neg = not negated
                has_pos = negated
            elif op in {"INT_LESSEQUAL", "INT_SLESSEQUAL"}:
                # param <= 0
                has_neg = not negated
                has_pos = False
        # op が 0 < param 系の場合
        elif left_zero and right_param:
            if op in {"INT_LESS", "INT_SLESS"}:
                # 0 < param
                has_pos = not negated
                has_neg = negated
            elif op in {"INT_LESSEQUAL", "INT_SLESSEQUAL"}:
                # 0 <= param
                has_pos = not negated
                has_neg = False

        if op in {"INT_NOTEQUAL"} and (left_zero and right_param or right_zero and left_param):
            has_zero = True

        return has_zero, has_pos, has_neg
    
    def analyze_function(
        self,
        function,
        timeout: int = 60,
        active_functions: Optional[Set[Tuple[Any, ...]]] = None,
        bound_parameter_values: Optional[Dict[int, Expression]] = None,
    ) -> Optional[FunctionReturnAnalysis]:
         # デバッグフラグを ConditionSimplifier に伝播
        from .condition import ConditionSimplifier
        ConditionSimplifier.DEBUG = self.debug
        ConditionSimplifier.reset_debug_state()
        
        current_function_ref = CallTargetRef.from_function(function)
        normalized_bound_parameter_values = self._normalize_bound_parameter_values(
            bound_parameter_values,
        )
        analysis_scope_key = self._analysis_scope_key(
            current_function_ref,
            normalized_bound_parameter_values,
        )
        cached_analysis = self._call_analysis_cache.get(analysis_scope_key)
        if cached_analysis is not None:
            return cached_analysis
        active_functions = self._extend_active_functions(
            active_functions,
            current_function_ref,
        )
        self._return_path_entry_cache = {}
        current_active_key = analysis_scope_key

        self._debug_print("=" * 60)
        self._debug_print(f"Analyzing function: {function.getName()}")
        self._debug_print("=" * 60)
        
        decompiler = self._get_decompiler()
        results = decompiler.decompileFunction(function, timeout, None)
        
        if not results.decompileCompleted():
            self._debug_print("Decompilation failed!")
            return None
        
        high_function = results.getHighFunction()
        if high_function is None:
            self._debug_print("HighFunction is None!")
            return None
        
        # Step 1: tracer / CFG infrastructure を先に構築する。
        # implicit passthrough parameter recovery でも CALLIND target を追跡するため、
        # PhiHandler が有効な状態で tracer を使えるようにしておく。
        tracer = self._make_tracer(
            high_function,
            bound_parameter_values=normalized_bound_parameter_values,
        )
        tracer.record_deferred_call = self._make_deferred_call_recorder(function)
        condition_tracker = ConditionTracker(tracer)
        tracer.condition_tracker = condition_tracker
        from .phi_resolver import PhiHandler

        phi_handler = PhiHandler(tracer, condition_tracker)
        tracer.phi_handler = phi_handler
        condition_tracker.build()

        parameters = self._collect_parameters(high_function)
        parameters = self._augment_parameters_with_implicit_passthrough(
            parameters,
            tracer,
            active_functions,
        )
        function_prototype = None
        try:
            function_prototype = high_function.getFunctionPrototype()
        except Exception:
            function_prototype = None

        with self._analysis_context(parameters, None, function_prototype=function_prototype):
            self._debug_print(f"Parameters: {[p['name'] for p in parameters]}")
            image_base = None
            try:
                image_base = self.program.getImageBase().getOffset()
            except Exception:
                image_base = None
            condition_tracker.refine_branch_conditions(
                call_resolver=self._make_call_resolver(active_functions, function),
                parameters=parameters,
                resolve_callee_parameters=self._get_freshest_callee_parameters,
                read_memory_value=self._read_memory_value,
                image_base=image_base,
            )

            # 戻り値の型を取得
            return_type_obj, return_type = self._get_return_type_info(high_function)
            self._debug_print(f"Return type: {return_type}")

            # === Phase 1: 符号性検出 ===
            signedness_result = self._detect_signedness(high_function)
            if signedness_result:
                self._debug_print(f"Inferred signedness: {signedness_result.signedness}")
                if self.debug:
                    self._debug_print(f"Evidence summary: {signedness_result.evidence_summary}")
                    self._debug_print(f"Opcode counts: {signedness_result.opcode_counts}")

            return_ops = tracer.find_return_ops()
            self._debug_print(f"Found {len(return_ops)} RETURN operations")

            empty_effect_summary = self._make_empty_effect_summary(parameters)
            recovered_control_returns, control_region_notes = self._recover_control_region_returns_early(
                function,
                tracer,
                condition_tracker,
                return_ops,
                active_functions=active_functions,
            )

            effect_summary = empty_effect_summary
            if recovered_control_returns is not None:
                self._current_effect_summary = empty_effect_summary
                return_infos = list(recovered_control_returns)
            else:
                effect_summary = self._invoke_build_effect_summary(
                    function,
                    high_function,
                    tracer,
                    condition_tracker,
                    parameters,
                    active_functions=active_functions,
                    bound_parameter_values=normalized_bound_parameter_values,
                )
                self._current_effect_summary = effect_summary

                pre_return_structural_result = self._try_pre_return_counted_loop_summary(
                    function=function,
                    high_function=high_function,
                    tracer=tracer,
                    parameters=parameters,
                    return_ops=return_ops,
                    current_function_ref=current_function_ref,
                    analysis_scope_key=analysis_scope_key,
                    return_type=return_type,
                    return_type_obj=return_type_obj,
                    signedness_result=signedness_result,
                    effect_summary=effect_summary,
                )
                if pre_return_structural_result is not None:
                    self._call_analysis_cache[analysis_scope_key] = pre_return_structural_result
                    function_cache_key = self._function_cache_key(function)
                    if function_cache_key is not None and not normalized_bound_parameter_values:
                        self._call_analysis_cache[function_cache_key] = pre_return_structural_result
                    return pre_return_structural_result

                return_infos = []
                for i, return_op in enumerate(return_ops):
                    self._debug_print(f"--- Analyzing RETURN #{i + 1} ---")
                    infos = self._analyze_return_op(
                        return_op,
                        tracer,
                        condition_tracker,
                        i,
                        current_function=function,
                        active_functions=active_functions,
                    )
                    return_infos.extend(infos)

            result = FunctionReturnAnalysis(
                function_name=function.getName(),
                entry_point=str(function.getEntryPoint()),
                parameters=parameters,
                returns=return_infos,
                function_ref=current_function_ref,
                analysis_scope_key=analysis_scope_key,
                return_type=return_type,
                return_type_obj=return_type_obj,
                signedness_result=signedness_result,
                deferred_calls=dict(self._current_deferred_calls),
                effect_summary=effect_summary,
                program_is_big_endian=self._program_is_big_endian(),
            )
            result.unknown_event_count = len(tracer.unknown_tracker.events)
            result.unknown_event_reasons = sorted(
                {
                    getattr(event, "reason_str", None) or getattr(event.reason, "value", "unknown")
                    for event in tracer.unknown_tracker.events
                }
            )

            for note in control_region_notes:
                if note not in result.analysis_notes:
                    result.analysis_notes.append(note)

            if recovered_control_returns is None:
                if (
                    return_type_obj is not None
                    and self._is_void_type(return_type_obj)
                    and effect_summary.synthetic_expr is not None
                    and not effect_summary.has_unsupported_call
                ):
                    result.returns = [
                        self._make_return_info(
                            address=str(function.getEntryPoint()),
                            conditions=[],
                            branch_index=0,
                            value=effect_summary.synthetic_expr,
                        )
                    ]
                    result.comparison_surface = ComparisonSurface(
                        kind="memory_effect",
                        explicit_bit_width=max(1, effect_summary.synthetic_expr.get_bit_width()),
                        use_sign_extension=False,
                        evidence={
                            "source": "effect_summary.synthetic_expr",
                            "effect_count": len(getattr(effect_summary, "effects", []) or []),
                        },
                    )

                recovered_returns = self._recover_call_wrapper_returns(
                    results,
                    result,
                    function,
                    tracer,
                    condition_tracker,
                    return_ops,
                    active_functions,
                )
                if recovered_returns is not None:
                    result.returns = recovered_returns
                    result.analysis_notes.append("call_wrapper_return_recovery")

                recovered_switch_returns = self._recover_switch_like_returns_from_pcode(
                    result,
                    tracer,
                    condition_tracker,
                    return_ops=return_ops,
                    current_function=function,
                    active_functions=active_functions,
                )
                if recovered_switch_returns is not None:
                    result.returns = recovered_switch_returns
                    if "switch_return_recovery" not in result.analysis_notes:
                        result.analysis_notes.append("switch_return_recovery")

            result.deferred_calls = dict(self._current_deferred_calls)
            self._apply_effect_call_argument_evidence_to_deferred_calls(result)

            if current_active_key is not None:
                self._analysis_in_progress[current_active_key] = result
            try:
                self._apply_bounded_call_refinement(
                    result,
                    active_functions,
                    CallTargetRef.from_function(function),
                )
            finally:
                if current_active_key is not None:
                    self._analysis_in_progress.pop(current_active_key, None)

            self._synchronize_parameters_with_referenced_parameter_expressions(result)
            self._repair_mixed_scalar_signedness(result)
            self._normalize_return_partition(result)
            self._mark_incomplete_control_flow(result)

            summary = self._apply_structural_recurrence_summary(
                function,
                high_function,
                result,
                tracer,
            )
            if summary is not None:
                result.returns = summary[0]
                if summary[1] not in result.analysis_notes:
                    result.analysis_notes.append(summary[1])
                self._normalize_return_partition(result)
                self._mark_incomplete_control_flow(result)
                if result.deferred_calls:
                    if current_active_key is not None:
                        self._analysis_in_progress[current_active_key] = result
                    try:
                        self._apply_bounded_call_refinement(
                            result,
                            active_functions,
                            CallTargetRef.from_function(function),
                        )
                    finally:
                        if current_active_key is not None:
                            self._analysis_in_progress.pop(current_active_key, None)
                    self._normalize_return_partition(result)
                    self._mark_incomplete_control_flow(result)
            if (
                result.has_symbolic_post_state_reads()
                and "symbolic_post_state_reads" not in result.analysis_notes
            ):
                result.analysis_notes.append("symbolic_post_state_reads")

            # デバッグダンプ（解析結果の可視化）
            self._dump_return_infos(result)

            # Unknown発生サマリー
            if self.debug:
                print("\n" + "=" * 70)
                print("UNKNOWN EVENTS SUMMARY")
                print("=" * 70)
                print(tracer.unknown_tracker.get_summary())
                phi_events = tracer.unknown_tracker.filter_phi_related()
                if phi_events:
                    print("\n--- PHI-related events ---")
                    for event in phi_events:
                        print(event.format_detail(indent=0))
            elif len(tracer.unknown_tracker.events) > 0:
                print(f"\n[Info] {len(tracer.unknown_tracker.events)} unknown events occurred")
                print(f"  Use --debug flag for detailed report")

            self._call_analysis_cache[analysis_scope_key] = result
            function_cache_key = self._function_cache_key(function)
            if function_cache_key is not None and not normalized_bound_parameter_values:
                self._call_analysis_cache[function_cache_key] = result
            return result

    def _apply_structural_recurrence_summary(
        self,
        function,
        high_function,
        analysis: FunctionReturnAnalysis,
        tracer: PcodeTracer,
    ) -> Optional[Tuple[List[ReturnInfo], str]]:
        if analysis is None or not analysis.returns:
            return None

        summarizer = StructuralRecurrenceSummarizer(tracer, debug=self.debug)
        should_try = analysis.has_unresolved_return_value() or any(
            reason in {"call_out_of_scope", "max_depth_exceeded", "phi_no_valid_branch", "phi_circular"}
            for reason in getattr(analysis, "unknown_event_reasons", [])
        )
        if not should_try:
            should_try = summarizer.has_summary_candidate(function, high_function, analysis)
        if not should_try:
            return None

        return summarizer.try_summarize_function(function, high_function, analysis)

    def _try_pre_return_counted_loop_summary(
        self,
        *,
        function,
        high_function,
        tracer: PcodeTracer,
        parameters: Sequence[Dict],
        return_ops: Sequence,
        current_function_ref: CallTargetRef,
        analysis_scope_key,
        return_type: Optional[str],
        return_type_obj,
        signedness_result: Optional[SignednessResult],
        effect_summary: EffectSummary,
    ) -> Optional[FunctionReturnAnalysis]:
        if not self._effect_summary_allows_pre_return_structural_summary(effect_summary):
            return None

        anchor = self._make_pre_return_summary_anchor(function, return_ops)
        skeleton = FunctionReturnAnalysis(
            function_name=function.getName(),
            entry_point=str(function.getEntryPoint()),
            parameters=list(parameters or []),
            returns=[anchor],
            function_ref=current_function_ref,
            analysis_scope_key=analysis_scope_key,
            return_type=return_type,
            return_type_obj=return_type_obj,
            signedness_result=signedness_result,
            deferred_calls=dict(self._current_deferred_calls),
            effect_summary=effect_summary,
            program_is_big_endian=self._program_is_big_endian(),
        )
        summarizer = StructuralRecurrenceSummarizer(tracer, debug=self.debug)
        summary = summarizer.try_summarize_pre_return_counted_scalar_loop(
            function,
            high_function,
            skeleton,
            return_ops,
        )
        if summary is None:
            return None

        summary_returns, summary_note = summary
        result = FunctionReturnAnalysis(
            function_name=function.getName(),
            entry_point=str(function.getEntryPoint()),
            parameters=list(parameters or []),
            returns=list(summary_returns),
            function_ref=current_function_ref,
            analysis_scope_key=analysis_scope_key,
            return_type=return_type,
            return_type_obj=return_type_obj,
            signedness_result=signedness_result,
            deferred_calls=dict(self._current_deferred_calls),
            effect_summary=effect_summary,
            program_is_big_endian=self._program_is_big_endian(),
        )
        if summary_note not in result.analysis_notes:
            result.analysis_notes.append(summary_note)
        if "pre_return_counted_loop_summary" not in result.analysis_notes:
            result.analysis_notes.append("pre_return_counted_loop_summary")
        result.unknown_event_count = len(tracer.unknown_tracker.events)
        result.unknown_event_reasons = sorted(
            {
                getattr(event, "reason_str", None) or getattr(event.reason, "value", "unknown")
                for event in tracer.unknown_tracker.events
            }
        )
        self._synchronize_parameters_with_referenced_parameter_expressions(result)
        self._repair_mixed_scalar_signedness(result)
        self._normalize_return_partition(result)
        self._mark_incomplete_control_flow(result)
        self._dump_return_infos(result)
        return result

    def _make_pre_return_summary_anchor(
        self,
        function,
        return_ops: Sequence,
    ) -> ReturnInfo:
        return_op = next(iter(return_ops or []), None)
        seqnum = getattr(return_op, "getSeqnum", lambda: None)() if return_op is not None else None
        address = str(getattr(seqnum, "getTarget", lambda: function.getEntryPoint())())
        pcode_time = getattr(seqnum, "getTime", lambda: None)()
        pcode_order = getattr(seqnum, "getOrder", lambda: None)()
        return self._make_return_info(
            address=address,
            value=Expression.unknown("pre_return_counted_loop_candidate"),
            conditions=[],
            branch_index=20_000,
            site_metadata={
                "pcode_identity": (
                    f"{address}:t{pcode_time}:o{pcode_order}"
                    if pcode_time is not None and pcode_order is not None
                    else None
                ),
                "pcode_time": pcode_time,
                "pcode_order": pcode_order,
            },
        )

    def _effect_summary_allows_pre_return_structural_summary(
        self,
        effect_summary: Optional[EffectSummary],
    ) -> bool:
        if effect_summary is None:
            return False
        if getattr(effect_summary, "effects", None):
            self._debug_print("Declined pre-return counted loop summary: effect summary contains memory writes")
            return False
        if getattr(effect_summary, "has_unsupported_call", False):
            self._debug_print("Declined pre-return counted loop summary: effect summary contains unsupported call")
            return False
        return True

    def _normalize_return_partition(self, analysis: FunctionReturnAnalysis) -> None:
        if analysis is None:
            return
        analysis.returns = self._strip_stack_protector_only_conditions(analysis.returns)
        if "control_region_return_recovery" not in analysis.analysis_notes:
            analysis.returns = self._exclusivize_return_regions(analysis.returns)
        analysis.returns = self._merge_equivalent_return_infos(analysis.returns)

    def _strip_stack_protector_only_conditions(
        self,
        return_infos: List[ReturnInfo],
    ) -> List[ReturnInfo]:
        if not return_infos:
            return return_infos

        stripped_infos: List[ReturnInfo] = []
        changed = False

        for info in return_infos:
            if not info.conditions:
                stripped_infos.append(info)
                continue

            retained_conditions = [
                cond
                for cond in info.conditions
                if not self._condition_looks_like_stack_protector_guard(cond)
            ]
            if len(retained_conditions) == len(info.conditions):
                stripped_infos.append(info)
                continue

            changed = True
            if self.debug:
                removed_dump = [
                    ConditionSimplifier.get_simplified_condition_string(cond)
                    for cond in info.conditions
                    if cond not in retained_conditions
                ]
                self._debug_print(
                    "Dropped object-centric stack-protector guard conditions from "
                    f"return case: {removed_dump}"
                )

            stripped_infos.append(
                self._make_return_info(
                    address=info.address,
                    value=info.value,
                    conditions=retained_conditions,
                    branch_index=info.branch_index,
                    site_metadata={
                        "pcode_identity": info.pcode_identity,
                        "pcode_order": info.pcode_order,
                        "pcode_time": info.pcode_time,
                    },
                )
            )

        if not changed:
            return return_infos
        return stripped_infos

    def _synchronize_parameters_with_referenced_parameter_expressions(
        self,
        analysis: FunctionReturnAnalysis,
    ) -> None:
        parameters = [dict(param) for param in (analysis.parameters or [])]
        referenced = self._collect_referenced_parameter_descriptors(analysis.returns)
        changed = False

        for candidate in referenced:
            match_index = self._find_matching_parameter_descriptor_index(parameters, candidate)
            if match_index is None:
                parameters.append(candidate)
                changed = True
                continue

            merged = self._merge_parameter_descriptors(parameters[match_index], candidate)
            if merged != parameters[match_index]:
                parameters[match_index] = merged
                changed = True

        if not changed:
            return

        parameters.sort(key=lambda param: int(param.get("index", 1 << 20)))
        analysis.parameters = parameters
        self._current_parameters = parameters

    def _repair_mixed_scalar_signedness(
        self,
        analysis: FunctionReturnAnalysis,
    ) -> None:
        profiles = self._collect_scalar_signedness_profiles(analysis.returns)
        preferred: Dict[Tuple[StructuralKey, int], str] = {}
        for key, profile in profiles.items():
            signed_score = int(profile.get("signed", 0))
            unsigned_score = int(profile.get("unsigned", 0))
            if signed_score <= 0 or unsigned_score <= 0 or signed_score == unsigned_score:
                continue
            preferred[key] = "signed" if signed_score > unsigned_score else "unsigned"

        if not preferred:
            return

        repaired_returns: List[ReturnInfo] = []
        changed = False
        for info in analysis.returns or []:
            rewritten_value, value_changed = self._rewrite_expression_signedness(
                info.value,
                preferred,
            )
            rewritten_conditions: List[Condition] = []
            cond_changed = False
            for cond in info.conditions or []:
                rewritten_expr, expr_changed = self._rewrite_expression_signedness(
                    cond.expression,
                    preferred,
                )
                rewritten_conditions.append(Condition(rewritten_expr, cond.negated))
                cond_changed = cond_changed or expr_changed
            if value_changed or cond_changed:
                changed = True
                repaired_returns.append(
                    self._make_return_info(
                        address=info.address,
                        value=rewritten_value,
                        conditions=rewritten_conditions,
                        branch_index=info.branch_index,
                        site_metadata={
                            "pcode_identity": info.pcode_identity,
                            "pcode_order": info.pcode_order,
                            "pcode_time": info.pcode_time,
                        },
                    )
                )
            else:
                repaired_returns.append(info)

        if not changed:
            return

        analysis.returns = repaired_returns
        note = "object_centric_scalar_signedness_repair"
        if note not in analysis.analysis_notes:
            analysis.analysis_notes.append(note)

    def _collect_scalar_signedness_profiles(
        self,
        return_infos: List[ReturnInfo],
    ) -> Dict[Tuple[StructuralKey, int], Dict[str, int]]:
        profiles: Dict[Tuple[StructuralKey, int], Dict[str, int]] = {}

        def record_expr(expr: Optional[Expression]) -> None:
            if expr is None:
                return
            self._record_scalar_signedness_from_expression(expr, profiles)
            for operand in getattr(expr, "operands", []) or []:
                record_expr(operand)
            if expr.expr_type == ExpressionType.PHI and expr.value:
                for cond, value in expr.value:
                    if cond is not None:
                        record_expr(cond.expression)
                    record_expr(value)

        for info in return_infos or []:
            record_expr(info.value)
            for cond in info.conditions or []:
                record_expr(cond.expression)

        return profiles

    def _record_scalar_signedness_from_expression(
        self,
        expr: Expression,
        profiles: Dict[Tuple[StructuralKey, int], Dict[str, int]],
    ) -> None:
        if expr is None or expr.expr_type != ExpressionType.BINARY_OP:
            return
        if expr.operator not in set(_UNSIGNED_COMPARE_TO_SIGNED) | set(_SIGNED_COMPARE_TO_UNSIGNED):
            return

        fact = ConditionSimplifier.extract_scalar_constraint(Condition(expr, False))
        if fact is None:
            return

        profile = profiles.setdefault(fact.key, {"signed": 0, "unsigned": 0})
        if expr.operator in _SIGNED_COMPARE_TO_UNSIGNED:
            score = 2
            if fact.value is not None and int(fact.value) < 0:
                score += 2
            profile["signed"] += score
        else:
            profile["unsigned"] += 1

    def _rewrite_expression_signedness(
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
                    cond_expr, cond_changed = self._rewrite_expression_signedness(
                        cond.expression,
                        preferred,
                    )
                    rewritten_cond = Condition(cond_expr, cond.negated)
                    branch_changed = branch_changed or cond_changed
                rewritten_value, value_changed = self._rewrite_expression_signedness(
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
                rewritten_operand, child_changed = self._rewrite_expression_signedness(
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

    def _collect_referenced_parameter_descriptors(
        self,
        return_infos: List[ReturnInfo],
    ) -> List[Dict]:
        discovered: Dict[str, Dict] = {}

        for return_info in return_infos or []:
            self._collect_parameter_descriptors_from_expression(return_info.value, discovered)
            for condition in return_info.conditions or []:
                self._collect_parameter_descriptors_from_expression(
                    getattr(condition, "expression", None),
                    discovered,
                )

        descriptors = list(discovered.values())
        descriptors.sort(key=lambda param: int(param.get("index", 1 << 20)))
        return descriptors

    def _collect_parameter_descriptors_from_expression(
        self,
        expr: Optional[Expression],
        discovered: Dict[str, Dict],
    ) -> None:
        if expr is None:
            return

        if expr.expr_type == ExpressionType.PARAMETER:
            descriptor = self._parameter_descriptor_from_expression(expr)
            key = self._parameter_descriptor_key(descriptor)
            existing = discovered.get(key)
            discovered[key] = self._merge_parameter_descriptors(existing, descriptor)
            return

        if expr.expr_type in {
            ExpressionType.BINARY_OP,
            ExpressionType.UNARY_OP,
            ExpressionType.CALL,
            ExpressionType.INTRINSIC,
            ExpressionType.MEMORY,
        }:
            for operand in expr.operands or []:
                self._collect_parameter_descriptors_from_expression(operand, discovered)
            return

        if expr.expr_type == ExpressionType.PHI and expr.value:
            for branch_condition, branch_value in expr.value:
                if branch_condition is not None:
                    self._collect_parameter_descriptors_from_expression(
                        getattr(branch_condition, "expression", None),
                        discovered,
                    )
                self._collect_parameter_descriptors_from_expression(branch_value, discovered)

    def _parameter_descriptor_from_expression(self, expr: Expression) -> Dict:
        index_value = expr.value if isinstance(expr.value, int) and expr.value >= 0 else -1

        descriptor = {
            "name": expr.name or (f"param_{index_value + 1}" if index_value >= 0 else None),
            "index": index_value,
            "size": expr.size or 0,
            "data_type": expr.data_type,
            "is_signed": True,
            "implicit_passthrough": True,
        }
        if expr.storage_info is not None:
            descriptor["storage"] = expr.storage_info.to_dict()
        return descriptor

    def _parameter_descriptor_key(self, descriptor: Dict) -> str:
        name = descriptor.get("name")
        if name:
            return f"name:{name}"
        index = descriptor.get("index")
        if isinstance(index, int) and index >= 0:
            return f"index:{index}"

        storage = descriptor.get("storage")
        if storage:
            base_name = storage.get("base_register_name") or storage.get("register_name") or storage.get("space_name")
            offset = int(storage.get("bit_offset_in_base", storage.get("offset", 0)) or 0)
            size_bits = int(storage.get("size_bits") or (storage.get("size", 0) * 8) or 0)
            return f"storage:{base_name}:{offset}:{size_bits}"
        return f"anonymous:{id(descriptor)}"

    def _find_matching_parameter_descriptor_index(
        self,
        parameters: List[Dict],
        candidate: Dict,
    ) -> Optional[int]:
        candidate_name = candidate.get("name")
        if candidate_name:
            for index, param in enumerate(parameters):
                if param.get("name") == candidate_name:
                    return index

        candidate_index = candidate.get("index")
        if isinstance(candidate_index, int) and candidate_index >= 0:
            for index, param in enumerate(parameters):
                if int(param.get("index", -1)) == candidate_index:
                    return index

        candidate_storage = candidate.get("storage")
        if candidate_storage:
            for index, param in enumerate(parameters):
                if self._parameter_storages_match_for_passthrough(
                    param.get("storage"),
                    candidate_storage,
                ):
                    return index
        return None

    def _merge_parameter_descriptors(
        self,
        existing: Optional[Dict],
        candidate: Dict,
    ) -> Dict:
        if existing is None:
            return dict(candidate)

        merged = dict(existing)
        if not merged.get("name") and candidate.get("name"):
            merged["name"] = candidate.get("name")
        if int(merged.get("index", -1)) < 0 and int(candidate.get("index", -1)) >= 0:
            merged["index"] = candidate.get("index")
        if int(merged.get("size", 0) or 0) <= 0 and int(candidate.get("size", 0) or 0) > 0:
            merged["size"] = candidate.get("size")
        if not merged.get("data_type") and candidate.get("data_type"):
            merged["data_type"] = candidate.get("data_type")
        if not merged.get("storage") and candidate.get("storage"):
            merged["storage"] = candidate.get("storage")
        if candidate.get("implicit_passthrough"):
            merged["implicit_passthrough"] = True
        if "is_signed" not in merged and "is_signed" in candidate:
            merged["is_signed"] = candidate.get("is_signed")
        return merged

    def _condition_looks_like_stack_protector_guard(self, condition: Condition) -> bool:
        compared = self._extract_stack_protector_compare_pair(condition)
        if compared is None:
            return False
        left, right = compared
        return self._reads_share_stack_protector_probe(left, right)

    def _extract_stack_protector_compare_pair(
        self,
        condition: Optional[Condition],
    ) -> Optional[Tuple[Expression, Expression]]:
        if condition is None:
            return None

        decomposed = self._decompose_comparison_condition(condition)
        if decomposed is None:
            return None

        _negated, operator, left, right = decomposed
        if operator in {"INT_NOTEQUAL", "INT_EQUAL"}:
            if self._is_zero_constant(right):
                pair = self._extract_difference_pair(left)
                if pair is not None:
                    return pair
            if self._is_zero_constant(left):
                pair = self._extract_difference_pair(right)
                if pair is not None:
                    return pair
            return left, right
        return None

    def _extract_difference_pair(
        self,
        expr: Optional[Expression],
    ) -> Optional[Tuple[Expression, Expression]]:
        if expr is None or expr.expr_type != ExpressionType.BINARY_OP or len(expr.operands) != 2:
            return None
        if expr.operator != "INT_SUB":
            return None
        return expr.operands[0], expr.operands[1]

    def _is_zero_constant(self, expr: Optional[Expression]) -> bool:
        return (
            expr is not None
            and expr.expr_type == ExpressionType.CONSTANT
            and int(expr.value) == 0
        )

    def _reads_share_stack_protector_probe(
        self,
        left: Expression,
        right: Expression,
    ) -> bool:
        left_probe = self._extract_stack_protector_memory_probe(left)
        right_probe = self._extract_stack_protector_memory_probe(right)
        if left_probe is None or right_probe is None:
            return False

        left_base_key, left_disp, left_deref_depth, left_size = left_probe
        right_base_key, right_disp, right_deref_depth, right_size = right_probe
        if left_size != right_size:
            return False
        if left_base_key != right_base_key or left_disp != right_disp:
            return False
        return {left_deref_depth, right_deref_depth} == {0, 1}

    def _extract_stack_protector_memory_probe(
        self,
        expr: Optional[Expression],
    ) -> Optional[Tuple[StructuralKey, int, int, int]]:
        if expr is None:
            return None

        current = expr
        while (
            current.expr_type == ExpressionType.UNARY_OP
            and current.operator in {"INT_ZEXT", "INT_SEXT"}
            and current.operands
        ):
            current = current.operands[0]

        if current.expr_type == ExpressionType.MEMORY and current.operands:
            probe = self._extract_indirect_probe(current.operands[0])
            if probe is None:
                return None
            base_key, displacement, deref_depth = probe
            return (base_key, displacement, deref_depth, int(current.size or 0))

        # Some architectures materialize the stack-protector spill as a direct
        # INDIRECT expression over an already-dereferenced guard pointer instead
        # of wrapping it in a MEMORY node. Preserve the same structured probe.
        probe = self._extract_indirect_probe(current)
        if probe is None:
            return None
        base_key, displacement, deref_depth = probe
        return (base_key, displacement, deref_depth, int(current.size or 0))

    def _extract_indirect_probe(
        self,
        expr: Optional[Expression],
    ) -> Optional[Tuple[StructuralKey, int, int]]:
        if expr is None:
            return None

        current = expr
        while (
            current.expr_type == ExpressionType.UNARY_OP
            and current.operator in {"INT_ZEXT", "INT_SEXT", "INT_2COMP"}
            and current.operands
        ):
            current = current.operands[0]

        if current.expr_type != ExpressionType.BINARY_OP or len(current.operands) != 2:
            return None
        if current.operator not in {"INDIRECT", "PTRADD", "PTRSUB", "INT_ADD"}:
            return None

        left, right = current.operands
        displacement = self._constant_int_value(right)
        base_expr = left
        if displacement is None:
            displacement = self._constant_int_value(left)
            base_expr = right
        if displacement is None:
            return None

        deref_depth = 0
        while base_expr.expr_type == ExpressionType.MEMORY and base_expr.operands:
            deref_depth += 1
            base_expr = base_expr.operands[0]

        return (
            ConditionNormalizer.expression_signature(
                base_expr,
                include_memory_read_order=False,
            ),
            displacement,
            deref_depth,
        )

    def _constant_int_value(self, expr: Optional[Expression]) -> Optional[int]:
        if expr is None or expr.expr_type != ExpressionType.CONSTANT:
            return None
        try:
            return int(expr.value)
        except (TypeError, ValueError):
            return None

    def _mark_incomplete_control_flow(self, analysis: FunctionReturnAnalysis) -> None:
        """後段で保守的に扱うべき不完全な制御フロー要約を記録する。"""
        auto_notes = {
            "unknown_return",
            "overlapping_unconditional_returns",
            "indirect_control_flow_unresolved",
        }
        analysis.analysis_notes = [
            note for note in analysis.analysis_notes
            if note not in auto_notes
        ]
        reasons = []

        if analysis.has_unknown_return():
            reasons.append("unknown_return")
        if analysis.has_overlapping_unconditional_returns():
            reasons.append("overlapping_unconditional_returns")
        if (
            analysis.has_unresolved_return_value()
            and any(
                reason in {"call_out_of_scope", "callind_out_of_scope"}
                for reason in analysis.unknown_event_reasons
            )
        ):
            reasons.append("indirect_control_flow_unresolved")

        if analysis.recovered_from_decompiler:
            reasons = [reason for reason in reasons if reason == "unknown_return"]

        seen = set(analysis.analysis_notes)
        for reason in reasons:
            if reason not in seen:
                analysis.analysis_notes.append(reason)
                seen.add(reason)
        analysis.incomplete_control_flow = bool(reasons)

    def _make_deferred_call_recorder(self, current_function=None):
        current_function_ref = (
            CallTargetRef.from_function(current_function)
            if current_function is not None
            else CallTargetRef.unknown()
        )

        def record_call(
            target,
            args: List[Expression],
            call_target_expr: Optional[Expression] = None,
            pcode_op_ref: Optional[PcodeOpRef] = None,
        ) -> UnknownValueRef:
            target_ref = self._coerce_runtime_target_ref(target) or CallTargetRef.unknown()
            sequence = self._deferred_call_counter
            self._deferred_call_counter += 1
            cloned_args = [self._clone_expression(arg) for arg in args]
            cloned_target_expr = (
                self._clone_expression(call_target_expr)
                if call_target_expr is not None
                else None
            )
            deferred_call_ref = DeferredCallRef(
                caller_program_id=current_function_ref.program_id,
                caller_entry_offset=current_function_ref.entry_offset,
                pcode_op_ref=pcode_op_ref,
                target_ref=target_ref,
                sequence=sequence,
            )
            info = DeferredCallInfo(
                target_ref=target_ref,
                arguments=cloned_args,
                call_target_expr=cloned_target_expr,
                deferred_call_ref=deferred_call_ref,
                placeholder_name=deferred_call_ref.display_name(),
            )
            self._current_deferred_calls[deferred_call_ref.stable_key()] = info
            if self.debug:
                arg_dump = ", ".join(arg.to_string() for arg in cloned_args)
                target_expr_dump = (
                    cloned_target_expr.to_string()
                    if cloned_target_expr is not None
                    else "<none>"
                )
                self._debug_print(
                    f"Recorded deferred call in '{current_function_ref.display_name()}': "
                    f"{info.placeholder_name} -> {target_ref.display_name()}([{arg_dump}]) "
                    f"target_expr={target_expr_dump}"
                )
            return info.unknown_ref

        return record_call

    def _apply_bounded_call_refinement(
        self,
        analysis: FunctionReturnAnalysis,
        active_functions: Set[Tuple[Any, ...]],
        current_function_ref: Optional[CallTargetRef],
    ) -> None:
        if (
            not self._bounded_call_refinement_enabled
            or analysis is None
            or not analysis.deferred_calls
            or self._bounded_call_unroll_limit <= 0
        ):
            return

        def provide_analysis(
            target,
            args: Optional[Sequence[Expression]] = None,
        ) -> Optional[FunctionReturnAnalysis]:
            target_ref = self._coerce_runtime_target_ref(target)
            if target_ref is None:
                return None
            bound_parameter_values = self._bound_parameter_values_from_args(args)
            scope_key = self._analysis_scope_key(target_ref, bound_parameter_values)
            if (
                current_function_ref is not None
                and analysis.analysis_scope_key == scope_key
            ):
                return analysis
            in_progress = self._analysis_in_progress.get(scope_key)
            if in_progress is not None:
                return in_progress
            active_key = self._target_active_key(target_ref)
            if active_key is not None and active_key in active_functions:
                return None
            return self._invoke_get_or_analyze_call_target(
                target_ref,
                active_functions,
                args=args,
            )

        refiner = BoundedCallRefiner(
            provide_analysis,
            max_unroll=self._bounded_call_unroll_limit,
            max_cases=self._bounded_call_max_cases,
            debug=self.debug,
        )
        changed = refiner.refine_analysis(analysis)
        if changed:
            self._debug_print(
                f"Applied bounded call refinement to '{analysis.function_name}' "
                f"(remaining deferred calls={len(analysis.deferred_calls)})"
            )

    def _apply_effect_call_argument_evidence_to_deferred_calls(
        self,
        analysis: FunctionReturnAnalysis,
    ) -> None:
        effect_summary = getattr(analysis, "effect_summary", None)
        evidence = getattr(effect_summary, "call_argument_evidence", None)
        if not evidence or not getattr(analysis, "deferred_calls", None):
            return
        changed = False
        incomplete = False
        for info in analysis.deferred_calls.values():
            if getattr(info, "arguments", None):
                continue
            deferred_ref = getattr(info, "deferred_call_ref", None)
            pcode_ref = getattr(deferred_ref, "pcode_op_ref", None)
            stable_key_fn = getattr(pcode_ref, "stable_key", None)
            if not callable(stable_key_fn):
                continue
            call_evidence = evidence.get(stable_key_fn())
            if call_evidence is None:
                continue
            is_usable = getattr(call_evidence, "is_usable", None)
            if not callable(is_usable) or not is_usable():
                incomplete = True
                continue
            target_matches = getattr(call_evidence, "target_matches", None)
            if callable(target_matches) and not target_matches(getattr(info, "target_ref", None)):
                incomplete = True
                continue
            args = getattr(call_evidence, "arguments", ())
            info.arguments = [self._clone_expression(arg) for arg in args]
            changed = True
        if changed and "effect_call_argument_evidence" not in analysis.analysis_notes:
            analysis.analysis_notes.append("effect_call_argument_evidence")
        if incomplete and "effect_call_argument_evidence_incomplete" not in analysis.analysis_notes:
            analysis.analysis_notes.append("effect_call_argument_evidence_incomplete")

    def _make_empty_effect_summary(
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

    def _recover_control_region_returns_early(
        self,
        current_function,
        tracer: PcodeTracer,
        condition_tracker: ConditionTracker,
        return_ops: List[Any],
        *,
        active_functions,
    ) -> Tuple[Optional[List[ReturnInfo]], List[str]]:
        if not return_ops:
            return None, []

        recovered_switch = self._recover_switch_like_returns_from_placeholder_analysis(
            current_function,
            tracer,
            condition_tracker,
            return_ops,
            active_functions=active_functions,
        )
        if recovered_switch is not None and self._control_region_returns_are_safe(recovered_switch):
            return recovered_switch, ["switch_return_recovery", "control_region_return_recovery"]

        recovered_paths = self._recover_control_flow_returns_from_block_paths(
            current_function,
            tracer,
            condition_tracker,
            return_ops,
            active_functions=active_functions,
        )
        if recovered_paths is not None and self._control_region_returns_are_safe(recovered_paths):
            return recovered_paths, ["control_region_return_recovery"]

        return None, []

    def _recover_switch_like_returns_from_placeholder_analysis(
        self,
        current_function,
        tracer: PcodeTracer,
        condition_tracker: ConditionTracker,
        return_ops: List[Any],
        *,
        active_functions,
    ) -> Optional[List[ReturnInfo]]:
        placeholders: List[ReturnInfo] = []
        fallback_address = (
            str(current_function.getEntryPoint())
            if current_function is not None and hasattr(current_function, "getEntryPoint")
            else "unknown"
        )
        for return_index, return_op in enumerate(return_ops or []):
            site_metadata = self._describe_pcode_site(return_op, fallback_address)
            placeholders.append(
                self._make_return_info(
                    address=cast(str, site_metadata.get("address") or fallback_address),
                    value=Expression.unknown("control_region_placeholder"),
                    conditions=[],
                    branch_index=return_index,
                    site_metadata=site_metadata,
                )
            )

        placeholder_analysis = FunctionReturnAnalysis(
            function_name=current_function.getName() if current_function is not None else "unknown",
            entry_point=fallback_address,
            parameters=list(self._current_parameters or []),
            returns=placeholders,
            function_ref=(
                CallTargetRef.from_function(current_function)
                if current_function is not None
                else None
            ),
            return_type="unknown",
            return_type_obj=None,
            unknown_event_count=1,
            unknown_event_reasons=["indirect_control_flow_unresolved"],
            program_is_big_endian=self._program_is_big_endian(),
        )
        recovered = self._recover_switch_like_returns_from_pcode(
            placeholder_analysis,
            tracer,
            condition_tracker,
            return_ops=return_ops,
            current_function=current_function,
            active_functions=active_functions,
        )
        if recovered is None:
            return None
        return self._merge_equivalent_return_infos(
            self._prune_less_precise_return_infos(recovered)
        )

    def _recover_control_flow_returns_from_block_paths(
        self,
        current_function,
        tracer: PcodeTracer,
        condition_tracker: ConditionTracker,
        return_ops: List[Any],
        *,
        active_functions,
    ) -> Optional[List[ReturnInfo]]:
        recovered_results: List[ReturnInfo] = []
        fallback_address = (
            str(current_function.getEntryPoint())
            if current_function is not None and hasattr(current_function, "getEntryPoint")
            else "unknown"
        )

        for return_index, return_op in enumerate(return_ops or []):
            path_entries = self._get_cached_return_path_entries(
                condition_tracker,
                return_op,
                tracer=tracer,
            )
            if not path_entries:
                return None

            site_metadata = self._describe_pcode_site(return_op, fallback_address)
            address = cast(str, site_metadata.get("address") or fallback_address)
            num_inputs = self._coerce_optional_int(getattr(return_op, "getNumInputs", lambda: 0)())
            num_inputs = num_inputs if num_inputs is not None else 0

            if num_inputs >= 2:
                path_recovered = self._recover_explicit_return_from_block_paths(
                    return_op,
                    address,
                    tracer,
                    condition_tracker,
                    return_index,
                    path_entries,
                    active_functions=active_functions,
                    current_function=current_function,
                    site_metadata=site_metadata,
                )
            else:
                path_recovered = self._recover_implicit_return_from_block_paths(
                    return_op,
                    address,
                    tracer,
                    condition_tracker,
                    return_index,
                    path_entries,
                    active_functions=active_functions,
                    current_function=current_function,
                    site_metadata=site_metadata,
                )

            if not path_recovered:
                return None
            recovered_results.extend(path_recovered)

        if not recovered_results:
            return None

        recovered_results = self._merge_equivalent_return_infos(
            self._prune_less_precise_return_infos(recovered_results)
        )
        return recovered_results

    def _recover_explicit_return_from_block_paths(
        self,
        return_op,
        address: str,
        tracer: PcodeTracer,
        condition_tracker: ConditionTracker,
        return_index: int,
        path_entries,
        active_functions: Optional[Set[Tuple[Any, ...]]] = None,
        current_function=None,
        site_metadata: Optional[Dict[str, Optional[object]]] = None,
    ) -> Optional[List[ReturnInfo]]:
        normalized_entries = self._coerce_block_path_entries(path_entries)
        if not normalized_entries:
            return None

        try:
            candidate_source = return_op.getInput(1)
        except Exception:
            return None

        recovered_results: List[ReturnInfo] = []
        unresolved_paths: List[int] = []

        for path_idx, (block_path, conditions) in enumerate(normalized_entries):
            selected_source = self._select_path_specific_return_source(
                candidate_source,
                block_path,
                condition_tracker=condition_tracker,
                path_conditions=conditions,
            )
            if selected_source is None:
                unresolved_paths.append(path_idx)
                continue

            path_results = self._recover_explicit_return_from_path_source(
                selected_source,
                address,
                tracer,
                condition_tracker,
                list(conditions),
                return_index * 1000 + path_idx * 100,
                active_functions=active_functions,
                current_function=current_function,
                site_metadata=site_metadata,
            )
            if not path_results:
                unresolved_paths.append(path_idx)
                continue
            recovered_results.extend(path_results)

        if recovered_results and not unresolved_paths:
            return self._merge_equivalent_return_infos(recovered_results)

        if self.debug and unresolved_paths:
            self._debug_print(
                "Explicit return path recovery could not resolve source on "
                f"path(s) {unresolved_paths}"
            )
        return None

    def _recover_explicit_return_from_path_source(
        self,
        return_source,
        address: str,
        tracer: PcodeTracer,
        condition_tracker: ConditionTracker,
        path_conditions: List[Condition],
        return_index_base: int,
        active_functions: Optional[Set[Tuple[Any, ...]]] = None,
        current_function=None,
        site_metadata: Optional[Dict[str, Optional[object]]] = None,
    ) -> Optional[List[ReturnInfo]]:
        direct_results = self._materialize_direct_path_specific_return_source(
            return_source,
            address,
            tracer,
            path_conditions,
            return_index_base,
            site_metadata=site_metadata,
        )
        if direct_results is not None:
            return direct_results

        tracked_sources = [self._make_tracked_return_value(return_source, tracer)]
        return self._recover_return_infos_from_tracked_sources(
            tracked_sources,
            address,
            tracer,
            condition_tracker,
            list(path_conditions),
            return_index_base,
            all_path_conditions=[list(path_conditions)],
            active_functions=active_functions,
            current_function=current_function,
            site_metadata=site_metadata,
        )

    def _materialize_direct_path_specific_return_source(
        self,
        return_source,
        address: str,
        tracer: PcodeTracer,
        path_conditions: List[Condition],
        return_index_base: int,
        site_metadata: Optional[Dict[str, Optional[object]]] = None,
    ) -> Optional[List[ReturnInfo]]:
        if return_source is None or self._contains_multiequal(return_source):
            return None

        # get_all_valid_block_paths_to_return() already provides exact feasible path
        # partitions, so re-simplifying the same guard set here only burns solver time.
        normalized_conditions = list(path_conditions or [])

        try:
            tracer.clear_cache()
        except Exception:
            pass

        value = tracer.trace_varnode(return_source, use_cache=False)
        if value is None:
            return None

        candidate_value = self._fold_constant_expression(
            value,
            fallback_expr=value,
        ) or value
        candidate_value = self._concretize_readonly_loads(
            candidate_value,
            normalized_conditions,
            self._current_parameters,
        )
        if candidate_value is None:
            return None
        if (
            self._expression_contains_unresolved_value(candidate_value)
            or expression_contains_post_state_reads(candidate_value)
            or _expression_contains_observed_loads(candidate_value)
        ):
            return None

        if not self._expression_contains_phi(candidate_value):
            return [
                self._make_return_info(
                    address=address,
                    value=candidate_value,
                    conditions=normalized_conditions,
                    branch_index=return_index_base,
                    site_metadata=site_metadata,
                )
            ]

        reduced_value = ConditionSimplifier.reduce_expression_under_conditions(
            candidate_value,
            normalized_conditions,
        )
        candidate_value = self._fold_constant_expression(
            reduced_value,
            fallback_expr=candidate_value,
        ) or reduced_value
        if (
            self._expression_contains_unresolved_value(candidate_value)
            or expression_contains_post_state_reads(candidate_value)
            or _expression_contains_observed_loads(candidate_value)
        ):
            return None
        if not self._expression_contains_phi(candidate_value):
            return [
                self._make_return_info(
                    address=address,
                    value=candidate_value,
                    conditions=normalized_conditions,
                    branch_index=return_index_base,
                    site_metadata=site_metadata,
                )
            ]

        split_cases = self._split_object_centric_return_case(
            candidate_value,
            normalized_conditions,
        )
        results: List[ReturnInfo] = []
        for split_index, (split_value, split_conditions) in enumerate(split_cases or []):
            normalized_value = self._fold_constant_expression(
                split_value,
                fallback_expr=candidate_value,
            ) or split_value
            if (
                self._expression_contains_unresolved_value(normalized_value)
                or expression_contains_post_state_reads(normalized_value)
                or _expression_contains_observed_loads(normalized_value)
            ):
                return None
            results.append(
                self._make_return_info(
                    address=address,
                    value=normalized_value,
                    conditions=list(split_conditions or []),
                    branch_index=(
                        return_index_base
                        if len(split_cases) == 1
                        else return_index_base * 10 + split_index
                    ),
                    site_metadata=site_metadata,
                )
            )

        if not results:
            return None
        return self._merge_equivalent_return_infos(results)

    def _get_cached_return_path_entries(
        self,
        condition_tracker: ConditionTracker,
        return_op,
        *,
        tracer: Optional[PcodeTracer] = None,
    ) -> Optional[List[Tuple[List[Any], List[Condition]]]]:
        key = self._pcode_op_identity_key(return_op) or ("id", id(return_op))
        cached = self._return_path_entry_cache.get(key, None)
        if key in self._return_path_entry_cache:
            return cached

        get_paths_to_return = getattr(condition_tracker, "get_all_valid_block_paths_to_return", None)
        if not callable(get_paths_to_return):
            self._return_path_entry_cache[key] = None
            return None

        raw_path_entries = get_paths_to_return(return_op)
        path_entries = self._coerce_block_path_entries(raw_path_entries)
        if path_entries and tracer is not None:
            path_entries = self._filter_noreturn_return_path_entries(path_entries, tracer, return_op)

        self._return_path_entry_cache[key] = path_entries
        return path_entries

    def _control_region_returns_are_safe(
        self,
        return_infos: List[ReturnInfo],
    ) -> bool:
        if not return_infos:
            return False
        for info in return_infos:
            if self._expression_contains_unresolved_value(info.value):
                return False
            if expression_contains_post_state_reads(info.value):
                return False
            if _expression_contains_observed_loads(info.value):
                return False
        return True

    def _return_infos_have_conflicting_overlap(
        self,
        return_infos: List[ReturnInfo],
    ) -> bool:
        for left_index, left in enumerate(return_infos):
            for right in return_infos[left_index + 1:]:
                combined_conditions = ConditionSimplifier.simplify_conditions(
                    list(left.conditions or []) + list(right.conditions or [])
                )
                if ConditionSimplifier.is_contradiction(combined_conditions):
                    continue
                if _expressions_equivalent(left.value, right.value):
                    continue
                if self.debug:
                    cond_dump = [
                        ConditionSimplifier.get_simplified_condition_string(cond)
                        for cond in combined_conditions
                    ]
                    self._debug_print(
                        "Control-region recovery rejected due to overlapping regions: "
                        f"left={self._debug_expr_identity_summary(left.value)} "
                        f"right={self._debug_expr_identity_summary(right.value)} "
                        f"conditions={cond_dump}"
                    )
                return True
        return False

    def _recover_call_wrapper_returns(
        self,
        decompile_results,
        analysis: FunctionReturnAnalysis,
        current_function,
        tracer: PcodeTracer,
        condition_tracker: ConditionTracker,
        return_ops: List[Any],
        active_functions: Optional[Set[Tuple[Any, ...]]] = None,
    ) -> Optional[List[ReturnInfo]]:
        """wrapper らしい unknown return を P-code/CFG ベースでのみ復元する。"""
        if not self._analysis_needs_wrapper_recovery(analysis):
            return None

        recovered_from_pcode = self._recover_call_wrapper_returns_from_pcode(
            analysis,
            tracer,
            condition_tracker,
            return_ops,
            current_function,
            active_functions or set(),
        )
        if recovered_from_pcode is not None:
            if self.debug:
                self._debug_print(
                    f"Call-wrapper recovery reconstructed {len(recovered_from_pcode)} return case(s) "
                    "from P-code block paths"
                )
            return recovered_from_pcode
        if self.debug:
            self._debug_print(
                "Call-wrapper recovery declined: no safe P-code/CFG reconstruction was available"
            )
        return None

    def _recover_call_wrapper_returns_from_pcode(
        self,
        analysis: FunctionReturnAnalysis,
        tracer: PcodeTracer,
        condition_tracker: ConditionTracker,
        return_ops: List[Any],
        current_function,
        active_functions: Set[Tuple[Any, ...]],
    ) -> Optional[List[ReturnInfo]]:
        """entry -> RETURN の block path 上の terminal CALL を callee summary から復元する。"""
        if not self._analysis_needs_wrapper_recovery(analysis):
            return None

        recovered: List[ReturnInfo] = []
        for return_index, return_op in enumerate(return_ops):
            path_entries = condition_tracker.get_all_valid_block_paths_to_return(return_op)
            if not path_entries:
                if self.debug:
                    self._debug_print(
                        f"P-code call-wrapper recovery aborted: no valid block path to RETURN #{return_index}"
                    )
                return None

            site_metadata = self._describe_pcode_site(return_op, analysis.entry_point)
            address = cast(str, site_metadata.get("address") or analysis.entry_point)
            return_results: List[ReturnInfo] = []

            for path_index, (block_path, path_conditions) in enumerate(path_entries):
                terminal_call = self._find_terminal_call_on_block_path(
                    block_path,
                    return_op,
                    tracer=tracer,
                    condition_tracker=condition_tracker,
                    current_function=current_function,
                    path_conditions=path_conditions,
                )
                if terminal_call is None:
                    if self.debug:
                        block_indexes = [block.index for block in block_path]
                        self._debug_print(
                            "P-code call-wrapper recovery aborted: no safe terminal CALL/CALLIND "
                            f"found on path {path_index} to RETURN #{return_index} "
                            f"(blocks={block_indexes})"
                        )
                    return None

                path_recovered = self._recover_implicit_return_from_terminal_call(
                    terminal_call,
                    address,
                    tracer,
                    condition_tracker,
                    path_conditions,
                    return_index,
                    all_path_conditions=[path_conditions],
                    active_functions=active_functions,
                    current_function=current_function,
                    site_metadata=site_metadata,
                )
                if not path_recovered:
                    if self.debug:
                        self._debug_print(
                            "P-code call-wrapper recovery aborted: terminal call expansion "
                            f"failed on path {path_index} to RETURN #{return_index}"
                        )
                    return None
                return_results.extend(path_recovered)

            if not return_results:
                return None
            recovered.extend(return_results)

        return recovered or None

    def _analysis_needs_wrapper_recovery(
        self,
        analysis: Optional[FunctionReturnAnalysis],
    ) -> bool:
        if analysis is None or not analysis.returns:
            return False
        return analysis.has_unknown_return() or analysis.has_unresolved_return_value()

    def _should_attempt_switch_recovery(
        self,
        analysis: Optional[FunctionReturnAnalysis],
    ) -> bool:
        if analysis is None or not analysis.returns:
            return False
        if analysis.recovered_from_decompiler:
            return False
        if analysis.has_unknown_return():
            return True
        if analysis.has_overlapping_unconditional_returns():
            return True
        if self._analysis_has_ambiguous_condition_region_returns(analysis):
            return True
        if analysis.has_unresolved_return_value():
            return True
        return any(
            reason in {"callind_out_of_scope", "indirect_control_flow_unresolved"}
            for reason in getattr(analysis, "unknown_event_reasons", [])
        )

    def _recover_switch_like_returns_from_pcode(
        self,
        analysis: FunctionReturnAnalysis,
        tracer: PcodeTracer,
        condition_tracker: ConditionTracker,
        return_ops: Optional[List[Any]] = None,
        current_function=None,
        active_functions: Optional[Set[Tuple[Any, ...]]] = None,
    ) -> Optional[List[ReturnInfo]]:
        from ..transform.expander import ExpandedValue

        if not self._should_attempt_switch_recovery(analysis):
            return None

        switch_dispatch_summaries = build_switch_dispatch_summaries(
            tracer=tracer,
            condition_tracker=condition_tracker,
            parameters=self._current_parameters,
            concretize_readonly_loads=self._concretize_readonly_loads,
            read_memory_value=self._read_memory_value,
            max_cases=self._bounded_call_max_cases,
            debug=self.debug,
            debug_print=self._debug_print if self.debug else None,
        )
        attach_summaries = getattr(condition_tracker, "attach_switch_dispatch_summaries", None)
        if callable(attach_summaries):
            attach_summaries(switch_dispatch_summaries)

        for dispatch_summary in switch_dispatch_summaries:
            switch_block = dispatch_summary.block_info
            dispatch_op = dispatch_summary.dispatch_op

            impacted_site_keys = self._collect_switch_impacted_return_sites(
                switch_block,
                return_ops or [],
                condition_tracker,
                analysis.entry_point,
            )
            if impacted_site_keys is None or not impacted_site_keys:
                continue

            affected_returns = [
                ret for ret in (analysis.returns or []) if self._return_site_key(ret) in impacted_site_keys
            ]
            unaffected_returns = [
                ret for ret in (analysis.returns or []) if self._return_site_key(ret) not in impacted_site_keys
            ]
            if not affected_returns:
                continue
            if not self._switch_recovery_targets_problematic_region(analysis, affected_returns):
                continue

            candidate_entries = self._enumerate_switch_dispatch_targets(dispatch_summary)
            if not candidate_entries or len(candidate_entries) < 2:
                continue

            dispatch_args = self._recover_dispatch_call_arguments(dispatch_op, tracer)
            expanded_values: List[ExpandedValue] = []
            candidate_failed = False
            for address_value, branch_conditions in candidate_entries:
                resolved = self._resolve_local_code_target_expansions(
                    address_value,
                    active_functions or set(),
                    current_function=current_function,
                    args=dispatch_args,
                )
                if not resolved:
                    resolved = self._resolve_switch_case_target_expansions(
                        address_value,
                        branch_conditions,
                        tracer,
                        condition_tracker,
                        return_ops or [],
                        active_functions=active_functions or set(),
                        current_function=current_function,
                    )
                if not resolved:
                    if self.debug:
                        cond_dump = [
                            ConditionSimplifier.get_simplified_condition_string(cond)
                            for cond in branch_conditions
                        ]
                        self._debug_print(
                            "Switch recovery aborted: local target expansion failed for "
                            f"0x{address_value:x} under {cond_dump}"
                        )
                    candidate_failed = True
                    break

                for ev in resolved:
                    merged_conditions = ConditionSimplifier.simplify_conditions(
                        list(branch_conditions) + list(getattr(ev, "conditions", []) or [])
                    )
                    if ConditionSimplifier.is_contradiction(merged_conditions):
                        continue
                    expanded_values.append(
                        ExpandedValue(
                            value=self._clone_expression(ev.value),
                            conditions=merged_conditions,
                        )
                    )

            if candidate_failed or not expanded_values:
                continue

            site_metadata = self._describe_pcode_site(
                dispatch_op,
                analysis.entry_point,
                identity_prefix="switch_dispatch",
            )
            recovered = self._build_return_infos_from_expansions(
                cast(str, site_metadata.get("address") or analysis.entry_point),
                expanded_values,
                0,
                site_metadata=site_metadata,
            )
            recovered = self._merge_equivalent_return_infos(
                self._prune_less_precise_return_infos(recovered)
            )
            if not recovered:
                continue
            if not self._switch_recovery_improves_returns(analysis, affected_returns, recovered):
                continue
            if self._switch_recovery_conflicts_with_unaffected_returns(unaffected_returns, recovered):
                continue
            combined = self._merge_equivalent_return_infos(
                self._prune_less_precise_return_infos(list(unaffected_returns) + recovered)
            )
            if not combined:
                continue
            if self.debug:
                self._debug_print(
                    "Recovered switch-like return cases from JumpTable/CFG structure "
                    f"(dispatch={dispatch_summary.dispatch_mnemonic}, "
                    f"affected_sites={sorted(impacted_site_keys)}, recovered={len(recovered)})"
                )
            return combined

        block_by_index = getattr(condition_tracker, "block_by_index", None) or {}
        switch_blocks = [
            block_info
            for block_info in block_by_index.values()
            if self._find_indirect_dispatch_op_on_block(block_info) is not None
        ]
        if not switch_blocks:
            return None

        for switch_block in sorted(switch_blocks, key=lambda info: info.index):
            indirect_op = self._find_indirect_dispatch_op_on_block(switch_block)
            if indirect_op is None:
                continue

            impacted_site_keys = self._collect_switch_impacted_return_sites(
                switch_block,
                return_ops or [],
                condition_tracker,
                analysis.entry_point,
            )
            if impacted_site_keys is None or not impacted_site_keys:
                continue

            affected_returns = [
                ret for ret in (analysis.returns or []) if self._return_site_key(ret) in impacted_site_keys
            ]
            unaffected_returns = [
                ret for ret in (analysis.returns or []) if self._return_site_key(ret) not in impacted_site_keys
            ]
            if not affected_returns:
                continue
            if not self._switch_recovery_targets_problematic_region(analysis, affected_returns):
                continue

            candidate_entries = self._enumerate_switch_branch_targets(
                switch_block,
                indirect_op,
                tracer,
                condition_tracker,
            )
            if not candidate_entries or len(candidate_entries) < 2:
                continue

            dispatch_args = self._recover_dispatch_call_arguments(indirect_op, tracer)
            expanded_values: List[ExpandedValue] = []
            candidate_failed = False
            for address_value, branch_conditions in candidate_entries:
                resolved = self._resolve_local_code_target_expansions(
                    address_value,
                    active_functions or set(),
                    current_function=current_function,
                    args=dispatch_args,
                )
                if not resolved:
                    resolved = self._resolve_switch_case_target_expansions(
                        address_value,
                        branch_conditions,
                        tracer,
                        condition_tracker,
                        return_ops or [],
                        active_functions=active_functions or set(),
                        current_function=current_function,
                    )
                if not resolved:
                    if self.debug:
                        cond_dump = [
                            ConditionSimplifier.get_simplified_condition_string(cond)
                            for cond in branch_conditions
                        ]
                        self._debug_print(
                            "Switch recovery aborted: local target expansion failed for "
                            f"0x{address_value:x} under {cond_dump}"
                        )
                    candidate_failed = True
                    break

                for ev in resolved:
                    merged_conditions = ConditionSimplifier.simplify_conditions(
                        list(branch_conditions) + list(getattr(ev, "conditions", []) or [])
                    )
                    if ConditionSimplifier.is_contradiction(merged_conditions):
                        continue
                    expanded_values.append(
                        ExpandedValue(
                            value=self._clone_expression(ev.value),
                            conditions=merged_conditions,
                        )
                    )

            if candidate_failed or not expanded_values:
                continue

            site_metadata = self._describe_pcode_site(
                indirect_op,
                analysis.entry_point,
                identity_prefix="indirect_dispatch",
            )
            recovered = self._build_return_infos_from_expansions(
                cast(str, site_metadata.get("address") or analysis.entry_point),
                expanded_values,
                0,
                site_metadata=site_metadata,
            )
            recovered = self._merge_equivalent_return_infos(
                self._prune_less_precise_return_infos(recovered)
            )
            if not recovered:
                continue
            if not self._switch_recovery_improves_returns(analysis, affected_returns, recovered):
                continue
            if self._switch_recovery_conflicts_with_unaffected_returns(unaffected_returns, recovered):
                continue
            combined = self._merge_equivalent_return_infos(
                self._prune_less_precise_return_infos(list(unaffected_returns) + recovered)
            )
            if not combined:
                continue
            if self.debug:
                self._debug_print(
                    "Recovered switch-like return cases from indirect-dispatch/CFG structure "
                    f"(affected_sites={sorted(impacted_site_keys)}, recovered={len(recovered)})"
                )
            return combined

        return None

    def _find_indirect_dispatch_op_on_block(
        self,
        block_info,
        mnemonics: Optional[Set[str]] = None,
    ) -> Optional[Any]:
        if block_info is None:
            return None
        allowed_mnemonics = mnemonics or {"BRANCHIND", "CALLIND"}
        for pcode_op in reversed(list(getattr(block_info, "pcode_ops", []) or [])):
            try:
                if str(pcode_op.getMnemonic()) in allowed_mnemonics:
                    return pcode_op
            except Exception:
                continue
        return None

    def _enumerate_switch_dispatch_targets(
        self,
        dispatch_summary,
    ) -> List[Tuple[int, List[Condition]]]:
        resolved_targets: List[Tuple[int, List[Condition]]] = []
        seen = set()

        for path_summary in getattr(dispatch_summary, "paths", []) or []:
            for dispatch_case in getattr(path_summary, "cases", []) or []:
                merged_conditions = ConditionSimplifier.simplify_conditions(
                    list(getattr(dispatch_case, "conditions", []) or [])
                )
                if ConditionSimplifier.is_contradiction(merged_conditions):
                    continue
                key = (
                    int(getattr(dispatch_case, "target_address", 0)),
                    tuple(
                        ConditionSimplifier.get_simplified_condition_string(cond)
                        for cond in merged_conditions
                    ),
                )
                if key in seen:
                    continue
                seen.add(key)
                resolved_targets.append(
                    (
                        int(getattr(dispatch_case, "target_address", 0)),
                        merged_conditions,
                    )
                )

        if len(resolved_targets) > self._bounded_call_max_cases:
            if self.debug:
                self._debug_print(
                    "Switch recovery skipped: dispatch fanout exceeds configured safety limit "
                    f"({len(resolved_targets)} > {self._bounded_call_max_cases})"
                )
            return []
        return resolved_targets

    def _recover_dispatch_call_arguments(
        self,
        dispatch_op,
        tracer: PcodeTracer,
    ) -> List[Expression]:
        if dispatch_op is None:
            return []
        try:
            mnemonic = dispatch_op.getMnemonic()
        except Exception:
            mnemonic = None
        if mnemonic != "CALLIND":
            return []

        recovered: List[Expression] = []
        try:
            num_inputs = int(dispatch_op.getNumInputs())
        except Exception:
            num_inputs = 0
        for input_index in range(1, max(0, num_inputs)):
            try:
                varnode = dispatch_op.getInput(input_index)
            except Exception:
                continue
            recovered.append(
                _resolve_call_argument_expression(
                    varnode,
                    tracer,
                    self._current_parameters or [],
                )
            )
        return recovered

    def _resolve_switch_case_target_expansions(
        self,
        address_value: int,
        dispatch_conditions: List[Condition],
        tracer: PcodeTracer,
        condition_tracker: ConditionTracker,
        return_ops: List[Any],
        *,
        active_functions: Set[Tuple[Any, ...]],
        current_function=None,
    ):
        from ..transform.expander import ExpandedValue

        target_block = self._find_block_info_for_program_offset(condition_tracker, address_value)
        if target_block is None:
            return None

        recovered_infos: List[ReturnInfo] = []
        get_paths_to_return = getattr(condition_tracker, "get_all_valid_block_paths_to_return", None)
        if not callable(get_paths_to_return):
            return None

        fallback_address = (
            str(current_function.getEntryPoint())
            if current_function is not None and hasattr(current_function, "getEntryPoint")
            else "unknown"
        )

        for return_index, return_op in enumerate(return_ops or []):
            path_entries = self._get_cached_return_path_entries(
                condition_tracker,
                return_op,
            )
            if not path_entries:
                continue

            for path_index, (block_path, path_conditions) in enumerate(path_entries):
                start_index = self._find_block_index_on_path(block_path, target_block)
                if start_index is None:
                    continue

                combined_conditions = ConditionSimplifier.simplify_conditions(
                    list(path_conditions) + list(dispatch_conditions)
                )
                if ConditionSimplifier.is_contradiction(combined_conditions):
                    continue

                site_metadata = self._describe_pcode_site(return_op, fallback_address)
                suffix_path = list(block_path[start_index:])
                linear_ops = self._collect_linear_ops_to_return(suffix_path, return_op)
                if not linear_ops:
                    continue

                tracked_values = self._build_return_tracking_targets(
                    return_op,
                    tracer=tracer,
                    current_function=current_function,
                )
                if not tracked_values:
                    continue

                for pcode_op in reversed(linear_ops[:-1]):
                    tracked_values = self._rewrite_tracked_return_values_for_op(
                        tracked_values,
                        pcode_op,
                        tracer=tracer,
                        condition_tracker=condition_tracker,
                        path_conditions=combined_conditions,
                        current_function=current_function,
                    )
                    if not tracked_values:
                        break

                if not tracked_values:
                    continue

                path_results = self._recover_return_infos_from_tracked_sources(
                    tracked_values,
                    cast(str, site_metadata.get("address") or fallback_address),
                    tracer,
                    condition_tracker,
                    combined_conditions,
                    return_index * 1000 + path_index,
                    all_path_conditions=[combined_conditions],
                    active_functions=active_functions,
                    current_function=current_function,
                    site_metadata=site_metadata,
                )

                if path_results:
                    recovered_infos.extend(path_results)

        if not recovered_infos:
            return None

        normalized_infos = self._merge_equivalent_return_infos(
            self._prune_less_precise_return_infos(recovered_infos)
        )
        if not normalized_infos:
            return None

        expanded_values = []
        for ret_info in normalized_infos:
            residual_conditions = ConditionSimplifier.subtract_implied_conditions(
                list(ret_info.conditions),
                list(dispatch_conditions),
            )
            expanded_values.append(
                ExpandedValue(
                    value=self._clone_expression(ret_info.value),
                    conditions=residual_conditions,
                )
            )
        return expanded_values or None

    def _find_block_info_for_program_offset(
        self,
        condition_tracker: ConditionTracker,
        address_value: int,
    ):
        block_by_index = getattr(condition_tracker, "block_by_index", None) or {}
        for block_info in block_by_index.values():
            block = getattr(block_info, "block", None)
            if block is None:
                continue
            start_offset = self._address_offset_for_block_endpoint(getattr(block, "getStart", lambda: None)())
            stop_offset = self._address_offset_for_block_endpoint(getattr(block, "getStop", lambda: None)())
            if start_offset is None:
                continue
            if stop_offset is None:
                stop_offset = start_offset
            lo = min(start_offset, stop_offset)
            hi = max(start_offset, stop_offset)
            if lo <= int(address_value) <= hi:
                return block_info
        return None

    def _address_offset_for_block_endpoint(self, address) -> Optional[int]:
        if address is None:
            return None
        try:
            return int(address.getOffset())
        except Exception:
            return None

    def _enumerate_switch_branch_targets(
        self,
        switch_block,
        indirect_op,
        tracer: PcodeTracer,
        condition_tracker: ConditionTracker,
    ) -> List[Tuple[int, List[Condition]]]:
        if indirect_op is None or indirect_op.getNumInputs() < 1:
            return []

        base_paths = condition_tracker.get_all_valid_block_paths_to_block(switch_block)
        if not base_paths:
            base_paths = [([switch_block], [])]

        resolved_targets: List[Tuple[int, List[Condition]]] = []
        seen = set()
        for _blocks, base_conditions in base_paths:
            try:
                target_varnode = indirect_op.getInput(0)
            except Exception:
                return []

            target_expr = tracer.trace_varnode(target_varnode, use_cache=False)
            target_expr = self._concretize_readonly_loads(
                target_expr,
                list(base_conditions),
                self._current_parameters,
            )
            target_branches = _enumerate_constant_expression_branches(target_expr)
            if not target_branches:
                if self.debug:
                    self._debug_print(
                        "Switch recovery skipped on block "
                        f"{switch_block.index}: indirect target was not finitely enumerable"
                    )
                return []

            for branch_conditions, address_value in target_branches:
                merged_conditions = ConditionSimplifier.simplify_conditions(
                    list(base_conditions) + list(branch_conditions)
                )
                if ConditionSimplifier.is_contradiction(merged_conditions):
                    continue
                key = (
                    int(address_value),
                    tuple(
                        ConditionSimplifier.get_simplified_condition_string(cond)
                        for cond in merged_conditions
                    ),
                )
                if key in seen:
                    continue
                seen.add(key)
                resolved_targets.append((int(address_value), merged_conditions))

        if len(resolved_targets) > self._bounded_call_max_cases:
            if self.debug:
                self._debug_print(
                    "Switch recovery skipped: branch target fanout exceeds configured safety limit "
                    f"({len(resolved_targets)} > {self._bounded_call_max_cases})"
                )
            return []

        return resolved_targets

    def _collect_switch_impacted_return_sites(
        self,
        switch_block,
        return_ops: List[Any],
        condition_tracker: ConditionTracker,
        fallback_address: str,
    ) -> Optional[Set[str]]:
        impacted: Set[str] = set()
        switch_index = getattr(switch_block, "index", None)

        for return_index, return_op in enumerate(return_ops or []):
            raw_entries = condition_tracker.get_all_valid_block_paths_to_return(return_op)
            path_entries = self._coerce_block_path_entries(raw_entries)
            if not path_entries:
                continue

            path_hits = [
                any(getattr(block_info, "index", None) == switch_index for block_info in (block_path or []))
                for block_path, _conditions in path_entries
            ]
            if not any(path_hits):
                continue
            if not all(path_hits):
                if self.debug:
                    self._debug_print(
                        "Switch recovery skipped: candidate BRANCHIND only influences a subset of "
                        f"paths to RETURN #{return_index}"
                    )
                return None

            site_metadata = self._describe_pcode_site(return_op, fallback_address)
            impacted.add(cast(str, site_metadata.get("pcode_identity") or site_metadata.get("address")))

        return impacted

    def _switch_recovery_targets_problematic_region(
        self,
        analysis: FunctionReturnAnalysis,
        affected_returns: List[ReturnInfo],
    ) -> bool:
        if not affected_returns:
            return False

        affected_analysis = FunctionReturnAnalysis(
            function_name=analysis.function_name,
            entry_point=analysis.entry_point,
            parameters=list(analysis.parameters or []),
            returns=list(affected_returns),
            function_ref=analysis.function_ref,
            return_type=analysis.return_type,
            return_type_obj=analysis.return_type_obj,
            unknown_event_count=analysis.unknown_event_count,
            unknown_event_reasons=list(analysis.unknown_event_reasons),
            program_is_big_endian=analysis.program_is_big_endian,
        )
        if affected_analysis.has_unknown_return():
            return True
        if affected_analysis.has_unresolved_return_value():
            return True
        if affected_analysis.has_overlapping_unconditional_returns():
            return True
        return self._analysis_has_ambiguous_condition_region_returns(affected_analysis)

    def _switch_recovery_improves_returns(
        self,
        analysis: FunctionReturnAnalysis,
        affected_returns: List[ReturnInfo],
        recovered: List[ReturnInfo],
    ) -> bool:
        if not recovered:
            return False
        if any(self._expression_contains_unresolved_value(ret.value) for ret in recovered):
            return False

        original_unresolved = sum(
            1 for ret in affected_returns if self._expression_contains_unresolved_value(ret.value)
        )
        recovered_unresolved = sum(
            1 for ret in recovered if self._expression_contains_unresolved_value(ret.value)
        )
        if recovered_unresolved < original_unresolved:
            return True

        affected_analysis = FunctionReturnAnalysis(
            function_name=analysis.function_name,
            entry_point=analysis.entry_point,
            parameters=list(analysis.parameters or []),
            returns=list(affected_returns),
            function_ref=analysis.function_ref,
            return_type=analysis.return_type,
            return_type_obj=analysis.return_type_obj,
            unknown_event_count=analysis.unknown_event_count,
            unknown_event_reasons=list(analysis.unknown_event_reasons),
            program_is_big_endian=analysis.program_is_big_endian,
        )
        if affected_analysis.has_overlapping_unconditional_returns():
            return True
        if self._analysis_has_ambiguous_condition_region_returns(affected_analysis):
            return True
        return False

    def _switch_recovery_conflicts_with_unaffected_returns(
        self,
        unaffected_returns: List[ReturnInfo],
        recovered: List[ReturnInfo],
    ) -> bool:
        for existing in unaffected_returns:
            for candidate in recovered:
                overlap_conditions = ConditionSimplifier.simplify_conditions(
                    list(existing.conditions) + list(candidate.conditions)
                )
                if ConditionSimplifier.is_contradiction(overlap_conditions):
                    continue
                if _expressions_equivalent(existing.value, candidate.value):
                    continue
                if self.debug:
                    cond_dump = [
                        ConditionSimplifier.get_simplified_condition_string(cond)
                        for cond in overlap_conditions
                    ]
                    self._debug_print(
                        "Switch recovery rejected due to overlap with unaffected return case: "
                        f"existing={self._debug_expr_summary(existing.value)} "
                        f"candidate={self._debug_expr_summary(candidate.value)} "
                        f"conditions={cond_dump}"
                    )
                return True
        return False

    def _find_terminal_call_on_block_path(
        self,
        block_path: List[Any],
        return_op,
        *,
        tracer: Optional[PcodeTracer] = None,
        condition_tracker: Optional[ConditionTracker] = None,
        current_function=None,
        path_conditions: Optional[List[Condition]] = None,
    ):
        """block path 上で RETURN 値 provenance を満たす wrapper 候補 CALL/CALLIND を探す。"""
        linear_ops = self._collect_linear_ops_to_return(block_path, return_op)
        if not linear_ops:
            return None
        return self._find_terminal_call_from_linear_ops(
            linear_ops,
            return_op,
            tracer=tracer,
            condition_tracker=condition_tracker,
            current_function=current_function,
            block_path=block_path,
            path_conditions=path_conditions,
        )

    def _collect_linear_ops_to_return(
        self,
        block_path: List[Any],
        return_op,
    ) -> Optional[List[Any]]:
        linear_ops = []
        for block_info in block_path:
            for pcode_op in getattr(block_info, "pcode_ops", []) or []:
                linear_ops.append(pcode_op)
                if self._pcode_ops_match(pcode_op, return_op):
                    break
            if linear_ops and self._pcode_ops_match(linear_ops[-1], return_op):
                break

        if not linear_ops or not self._pcode_ops_match(linear_ops[-1], return_op):
            return None
        return linear_ops

    def _find_terminal_call_from_linear_ops(
        self,
        linear_ops: List[Any],
        return_op,
        *,
        tracer: Optional[PcodeTracer] = None,
        condition_tracker: Optional[ConditionTracker] = None,
        current_function=None,
        block_path=None,
        path_conditions: Optional[List[Condition]] = None,
    ):
        for index in range(len(linear_ops) - 2, -1, -1):
            pcode_op = linear_ops[index]
            if not self._is_pcode_call_op(pcode_op):
                continue
            if self._call_output_proves_wrapper_return(
                linear_ops,
                index,
                return_op,
                tracer=tracer,
                condition_tracker=condition_tracker,
                current_function=current_function,
                block_path=block_path,
                path_conditions=path_conditions,
            ):
                if self.debug:
                    self._debug_print(
                        "Wrapper provenance selected terminal "
                        f"{self._pcode_op_debug_name(pcode_op)} before RETURN"
                    )
                return pcode_op
        return None

    def _get_pcode_opcode(self, pcode_op) -> Optional[int]:
        if pcode_op is None:
            return None
        get_opcode = getattr(pcode_op, "getOpcode", None)
        if callable(get_opcode):
            try:
                return int(get_opcode())
            except Exception:
                pass
        get_mnemonic = getattr(pcode_op, "getMnemonic", None)
        if callable(get_mnemonic):
            try:
                mnemonic = str(get_mnemonic())
            except Exception:
                mnemonic = ""
            return _PCODE_OPCODE_BY_MNEMONIC.get(mnemonic)
        return None

    def _pcode_op_debug_name(self, pcode_op) -> str:
        if pcode_op is None:
            return "<none>"
        get_mnemonic = getattr(pcode_op, "getMnemonic", None)
        if callable(get_mnemonic):
            try:
                return str(get_mnemonic())
            except Exception:
                return "<pcode>"
        return "<pcode>"

    def _is_pcode_call_op(self, pcode_op) -> bool:
        opcode = self._get_pcode_opcode(pcode_op)
        return opcode in _PCODE_CALL_OPCODES

    def _tracked_return_value_key(self, tracked: _TrackedReturnValue) -> Tuple[Any, ...]:
        varnode_key = self._varnode_location_key(tracked.varnode)
        if varnode_key is None and tracked.varnode is not None:
            varnode_key = ("id", id(tracked.varnode))
        storage = tracked.storage
        storage_key = None
        if storage is not None:
            storage_key = (
                bool(getattr(storage, "is_register", False)),
                getattr(storage, "space_name", None),
                getattr(storage, "offset", None),
                getattr(storage, "size", None),
                getattr(storage, "size_bits", None),
                getattr(storage, "register_name", None),
                getattr(storage, "base_register_name", None),
                getattr(storage, "bit_offset_in_base", None),
            )
        producer_key = self._pcode_op_identity_key(tracked.producer_op)
        if producer_key is None and tracked.producer_op is not None:
            producer_key = ("id", id(tracked.producer_op))
        return (varnode_key, storage_key, producer_key)

    def _deduplicate_tracked_return_values(
        self,
        tracked_values: List[_TrackedReturnValue],
    ) -> List[_TrackedReturnValue]:
        deduped: List[_TrackedReturnValue] = []
        seen: Set[Tuple[Any, ...]] = set()
        for tracked in tracked_values:
            key = self._tracked_return_value_key(tracked)
            if key in seen:
                continue
            seen.add(key)
            deduped.append(tracked)
        return deduped

    def _make_tracked_return_value(
        self,
        varnode,
        tracer: Optional[PcodeTracer],
        *,
        storage: Optional[StorageInfo] = None,
        producer_op=None,
    ) -> _TrackedReturnValue:
        resolved_storage = storage
        if resolved_storage is None and tracer is not None and varnode is not None:
            try:
                resolved_storage = tracer._get_storage_info_from_varnode(varnode)
            except Exception:
                resolved_storage = None
        return _TrackedReturnValue(
            varnode=varnode,
            storage=resolved_storage,
            producer_op=producer_op,
        )

    def _make_tracked_return_storage_value(
        self,
        storage: Optional[StorageInfo],
        *,
        producer_op=None,
    ) -> _TrackedReturnValue:
        return _TrackedReturnValue(
            varnode=None,
            storage=storage,
            producer_op=producer_op,
        )

    def _make_tracked_return_value_from_affecting_op(
        self,
        pcode_op,
        target_storage: Optional[StorageInfo],
        tracer: Optional[PcodeTracer],
    ) -> Optional[_TrackedReturnValue]:
        if pcode_op is None:
            return None

        output = getattr(pcode_op, "getOutput", lambda: None)()
        if output is not None:
            return self._make_tracked_return_value(
                output,
                tracer,
                storage=target_storage,
                producer_op=pcode_op,
            )

        if self._is_pcode_call_op(pcode_op):
            return self._make_tracked_return_storage_value(
                target_storage,
                producer_op=pcode_op,
            )
        return None

    def _pcode_op_affects_tracked_storage(
        self,
        pcode_op,
        target_storage: Optional[StorageInfo],
        tracer: Optional[PcodeTracer],
        current_function=None,
    ) -> bool:
        if pcode_op is None or target_storage is None or tracer is None:
            return False

        output = getattr(pcode_op, "getOutput", lambda: None)()
        if output is not None:
            output_storage = None
            try:
                output_storage = tracer._get_storage_info_from_varnode(output)
            except Exception:
                output_storage = None
            if output_storage is not None and self._storages_overlap_for_return_recovery(
                output_storage,
                target_storage,
            ):
                return True

        if not self._is_pcode_call_op(pcode_op):
            return False

        for return_storage in self._get_implicit_return_target_storages(current_function, tracer):
            if self._storages_overlap_for_return_recovery(target_storage, return_storage):
                return True
        return False

    def _resolve_implicit_return_tracked_values(
        self,
        return_op,
        tracer: PcodeTracer,
        condition_tracker: ConditionTracker,
        current_function=None,
        block_path=None,
    ) -> List[_TrackedReturnValue]:
        search_blocks = None
        if block_path:
            search_blocks = list(block_path)
        else:
            return_parent = getattr(return_op, "getParent", lambda: None)()
            return_block = condition_tracker.get_block_by_hash(return_parent)
            if return_block is None:
                return []
            search_blocks = [return_block]

        target_storages = self._get_implicit_return_target_storages(current_function, tracer)
        if not target_storages:
            return []

        tracked_values: List[_TrackedReturnValue] = []
        for target_storage in target_storages:
            candidate: Optional[_TrackedReturnValue] = None
            for block_info in search_blocks:
                for pcode_op in getattr(block_info, "pcode_ops", []) or []:
                    if self._pcode_ops_match(pcode_op, return_op):
                        break
                    if not self._pcode_op_affects_tracked_storage(
                        pcode_op,
                        target_storage,
                        tracer,
                        current_function=current_function,
                    ):
                        continue
                    candidate = self._make_tracked_return_value_from_affecting_op(
                        pcode_op,
                        target_storage,
                        tracer,
                    )
            if candidate is not None:
                tracked_values.append(candidate)

        tracked_values = self._deduplicate_tracked_return_values(tracked_values)
        if tracked_values and self.debug:
            for tracked in tracked_values:
                if tracked.producer_op is not None:
                    self._debug_print(
                        "Implicit return source matched to terminal producer "
                        f"{self._pcode_op_debug_name(tracked.producer_op)}"
                    )
                elif tracked.varnode is not None:
                    self._debug_print(
                        f"Implicit return source matched to block-local output {tracked.varnode}"
                    )
        return tracked_values

    def _build_return_tracking_targets(
        self,
        return_op,
        *,
        tracer: Optional[PcodeTracer],
        current_function,
    ) -> List[_TrackedReturnValue]:
        tracked_values: List[_TrackedReturnValue] = []

        explicit_inputs = self._coerce_optional_int(
            getattr(return_op, "getNumInputs", lambda: 0)()
        )
        explicit_inputs = explicit_inputs if explicit_inputs is not None else 0
        if explicit_inputs >= 2:
            try:
                tracked_values.append(
                    self._make_tracked_return_value(return_op.getInput(1), tracer)
                )
            except Exception:
                pass

        if not tracked_values and tracer is not None:
            for storage in self._get_implicit_return_target_storages(current_function, tracer):
                tracked_values.append(self._make_tracked_return_storage_value(storage))

        return self._deduplicate_tracked_return_values(tracked_values)

    def _call_output_proves_wrapper_return(
        self,
        linear_ops: List[Any],
        candidate_index: int,
        return_op,
        *,
        tracer: Optional[PcodeTracer],
        condition_tracker: Optional[ConditionTracker],
        current_function,
        block_path=None,
        path_conditions: Optional[List[Condition]] = None,
    ) -> bool:
        tracked_values = self._build_return_tracking_targets(
            return_op,
            tracer=tracer,
            current_function=current_function,
        )
        if not tracked_values:
            if self.debug:
                self._debug_print(
                    "Wrapper provenance failed: no return tracking targets were available"
                )
            return False

        for pcode_op in reversed(linear_ops[candidate_index + 1:-1]):
            tracked_values = self._rewrite_tracked_return_values_for_op(
                tracked_values,
                pcode_op,
                tracer=tracer,
                condition_tracker=condition_tracker,
                path_conditions=path_conditions,
                current_function=current_function,
            )
            if not tracked_values:
                if self.debug:
                    self._debug_print(
                        "Wrapper provenance rejected due to intervening op "
                        f"{self._pcode_op_debug_name(pcode_op)}"
                    )
                return False

        return self._tracked_values_match_call_output(
            tracked_values,
            linear_ops[candidate_index],
            tracer=tracer,
            current_function=current_function,
        )

    def _rewrite_tracked_return_values_for_op(
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
            updated = self._rewrite_single_tracked_return_value_for_op(
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
        return self._deduplicate_tracked_return_values(rewritten)

    def _rewrite_single_tracked_return_value_for_op(
        self,
        tracked: _TrackedReturnValue,
        pcode_op,
        *,
        tracer: Optional[PcodeTracer],
        condition_tracker: Optional[ConditionTracker],
        path_conditions: Optional[List[Condition]] = None,
        current_function=None,
    ) -> Optional[List[_TrackedReturnValue]]:
        if not self._tracked_return_value_is_affected_by_op(
            tracked,
            pcode_op,
            tracer=tracer,
            current_function=current_function,
        ):
            return [tracked]

        opcode = self._get_pcode_opcode(pcode_op)
        if opcode in _PCODE_CALL_OPCODES:
            return None

        if opcode in _PCODE_VALUE_PASSTHROUGH_OPCODES:
            propagated = self._propagate_passthrough_input_from_op(pcode_op, tracer)
            return propagated if propagated else None

        if opcode == _PCODE_OPCODE_BY_MNEMONIC["MULTIEQUAL"]:
            propagated = self._propagate_multiequal_input_for_return_path(
                pcode_op,
                tracer=tracer,
                condition_tracker=condition_tracker,
                path_conditions=path_conditions,
            )
            return propagated if propagated else None

        if opcode == _PCODE_OPCODE_BY_MNEMONIC["INDIRECT"]:
            propagated = self._propagate_indirect_return_effect(
                tracked,
                pcode_op,
                tracer=tracer,
            )
            return propagated if propagated else None

        return None

    def _tracked_return_value_is_affected_by_op(
        self,
        tracked: _TrackedReturnValue,
        pcode_op,
        *,
        tracer: Optional[PcodeTracer],
        current_function=None,
    ) -> bool:
        output = getattr(pcode_op, "getOutput", lambda: None)()
        output_storage = None
        if tracer is not None and output is not None:
            try:
                output_storage = tracer._get_storage_info_from_varnode(output)
            except Exception:
                output_storage = None

        if tracked.varnode is not None and output is not None and self._varnodes_may_alias(tracked.varnode, output):
            return True

        tracked_storage = tracked.storage
        if tracked_storage is None and tracked.varnode is not None and tracer is not None:
            try:
                tracked_storage = tracer._get_storage_info_from_varnode(tracked.varnode)
            except Exception:
                tracked_storage = None

        if tracked_storage is not None and output_storage is not None:
            if self._storages_overlap_for_return_recovery(tracked_storage, output_storage):
                return True

        if output is None and self._is_pcode_call_op(pcode_op) and tracked_storage is not None and tracer is not None:
            for return_storage in self._get_implicit_return_target_storages(current_function, tracer):
                if self._storages_overlap_for_return_recovery(tracked_storage, return_storage):
                    return True
        return False

    def _propagate_passthrough_input_from_op(
        self,
        pcode_op,
        tracer: Optional[PcodeTracer],
    ) -> List[_TrackedReturnValue]:
        input_varnode = getattr(pcode_op, "getInput", lambda _idx: None)(0)
        if input_varnode is None:
            return []
        return [self._make_tracked_return_value(input_varnode, tracer)]

    def _propagate_multiequal_input_for_return_path(
        self,
        pcode_op,
        *,
        tracer: Optional[PcodeTracer],
        condition_tracker: Optional[ConditionTracker],
        path_conditions: Optional[List[Condition]] = None,
    ) -> List[_TrackedReturnValue]:
        if condition_tracker is None:
            return []
        parent = getattr(pcode_op, "getParent", lambda: None)()
        predecessor = None
        normalized_conditions = list(path_conditions or [])
        if parent is not None:
            get_in_size = getattr(parent, "getInSize", None)
            get_in = getattr(parent, "getIn", None)
            if callable(get_in_size) and callable(get_in):
                current_keys = self._build_condition_signature_set(normalized_conditions)
                best_score = None
                try:
                    for index in range(int(get_in_size())):
                        incoming = get_in(index)
                        score = self._score_multiequal_incoming_for_return_path(
                            incoming,
                            None,
                            condition_tracker,
                            current_keys,
                        )
                        if best_score is None or score > best_score[0]:
                            best_score = (score, incoming)
                except Exception:
                    best_score = None
                if best_score is not None:
                    predecessor = best_score[1]

        selected = self._select_multiequal_input_for_return_path(
            multiequal_op=pcode_op,
            predecessor=predecessor,
            condition_tracker=condition_tracker,
            path_conditions=normalized_conditions,
        )
        if selected is None:
            try:
                selected = pcode_op.getInput(0)
            except Exception:
                selected = None
        if selected is None:
            return []
        return [self._make_tracked_return_value(selected, tracer)]

    def _is_zero_constant_varnode(self, varnode) -> bool:
        if varnode is None:
            return False
        is_constant = getattr(varnode, "isConstant", None)
        if callable(is_constant):
            try:
                if bool(is_constant()):
                    return int(varnode.getOffset()) == 0
            except Exception:
                pass
        address = getattr(varnode, "getAddress", lambda: None)()
        if address is not None:
            is_constant_address = getattr(address, "isConstantAddress", None)
            if callable(is_constant_address):
                try:
                    if bool(is_constant_address()):
                        return int(address.getOffset()) == 0
                except Exception:
                    pass
        return False

    def _propagate_indirect_return_effect(
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
        if self._is_zero_constant_varnode(base_input):
            return [tracked]

        if base_input is None:
            return []
        return [self._make_tracked_return_value(base_input, tracer)]

    def _tracked_values_match_call_output(
        self,
        tracked_values: List[_TrackedReturnValue],
        call_op,
        *,
        tracer: Optional[PcodeTracer],
        current_function=None,
    ) -> bool:
        call_output = getattr(call_op, "getOutput", lambda: None)()
        call_output_storage = None
        if tracer is not None and call_output is not None:
            try:
                call_output_storage = tracer._get_storage_info_from_varnode(call_output)
            except Exception:
                call_output_storage = None

        if call_output is None:
            if tracer is None:
                return False
            return_storages = self._get_implicit_return_target_storages(current_function, tracer)
            for tracked in tracked_values:
                tracked_storage = tracked.storage
                if tracked_storage is None and tracked.varnode is not None:
                    try:
                        tracked_storage = tracer._get_storage_info_from_varnode(tracked.varnode)
                    except Exception:
                        tracked_storage = None
                if tracked_storage is None:
                    continue
                if any(
                    self._storages_overlap_for_return_recovery(tracked_storage, return_storage)
                    for return_storage in return_storages
                ):
                    return True
            return False

        for tracked in tracked_values:
            if tracked.varnode is not None and self._varnodes_may_alias(tracked.varnode, call_output):
                return True
            tracked_storage = tracked.storage
            if tracked_storage is None and tracked.varnode is not None and tracer is not None:
                try:
                    tracked_storage = tracer._get_storage_info_from_varnode(tracked.varnode)
                except Exception:
                    tracked_storage = None
            if tracked_storage is not None and call_output_storage is not None:
                if self._storages_overlap_for_return_recovery(tracked_storage, call_output_storage):
                    return True
        return False

    def _parameter_storages_overlap_for_passthrough(
        self,
        caller_storage: Optional[Dict],
        callee_storage: Optional[Dict],
    ) -> bool:
        caller = self._coerce_wrapper_storage_info(caller_storage)
        callee = self._coerce_wrapper_storage_info(callee_storage)
        if caller is None or callee is None:
            return False
        if not caller.is_register or not callee.is_register:
            return False
        try:
            return (
                caller.shares_base_register_with(callee)
                and caller.bit_range_overlaps_with(callee)
            )
        except Exception:
            return False

    def _parameter_storages_match_for_passthrough(
        self,
        caller_storage: Optional[Dict],
        callee_storage: Optional[Dict],
    ) -> bool:
        caller = self._coerce_wrapper_storage_info(caller_storage)
        callee = self._coerce_wrapper_storage_info(callee_storage)
        if caller is None or callee is None:
            return False
        if not caller.is_register or not callee.is_register:
            return False
        if not caller.shares_base_register_with(callee):
            return False
        if int(caller.bit_offset_in_base or 0) != int(callee.bit_offset_in_base or 0):
            return False
        caller_bits = int(caller.size_bits or (caller.size or 0) * 8)
        callee_bits = int(callee.size_bits or (callee.size or 0) * 8)
        return caller_bits == callee_bits and caller_bits > 0

    def _coerce_wrapper_storage_info(self, storage: Optional[object]) -> Optional[StorageInfo]:
        if storage is None:
            return None
        if isinstance(storage, StorageInfo):
            return storage
        if isinstance(storage, dict):
            try:
                return StorageInfo(
                    is_register=bool(storage.get("is_register", False)),
                    space_name=str(storage.get("space_name", "")),
                    space_id=self._coerce_optional_int(storage.get("space_id")),
                    offset=int(storage.get("offset", 0)),
                    size=int(storage.get("size", 0)),
                    size_bits=int(storage.get("size_bits", 0)),
                    register_name=storage.get("register_name"),
                    register_offset=self._coerce_optional_int(storage.get("register_offset")),
                    register_size=self._coerce_optional_int(storage.get("register_size")),
                    register_size_bits=self._coerce_optional_int(storage.get("register_size_bits")),
                    base_register_name=storage.get("base_register_name"),
                    base_register_offset=int(storage.get("base_register_offset", 0)),
                    base_register_size=int(storage.get("base_register_size", 0)),
                    base_register_size_bits=int(storage.get("base_register_size_bits", 0)),
                    bit_offset_in_base=int(storage.get("bit_offset_in_base", 0)),
                    is_stack_pointer=bool(storage.get("is_stack_pointer", False)),
                    is_frame_pointer=bool(storage.get("is_frame_pointer", False)),
                )
            except Exception:
                return None
        return None

    def _parameter_descriptor_quality(self, parameters: Optional[List[Dict]]) -> Tuple[int, int, int, int]:
        params = list(parameters or [])
        return (
            len(params),
            sum(1 for param in params if param.get("storage")),
            sum(1 for param in params if param.get("data_type")),
            sum(1 for param in params if int(param.get("size", 0) or 0) > 0),
        )

    def _choose_richer_parameter_descriptors(
        self,
        cached_parameters: Optional[List[Dict]],
        fresh_parameters: Optional[List[Dict]],
    ) -> List[Dict]:
        cached = list(cached_parameters or [])
        fresh = list(fresh_parameters or [])
        if self._parameter_descriptor_quality(fresh) > self._parameter_descriptor_quality(cached):
            return fresh
        return cached

    def _coerce_runtime_target_ref(self, target) -> Optional[CallTargetRef]:
        return coerce_call_target_ref(target)

    def _function_cache_key(self, function) -> Optional[Tuple[Any, ...]]:
        if function is None:
            return None
        try:
            return (str(function.getEntryPoint()),)
        except Exception:
            return None

    def _normalize_bound_parameter_values(
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
            normalized[normalized_index] = self._clone_expression(expr)
        return normalized

    def _bound_parameter_values_from_args(
        self,
        args: Optional[Sequence[Expression]],
    ) -> Dict[int, Expression]:
        return self._normalize_bound_parameter_values(
            {
                index: expr
                for index, expr in enumerate(args or [])
                if expr is not None
            }
        )

    def _analysis_scope_key(
        self,
        target,
        bound_parameter_values: Optional[Dict[int, Expression]] = None,
    ) -> Tuple[Any, ...]:
        target_ref = self._coerce_runtime_target_ref(target)
        if target_ref is None and target is not None:
            try:
                if hasattr(target, "getEntryPoint"):
                    target_ref = CallTargetRef.from_function(target)
            except Exception:
                target_ref = None
        target_key = (
            self._target_active_key(target_ref)
            if target_ref is not None
            else self._function_cache_key(target)
        ) or ("unknown_target",)
        normalized_bound_parameter_values = self._normalize_bound_parameter_values(
            bound_parameter_values,
        )
        bound_signature = tuple(
            (
                int(index),
                ConditionNormalizer.expression_signature(
                    expr,
                    include_memory_read_order=False,
                ),
            )
            for index, expr in sorted(normalized_bound_parameter_values.items())
        )
        return ("analysis_scope", target_key, bound_signature)

    def _target_active_key(self, target_ref: Optional[CallTargetRef]) -> Optional[Tuple[Any, ...]]:
        if target_ref is None:
            return None
        return target_ref.analysis_key()

    def _extend_active_functions(
        self,
        active_functions: Optional[Set[Tuple[Any, ...]]],
        target_ref: Optional[CallTargetRef],
    ) -> Set[Tuple[Any, ...]]:
        scoped = set(active_functions or set())
        active_key = self._target_active_key(target_ref)
        if active_key is not None:
            scoped.add(active_key)
        return scoped

    def _resolve_target_function(self, target) -> Optional[Any]:
        target_ref = self._coerce_runtime_target_ref(target)
        if target_ref is None or self.program is None:
            return None
        if target_ref.function_obj is not None:
            return target_ref.function_obj
        if target_ref.entry_offset is not None:
            return self._resolve_function_from_program_offset(target_ref.entry_offset)
        if target_ref.address_offset is not None:
            return self._resolve_function_from_program_offset(target_ref.address_offset)
        if target_ref.function_name:
            return self._find_function_by_name(target_ref.function_name)
        return None

    def _get_freshest_callee_parameters(self, target) -> List[Dict]:
        callee = self._resolve_target_function(target)
        if callee is None:
            return []

        callee_key = self._function_cache_key(callee)
        if callee_key is None:
            return []
        cached_parameters = self._effect_summary_parameter_cache.get(callee_key)

        results = self._decompile_function(callee, timeout=60)
        if results is None:
            return list(cached_parameters or [])

        callee_high = results.getHighFunction()
        if callee_high is None:
            return list(cached_parameters or [])

        fresh_parameters = self._collect_parameters(callee_high)
        merged_parameters = self._choose_richer_parameter_descriptors(
            cached_parameters,
            fresh_parameters,
        )
        self._effect_summary_parameter_cache[callee_key] = list(merged_parameters)
        return list(merged_parameters)

    def _augment_parameters_with_implicit_passthrough(
        self,
        parameters: List[Dict],
        tracer: Any,
        active_functions: Set[Tuple[Any, ...]],
    ) -> List[Dict]:
        augmented = [dict(param) for param in (parameters or [])]
        changed = False

        try:
            pcode_ops = list(tracer.get_all_pcode_ops())
        except Exception:
            return augmented

        for op in pcode_ops:
            try:
                if op.getMnemonic() not in {"CALL", "CALLIND"} or op.getNumInputs() < 1:
                    continue
            except Exception:
                continue

            target_ref = _resolve_call_target_ref(tracer, op)
            if target_ref is None:
                continue
            active_key = self._target_active_key(target_ref)
            if target_ref.is_unknown():
                continue
            if active_key is not None and active_key in active_functions:
                continue

            explicit_count = max(0, int(op.getNumInputs()) - 1)
            callee_parameters = self._get_freshest_callee_parameters(target_ref)
            if len(callee_parameters) <= explicit_count:
                continue

            for callee_param in callee_parameters[explicit_count:]:
                callee_storage = self._coerce_wrapper_storage_info(callee_param.get("storage"))
                if callee_storage is None or not callee_storage.is_register:
                    continue
                if any(
                    self._parameter_storages_overlap_for_passthrough(
                        existing.get("storage"),
                        callee_param.get("storage"),
                    )
                    for existing in augmented
                ):
                    continue
                if not self._should_synthesize_implicit_passthrough_for_call(
                    tracer,
                    op,
                    callee_storage,
                ):
                    continue
                augmented.append(
                    self._synthesize_implicit_passthrough_parameter(
                        augmented,
                        callee_param,
                        callee_storage,
                    )
                )
                changed = True

        if changed:
            augmented.sort(key=lambda param: int(param.get("index", 1 << 20)))
        return augmented

    def _should_synthesize_implicit_passthrough_for_call(
        self,
        tracer: PcodeTracer,
        call_op,
        target_storage: StorageInfo,
    ) -> bool:
        if self._has_non_parameter_symbol_for_storage(tracer, target_storage):
            return False
        if self._is_passthrough_storage_live_in_for_call(tracer, call_op, target_storage):
            return True
        return True

    def _is_passthrough_storage_live_in_for_call(
        self,
        tracer: PcodeTracer,
        call_op,
        target_storage: StorageInfo,
    ) -> bool:
        get_order_key = getattr(tracer, "_get_op_order_key", None)
        if not callable(get_order_key):
            return True

        call_order = self._coerce_order_key(get_order_key(call_op))
        if call_order is None:
            return True

        for op in tracer.get_all_pcode_ops():
            op_order = self._coerce_order_key(get_order_key(op))
            if op_order is None:
                continue
            if op_order >= call_order:
                continue
            output = getattr(op, "getOutput", lambda: None)()
            if output is None:
                continue
            output_storage = tracer._get_storage_info_from_varnode(output)
            if output_storage is None or not getattr(output_storage, "is_register", False):
                continue
            try:
                same_base = output_storage.shares_base_register_with(target_storage)
                overlaps = output_storage.bit_range_overlaps_with(target_storage)
            except Exception:
                same_base = False
                overlaps = False
            if same_base and overlaps:
                return False
        return True

    def _has_non_parameter_symbol_for_storage(
        self,
        tracer: PcodeTracer,
        target_storage: StorageInfo,
    ) -> bool:
        high_function = getattr(tracer, "high_function", None)
        if high_function is None:
            return False
        try:
            local_map = high_function.getLocalSymbolMap()
        except Exception:
            return False
        if local_map is None:
            return False

        for sym in local_map.getSymbols() or []:
            try:
                if sym.isParameter():
                    continue
            except Exception:
                continue
            candidate_storage = self._coerce_wrapper_storage_info(self._get_storage_info(sym))
            if candidate_storage is None or not candidate_storage.is_register:
                continue
            try:
                same_base = candidate_storage.shares_base_register_with(target_storage)
                overlaps = candidate_storage.bit_range_overlaps_with(target_storage)
            except Exception:
                same_base = False
                overlaps = False
            if same_base and overlaps:
                return True
        return False

    def _coerce_order_key(self, value: object) -> Optional[int]:
        if value is None:
            return None
        if isinstance(value, bool):
            return int(value)
        if isinstance(value, int):
            return value
        try:
            return int(cast(Any, value))
        except Exception:
            return None

    def _synthesize_implicit_passthrough_parameter(
        self,
        current_parameters: List[Dict],
        callee_param: Dict,
        callee_storage: StorageInfo,
    ) -> Dict:
        used_names = {param.get("name") for param in current_parameters if param.get("name")}
        next_index = max((int(param.get("index", -1)) for param in current_parameters), default=-1) + 1
        suggested_name = callee_param.get("name") or f"param_{next_index + 1}"
        if suggested_name in used_names:
            suggested_name = f"param_{next_index + 1}"

        return {
            "name": suggested_name,
            "index": next_index,
            "size": callee_param.get("size") or callee_storage.size or 0,
            "data_type": callee_param.get("data_type"),
            "data_type_obj": callee_param.get("data_type_obj"),
            "is_signed": callee_param.get("is_signed", True),
            "storage": callee_storage.to_dict(),
            "implicit_passthrough": True,
        }

    def _clone_expression(self, expr: Expression) -> Expression:
        return expr.clone_with(operands=[self._clone_expression(op) for op in expr.operands])

    def _make_tracer(
        self,
        high_function,
        *,
        bound_parameter_values: Optional[Dict[int, Expression]] = None,
    ) -> PcodeTracer:
        try:
            return PcodeTracer(
                self.program,
                high_function,
                debug=self.debug,
                bound_parameter_values=bound_parameter_values,
            )
        except TypeError:
            return PcodeTracer(
                self.program,
                high_function,
                debug=self.debug,
            )

    def _invoke_build_effect_summary(
        self,
        function,
        high_function,
        tracer: PcodeTracer,
        condition_tracker: ConditionTracker,
        parameters: List[Dict],
        active_functions: Set[Tuple[Any, ...]],
        *,
        bound_parameter_values: Optional[Dict[int, Expression]] = None,
    ):
        try:
            return self._build_effect_summary(
                function,
                high_function,
                tracer,
                condition_tracker,
                parameters,
                active_functions=active_functions,
                bound_parameter_values=bound_parameter_values,
            )
        except TypeError:
            return self._build_effect_summary(
                function,
                high_function,
                tracer,
                condition_tracker,
                parameters,
                active_functions=active_functions,
            )

    def _invoke_get_or_analyze_call_target(
        self,
        target,
        active_functions: Set[Tuple[Any, ...]],
        *,
        minimum_param_count: int = 0,
        args: Optional[Sequence[Expression]] = None,
    ) -> Optional[FunctionReturnAnalysis]:
        try:
            return self._get_or_analyze_call_target(
                target,
                active_functions,
                minimum_param_count=minimum_param_count,
                args=args,
            )
        except TypeError:
            try:
                return self._get_or_analyze_call_target(
                    target,
                    active_functions,
                    minimum_param_count=minimum_param_count,
                )
            except TypeError:
                return self._get_or_analyze_call_target(
                    target,
                    active_functions,
                )

    def _build_effect_summary(
        self,
        function,
        high_function,
        tracer: PcodeTracer,
        condition_tracker: ConditionTracker,
        parameters: List[Dict],
        active_functions: Set[Tuple[Any, ...]],
        bound_parameter_values: Optional[Dict[int, Expression]] = None,
    ):
        function_cache_key = self._function_cache_key(function)
        if function_cache_key is None:
            return None
        self._effect_summary_parameter_cache[function_cache_key] = list(parameters)
        summary_cache_key = self._analysis_scope_key(
            function,
            bound_parameter_values,
        )
        cached = self._effect_summary_cache.get(summary_cache_key)
        if cached is not None:
            return cached

        def summarize_call(target, args):
            target_ref = self._coerce_runtime_target_ref(target)
            if target_ref is None:
                return None
            active_key = self._target_active_key(target_ref)
            if active_key is not None and active_key in active_functions:
                return None
            callee = self._resolve_target_function(target_ref)
            if callee is None:
                return None
            callee_scope_key = self._analysis_scope_key(
                callee,
                self._bound_parameter_values_from_args(args),
            )
            if callee_scope_key is None:
                return None
            cached_callee = self._effect_summary_cache.get(callee_scope_key)
            if cached_callee is not None:
                return cached_callee

            decompiler = self._get_decompiler()
            results = decompiler.decompileFunction(callee, 60, None)
            if not results.decompileCompleted():
                return None
            callee_high = results.getHighFunction()
            if callee_high is None:
                return None

            callee_bound_parameter_values = self._bound_parameter_values_from_args(args)
            callee_tracer = self._make_tracer(
                callee_high,
                bound_parameter_values=callee_bound_parameter_values,
            )
            callee_tracer.record_deferred_call = self._make_deferred_call_recorder(callee)
            callee_tracker = ConditionTracker(callee_tracer)
            callee_tracer.condition_tracker = callee_tracker
            from .phi_resolver import PhiHandler

            callee_phi_handler = PhiHandler(callee_tracer, callee_tracker)
            callee_tracer.phi_handler = callee_phi_handler
            callee_tracker.build()
            callee_parameters = self._collect_parameters(callee_high)
            callee_function_cache_key = self._function_cache_key(callee)
            if callee_function_cache_key is not None:
                self._effect_summary_parameter_cache[callee_function_cache_key] = list(callee_parameters)
            image_base = None
            try:
                image_base = self.program.getImageBase().getOffset()
            except Exception:
                image_base = None
            callee_tracker.refine_branch_conditions(
                call_resolver=self._make_call_resolver(
                    self._extend_active_functions(active_functions, target_ref),
                    callee,
                ),
                parameters=callee_parameters,
                resolve_callee_parameters=self._get_freshest_callee_parameters,
                read_memory_value=self._read_memory_value,
                image_base=image_base,
            )
            summary = self._invoke_build_effect_summary(
                callee,
                callee_high,
                callee_tracer,
                callee_tracker,
                callee_parameters,
                self._extend_active_functions(active_functions, target_ref),
                bound_parameter_values=callee_bound_parameter_values,
            )
            return summary

        def resolve_callee_parameters(target):
            return self._get_freshest_callee_parameters(target)

        current_target = CallTargetRef.from_function(function)
        image_base = None
        try:
            image_base = self.program.getImageBase().getOffset()
        except Exception:
            image_base = None
        summary = summarize_store_effects(
            condition_tracker.block_by_index.values(),
            tracer,
            condition_tracker,
            parameters,
            direct_call_summary=summarize_call,
            direct_call_expander=self._make_call_resolver(
                self._extend_active_functions(active_functions, current_target),
                function,
            ),
            resolve_callee_parameters=resolve_callee_parameters,
            read_memory_value=self._read_memory_value,
            image_base=image_base,
            debug=self.debug,
        )
        self._effect_summary_cache[summary_cache_key] = summary
        return summary

    def _make_call_resolver(self, active_functions: Set[Tuple[Any, ...]], current_function=None):
        def resolve_call(target, args):
            return self._resolve_call_expansions(target, args, active_functions, current_function)

        return resolve_call

    def _resolve_call_expansions(
        self,
        target,
        args: List[Expression],
        active_functions: Set[Tuple[Any, ...]],
        current_function=None,
    ):
        from ..transform.expander import ExpandedValue

        target_ref = self._coerce_runtime_target_ref(target)
        if target_ref is None:
            return None
        target_label = target_ref.display_name()

        if target_ref.is_code_address() and target_ref.address_offset is not None:
            return self._resolve_local_code_target_expansions(
                target_ref.address_offset,
                active_functions,
                current_function,
                args=args,
            )

        active_key = self._target_active_key(target_ref)
        if active_key is not None and active_key in active_functions:
            self._debug_print(f"Skipping recursive call expansion for '{target_label}'")
            return None

        analysis = self._invoke_get_or_analyze_call_target(
            target_ref,
            active_functions,
            args=args,
        )
        if analysis is None:
            self._debug_print(f"Call expansion skipped for '{target_label}': analysis unavailable")
            return None

        if len(args) < len(analysis.parameters):
            self._debug_print(
                f"Call expansion skipped for '{target_label}': "
                f"expected {len(analysis.parameters)} args, got {len(args)}"
            )
            return None

        specialized = self._specialize_call_analysis(analysis, args)
        if specialized.deferred_calls:
            self._apply_bounded_call_refinement(
                specialized,
                active_functions,
                analysis.function_ref,
            )
            self._merge_deferred_calls_into_current_analysis(specialized.deferred_calls)

        preserve_non_exhaustive_returns = bool(
            specialized.deferred_calls
            or specialized.unknown_event_count
            or specialized.incomplete_control_flow
        )

        expanded = []
        rejected_returns = 0
        for ret in specialized.returns:
            simplified_conditions = ConditionSimplifier.simplify_conditions_object_centric(
                ret.conditions
            )
            contradictory_conditions = ConditionSimplifier.object_centric_is_contradiction(
                simplified_conditions
            )
            if contradictory_conditions and not preserve_non_exhaustive_returns:
                rejected_returns += 1
                continue

            effective_conditions = (
                list(ret.conditions)
                if contradictory_conditions and preserve_non_exhaustive_returns
                else simplified_conditions
            )
            if contradictory_conditions and preserve_non_exhaustive_returns:
                effective_value = ret.value
            else:
                reduced_value = _reduce_expression_under_conditions(
                    ret.value,
                    effective_conditions,
                )
                effective_value = reduced_value if reduced_value is not None else ret.value

            if not self._call_summary_is_safe(effective_value, effective_conditions, args):
                self._debug_print(
                    f"Call expansion rejected for '{target_label}': "
                    "summary not safe enough for inlining"
                )
                rejected_returns += 1
                continue

            # Keep safe return candidates even if others are rejected.
            expanded.append(
                ExpandedValue(
                    value=effective_value,
                    conditions=effective_conditions,
                )
            )

        if not expanded and rejected_returns:
            self._debug_print(
                f"Call expansion for '{target_label}' dropped all "
                f"({rejected_returns}) inlining candidates; keeping unresolved"
            )
            return None
        return expanded

    def _decompile_function(self, function, timeout: int = 60):
        try:
            decompiler = self._get_decompiler()
            results = decompiler.decompileFunction(function, timeout, None)
            if not results.decompileCompleted():
                return None
            return results
        except Exception:
            return None
    def _resolve_local_code_target_expansions(
        self,
        address_value: int,
        active_functions: Set[Tuple[Any, ...]],
        current_function=None,
        args: Optional[List[Expression]] = None,
    ):
        from ..transform.expander import ExpandedValue

        args = list(args or [])
        cache_key = self._local_target_cache_key(address_value, args)
        if cache_key in self._local_target_cache:
            return self._local_target_cache[cache_key]

        try:
            default_space = self.program.getAddressFactory().getDefaultAddressSpace()
            addr = default_space.getAddress(address_value)
        except Exception:
            self._debug_print(f"Local target resolution failed: invalid address 0x{address_value:x}")
            self._local_target_cache[cache_key] = None
            return None

        function_manager = self.program.getFunctionManager()
        containing = function_manager.getFunctionContaining(addr)
        if containing is None and current_function is not None:
            try:
                body = current_function.getBody()
                body_contains = body is not None and body.contains(addr)
                if not body_contains and body is not None:
                    min_addr = body.getMinAddress()
                    max_addr = body.getMaxAddress()
                    if min_addr is not None and max_addr is not None:
                        try:
                            body_contains = (
                                min_addr.getOffset() <= addr.getOffset() <= max_addr.getOffset()
                            )
                        except Exception:
                            body_contains = False
                if body_contains:
                    containing = current_function
                    self._debug_print(
                        f"Local target {addr} falling back to current function '{current_function.getName()}'"
                    )
            except Exception:
                containing = current_function
                self._debug_print(
                    f"Local target {addr} falling back to current function "
                    f"'{current_function.getName()}' after body check failure"
                )
        if containing is None and current_function is not None:
            containing = current_function
            self._debug_print(
                f"Local target {addr} using current function '{current_function.getName()}' as fallback"
            )
        if containing is None:
            self._debug_print(f"Local target resolution failed: no containing function for 0x{address_value:x}")
            self._local_target_cache[cache_key] = None
            return None

        decompiler = self._get_decompiler()
        results = decompiler.decompileFunction(containing, 60, None)
        if not results.decompileCompleted():
            self._debug_print(
                f"Local target resolution failed: decompilation incomplete for 0x{address_value:x}"
            )
            self._local_target_cache[cache_key] = None
            return None
        high_function = results.getHighFunction()
        if high_function is None:
            self._debug_print(f"Local target resolution failed: HighFunction unavailable for 0x{address_value:x}")
            self._local_target_cache[cache_key] = None
            return None

        tracer = self._make_tracer(
            high_function,
            bound_parameter_values={
                index: self._clone_expression(arg)
                for index, arg in enumerate(args or [])
                if arg is not None
            },
        )
        tracer.record_deferred_call = self._make_deferred_call_recorder(containing)
        expanded = self._expand_linear_code_target(addr, tracer, containing)
        if expanded:
            expanded = self._specialize_local_target_expansions(expanded, tracer, args)
        self._local_target_cache[cache_key] = expanded
        return expanded

    def _local_target_cache_key(
        self,
        address_value: int,
        args: List[Expression],
    ) -> Tuple[object, ...]:
        return (
            "local_target",
            int(address_value),
            tuple(
                arg.structural_key(budget=256)
                for arg in (args or [])
                if arg is not None
            ),
        )

    def _specialize_local_target_expansions(
        self,
        expanded: List[Any],
        tracer: PcodeTracer,
        args: List[Expression],
    ) -> List[Any]:
        if not expanded or not getattr(tracer, "_parameter_descriptors", None):
            return expanded
        if not args:
            return expanded
        owner_scope: Dict[str, Optional[int]] = {}
        get_owner_scope = getattr(tracer, "get_parameter_owner_scope", None)
        if callable(get_owner_scope):
            try:
                maybe_scope = get_owner_scope() or {}
            except Exception:
                maybe_scope = {}
            if isinstance(maybe_scope, dict):
                owner_scope = maybe_scope

        callee_params = [
            {
                "name": descriptor.name,
                "index": descriptor.index,
                "size": descriptor.size_bytes,
                "data_type": descriptor.data_type,
                "is_signed": descriptor.is_signed,
                **owner_scope,
            }
            for descriptor in getattr(tracer, "_parameter_descriptors", [])
        ]
        if not callee_params:
            return expanded

        replacements = _build_parameter_replacements(callee_params, args)
        specialized: List[Any] = []
        for item in expanded:
            value = substitute_expression(item.value, replacements, callee_params)
            conditions = [
                substitute_condition(cond, replacements, callee_params)
                for cond in (item.conditions or [])
            ]
            specialized.append(
                item.__class__(
                    value=value,
                    conditions=conditions,
                )
            )
        return specialized

    def _expand_linear_code_target(self, addr, tracer, current_function=None):
        from ..transform.expander import ExpandedValue

        instruction = self._get_instruction_with_fallback(addr)
        if instruction is None:
            self._debug_print(f"Local target resolution failed: no instruction at {addr}")
            return None

        self._debug_print(f"Attempting linear local target expansion from {addr}")
        max_steps = 16
        visited_offsets: Set[int] = set()
        local_values: Dict[Tuple[str, int, int], Expression] = {}
        local_storages: Dict[Tuple[str, int, int], Any] = {}
        local_memory: Dict[Tuple[StructuralKey, int], Expression] = {}

        for _ in range(max_steps):
            typed_instruction = cast(Any, instruction)
            try:
                current_offset = typed_instruction.getAddress().getOffset()
            except Exception:
                current_offset = None
            if current_offset is not None:
                if current_offset in visited_offsets:
                    self._debug_print(
                        f"Local target resolution aborted at {typed_instruction.getAddress()}: cycle detected"
                    )
                    return None
                visited_offsets.add(current_offset)

            try:
                pcode_ops = typed_instruction.getPcode()
            except Exception:
                self._debug_print(f"Local target resolution failed: unable to get pcode at {typed_instruction.getAddress()}")
                return None

            branch_target = None
            for pcode_op in pcode_ops:
                mnemonic = pcode_op.getMnemonic()
                if mnemonic == "RETURN":
                    value = self._resolve_local_return_expression(
                        pcode_op,
                        tracer,
                        local_values,
                        local_storages,
                        local_memory,
                        current_function,
                    )
                    self._debug_print(
                        f"Resolved local target {typed_instruction.getAddress()} to return expression {value.to_string()}"
                    )
                    return [ExpandedValue(value=value, conditions=[])]

                if mnemonic == "STORE":
                    self._apply_local_store_effect(
                        pcode_op,
                        tracer,
                        local_values,
                        local_storages,
                        local_memory,
                    )
                    continue

                if mnemonic == "BRANCH":
                    branch_target = self._resolve_local_branch_target(instruction)
                    if branch_target is None:
                        self._debug_print(
                            f"Local target resolution aborted at {typed_instruction.getAddress()}: "
                            "unresolved BRANCH target"
                        )
                        return None
                    continue

                if mnemonic in {"CALL", "CALLIND", "CBRANCH", "BRANCHIND", "MULTIEQUAL"}:
                    self._debug_print(
                        f"Local target resolution aborted at {typed_instruction.getAddress()}: unsupported {mnemonic}"
                    )
                    return None

                output = getattr(pcode_op, "getOutput", lambda: None)()
                if output is not None:
                    value = self._evaluate_local_pcode_expression(
                        pcode_op,
                        tracer,
                        local_values,
                        local_storages,
                        local_memory,
                    )
                    if value is not None:
                        output_key = self._local_varnode_key(output)
                        local_values[output_key] = value
                        try:
                            local_storages[output_key] = tracer._get_storage_info_from_varnode(output)
                        except Exception:
                            pass

            if branch_target is not None:
                self._debug_print(
                    f"Local target {typed_instruction.getAddress()} following BRANCH to {branch_target}"
                )
                instruction = self._get_instruction_with_fallback(branch_target)
                if instruction is None:
                    self._debug_print(
                        f"Local target resolution failed: no instruction at branch target {branch_target}"
                    )
                    return None
                continue

            next_instruction = typed_instruction.getNext()
            if next_instruction is None:
                break
            instruction = next_instruction

        self._debug_print(f"Local target resolution failed: no RETURN found from {addr}")
        return None

    def _local_varnode_key(self, varnode) -> Tuple[str, int, int]:
        try:
            addr = varnode.getAddress()
            return (addr.getAddressSpace().getName(), int(varnode.getOffset()), int(varnode.getSize()))
        except Exception:
            return ("synthetic", id(varnode), int(getattr(varnode, "getSize", lambda: 0)()))

    def _local_memory_key(self, addr_expr: Expression, size: int) -> Tuple[StructuralKey, int]:
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

    def _evaluate_local_varnode_expression(
        self,
        varnode,
        tracer,
        local_values: Dict[Tuple[str, int, int], Expression],
        local_storages: Dict[Tuple[str, int, int], Any],
        local_memory: Dict[Tuple[StructuralKey, int], Expression],
        visiting: Optional[Set[int]] = None,
    ) -> Expression:
        if varnode is None:
            return Expression.unknown("local_none")

        key = self._local_varnode_key(varnode)
        cached = local_values.get(key)
        if cached is not None:
            return cached

        aliased = self._lookup_local_alias_expression(varnode, tracer, local_values, local_storages)
        if aliased is not None:
            local_values[key] = aliased
            return aliased

        is_constant = getattr(varnode, "isConstant", None)
        if callable(is_constant) and is_constant():
            return Expression.constant(varnode.getOffset(), varnode.getSize())

        if visiting is None:
            visiting = set()
        marker = id(varnode)
        if marker in visiting:
            return Expression.unknown("local_cycle")
        visiting.add(marker)
        try:
            get_def = getattr(varnode, "getDef", None)
            def_op = get_def() if callable(get_def) else None
            if def_op is not None:
                evaluated = self._evaluate_local_pcode_expression(
                    def_op,
                    tracer,
                    local_values,
                    local_storages,
                    local_memory,
                    visiting,
                )
                if evaluated is not None:
                    local_values[key] = evaluated
                    return evaluated
        finally:
            visiting.discard(marker)

        return tracer.trace_varnode(varnode, use_cache=False)

    def _evaluate_local_pcode_expression(
        self,
        pcode_op,
        tracer,
        local_values: Dict[Tuple[str, int, int], Expression],
        local_storages: Dict[Tuple[str, int, int], Any],
        local_memory: Dict[Tuple[StructuralKey, int], Expression],
        visiting: Optional[Set[int]] = None,
    ) -> Optional[Expression]:
        mnemonic = pcode_op.getMnemonic()

        def _input(index: int) -> Expression:
            return self._evaluate_local_varnode_expression(
                pcode_op.getInput(index),
                tracer,
                local_values,
                local_storages,
                local_memory,
                visiting,
            )

        if mnemonic in {"COPY", "CAST"} and pcode_op.getNumInputs() >= 1:
            expr = _input(0)
            output = pcode_op.getOutput()
            if output is not None:
                expr = self._clone_expression(expr)
                expr.size = output.getSize()
            return expr

        binary_ops = {
            "INT_ADD", "INT_SUB", "INT_MULT", "INT_DIV", "INT_SDIV",
            "INT_REM", "INT_SREM", "INT_AND", "INT_OR", "INT_XOR",
            "INT_LEFT", "INT_RIGHT", "INT_SRIGHT",
            "INT_EQUAL", "INT_NOTEQUAL", "INT_LESS", "INT_SLESS",
            "INT_LESSEQUAL", "INT_SLESSEQUAL",
            "FLOAT_ADD", "FLOAT_SUB", "FLOAT_MULT", "FLOAT_DIV",
            "FLOAT_EQUAL", "FLOAT_NOTEQUAL", "FLOAT_LESS", "FLOAT_LESSEQUAL",
            "BOOL_AND", "BOOL_OR", "BOOL_XOR", "PIECE", "SUBPIECE",
            "PTRADD", "PTRSUB",
        }
        if mnemonic in binary_ops and pcode_op.getNumInputs() >= 2:
            if mnemonic == "PTRADD" and pcode_op.getNumInputs() >= 3:
                base = _input(0)
                index = _input(1)
                element_size = _input(2)
                return Expression.binary_op(
                    "INT_ADD",
                    base,
                    Expression.binary_op("INT_MULT", index, element_size),
                )
            return Expression.binary_op(mnemonic, _input(0), _input(1))

        unary_ops = {
            "INT_NEGATE", "INT_2COMP", "BOOL_NEGATE", "INT_ZEXT", "INT_SEXT",
            "FLOAT_NEG", "FLOAT_ABS", "FLOAT_SQRT",
            "TRUNC", "FLOAT_FLOAT2FLOAT", "FLOAT_INT2FLOAT", "FLOAT_CEIL", "FLOAT_FLOOR",
            "POPCOUNT", "LZCOUNT",
        }
        if mnemonic in unary_ops and pcode_op.getNumInputs() >= 1:
            expr = Expression.unary_op(mnemonic, _input(0))
            output = pcode_op.getOutput()
            if output is not None:
                expr.size = output.getSize()
            return expr

        if mnemonic == "LOAD" and pcode_op.getNumInputs() >= 2:
            output = pcode_op.getOutput()
            size = output.getSize() if output is not None else 4
            addr_expr = _input(1)
            cached = local_memory.get(self._local_memory_key(addr_expr, size))
            if cached is not None:
                return cached
            return Expression.memory(addr_expr, size)

        return None

    def _apply_local_store_effect(
        self,
        pcode_op,
        tracer,
        local_values: Dict[Tuple[str, int, int], Expression],
        local_storages: Dict[Tuple[str, int, int], Any],
        local_memory: Dict[Tuple[StructuralKey, int], Expression],
    ) -> None:
        if pcode_op.getNumInputs() < 3:
            return
        addr_expr = self._evaluate_local_varnode_expression(
            pcode_op.getInput(1),
            tracer,
            local_values,
            local_storages,
            local_memory,
        )
        value_expr = self._evaluate_local_varnode_expression(
            pcode_op.getInput(2),
            tracer,
            local_values,
            local_storages,
            local_memory,
        )
        size = pcode_op.getInput(2).getSize()
        local_memory[self._local_memory_key(addr_expr, size)] = value_expr

    def _resolve_local_return_expression(
        self,
        pcode_op,
        tracer,
        local_values: Dict[Tuple[str, int, int], Expression],
        local_storages: Dict[Tuple[str, int, int], Any],
        local_memory: Dict[Tuple[StructuralKey, int], Expression],
        current_function=None,
    ) -> Expression:
        if pcode_op.getNumInputs() >= 2:
            return self._evaluate_local_varnode_expression(
                pcode_op.getInput(1),
                tracer,
                local_values,
                local_storages,
                local_memory,
            )

        for return_varnode in self._get_function_return_varnodes(current_function):
            expr = self._evaluate_local_varnode_expression(
                return_varnode,
                tracer,
                local_values,
                local_storages,
                local_memory,
            )
            if expr is not None and expr.expr_type != ExpressionType.UNKNOWN:
                self._debug_print(
                    f"Local target RETURN without explicit value; using return storage {return_varnode}"
                )
                return expr

        for return_storage in self._get_implicit_return_target_storages(current_function, tracer):
            expr = self._lookup_local_expression_for_storage(
                return_storage,
                local_values,
                local_storages,
            )
            if expr is not None and expr.expr_type != ExpressionType.UNKNOWN:
                self._debug_print(
                    "Local target RETURN without explicit value; using implicit return storage "
                    f"{getattr(return_storage, 'base_register_name', None) or getattr(return_storage, 'register_name', None)}"
                )
                return expr

        self._debug_print("Local target RETURN without explicit value; defaulting to 0")
        return Expression.constant(0, 1)

    def _lookup_local_alias_expression(
        self,
        varnode,
        tracer,
        local_values: Dict[Tuple[str, int, int], Expression],
        local_storages: Dict[Tuple[str, int, int], Any],
    ) -> Optional[Expression]:
        try:
            target_storage = tracer._get_storage_info_from_varnode(varnode)
        except Exception:
            return None
        if target_storage is None or not getattr(target_storage, "is_register", False):
            return None

        for key, candidate_storage in local_storages.items():
            if candidate_storage is None:
                continue
            try:
                same_base = candidate_storage.shares_base_register_with(target_storage)
                overlaps = candidate_storage.bit_range_overlaps_with(target_storage)
            except Exception:
                continue
            if not same_base or not overlaps:
                continue
            candidate_expr = local_values.get(key)
            if candidate_expr is None:
                continue
            aliased = self._clone_expression(candidate_expr)
            aliased.size = target_storage.size
            self._debug_print(
                "Local alias resolution: "
                f"{getattr(candidate_storage, 'register_name', None)} -> "
                f"{getattr(target_storage, 'register_name', None)} as {aliased.to_string()}"
            )
            return aliased
        return None

    def _lookup_local_expression_for_storage(
        self,
        target_storage: Optional[StorageInfo],
        local_values: Dict[Tuple[str, int, int], Expression],
        local_storages: Dict[Tuple[str, int, int], Any],
    ) -> Optional[Expression]:
        if target_storage is None or not getattr(target_storage, "is_register", False):
            return None

        best_expr: Optional[Expression] = None
        best_score: Optional[Tuple[int, int, int, int]] = None

        for key, candidate_storage in local_storages.items():
            if candidate_storage is None:
                continue
            try:
                same_base = candidate_storage.shares_base_register_with(target_storage)
                overlaps = candidate_storage.bit_range_overlaps_with(target_storage)
            except Exception:
                continue
            if not same_base or not overlaps:
                continue

            candidate_expr = local_values.get(key)
            if candidate_expr is None:
                continue

            candidate_size = int(getattr(candidate_storage, "size", 0) or 0)
            target_size = int(getattr(target_storage, "size", 0) or 0)
            candidate_offset = int(getattr(candidate_storage, "bit_offset_in_base", 0) or 0)
            target_offset = int(getattr(target_storage, "bit_offset_in_base", 0) or 0)
            score = (
                1 if candidate_offset == target_offset else 0,
                1 if candidate_size == target_size else 0,
                min(candidate_size, target_size),
                -abs(candidate_offset - target_offset),
            )
            if best_score is not None and score <= best_score:
                continue

            aliased = self._clone_expression(candidate_expr)
            aliased.size = max(1, target_size or getattr(aliased, "size", 0) or 0)
            best_expr = aliased
            best_score = score

        return best_expr

    def _get_function_return_varnodes(self, function) -> List[Any]:
        if function is None:
            return []
        try:
            return_var = function.getReturn()
            if return_var is None:
                return []
            storage = return_var.getVariableStorage()
            if storage is None:
                return []
            get_varnodes = getattr(storage, "getVarnodes", None)
            if callable(get_varnodes):
                raw_varnodes = cast(Iterable[Any], get_varnodes())
                return [vn for vn in raw_varnodes if vn is not None]
        except Exception:
            return []
        return []

    def _get_current_prototype_return_varnodes(self) -> List[Any]:
        prototype = self._current_function_prototype
        if prototype is None:
            return []
        try:
            storage = prototype.getReturnStorage()
            if storage is None:
                return []
            get_varnodes = getattr(storage, "getVarnodes", None)
            if callable(get_varnodes):
                raw_varnodes = cast(Iterable[Any], get_varnodes())
                return [vn for vn in raw_varnodes if vn is not None]
        except Exception:
            return []
        return []

    def _infer_abi_return_storages(self) -> List[StorageInfo]:
        """関数シグネチャが void に潰れていても使える保守的な返り値レジスタ候補。"""
        try:
            lang = self.program.getLanguage() if self.program is not None else None
            lang_id = str(lang.getLanguageID()) if lang is not None else ""
            processor = str(lang.getProcessor()) if lang is not None else ""
            pointer_size = int(self.program.getDefaultPointerSize()) if self.program is not None else 8
        except Exception:
            lang_id = ""
            processor = ""
            pointer_size = 8

        arch_tag = f"{lang_id} {processor}".upper()
        base_bits = max(pointer_size * 8, 32)

        def _reg(base_name: str) -> StorageInfo:
            return StorageInfo(
                is_register=True,
                space_name="register",
                size=max(base_bits // 8, 4),
                size_bits=base_bits,
                register_name=base_name,
                base_register_name=base_name,
                base_register_size=max(base_bits // 8, 4),
                base_register_size_bits=base_bits,
                bit_offset_in_base=0,
            )

        if "MIPS" in arch_tag:
            return [_reg("v0")]
        if "AARCH64" in arch_tag or "ARM:LE:64" in arch_tag or "ARM:BE:64" in arch_tag:
            return [_reg("x0")]
        if "ARM" in arch_tag:
            return [_reg("r0")]
        if "X86" in arch_tag and "64" in arch_tag:
            return [_reg("rax")]
        if "X86" in arch_tag or "IA-32" in arch_tag:
            return [_reg("eax")]
        return []

    def _get_implicit_return_target_storages(
        self,
        function,
        tracer: PcodeTracer,
    ) -> List[StorageInfo]:
        target_storages: List[StorageInfo] = []
        for return_varnode in self._get_current_prototype_return_varnodes():
            storage = tracer._get_storage_info_from_varnode(return_varnode)
            if storage is not None:
                target_storages.append(storage)
        for return_varnode in self._get_function_return_varnodes(function):
            storage = tracer._get_storage_info_from_varnode(return_varnode)
            if storage is not None:
                target_storages.append(storage)

        if target_storages:
            return self._deduplicate_storage_infos(target_storages)

        fallback = self._infer_abi_return_storages()
        if self.debug and fallback:
            names = [storage.base_register_name or storage.register_name or "?" for storage in fallback]
            self._debug_print(
                f"Using ABI fallback return storages: {names}"
            )
        return fallback

    def _deduplicate_storage_infos(
        self,
        storages: List[StorageInfo],
    ) -> List[StorageInfo]:
        deduped: List[StorageInfo] = []
        seen: Set[Tuple[Any, ...]] = set()
        for storage in storages:
            key = (
                bool(getattr(storage, "is_register", False)),
                getattr(storage, "space_name", None),
                getattr(storage, "offset", None),
                getattr(storage, "size", None),
                getattr(storage, "size_bits", None),
                getattr(storage, "register_name", None),
                getattr(storage, "base_register_name", None),
                getattr(storage, "bit_offset_in_base", None),
            )
            if key in seen:
                continue
            seen.add(key)
            deduped.append(storage)
        return deduped

    def _get_instruction_with_fallback(self, addr):
        listing = self.program.getListing()
        instruction = listing.getInstructionAt(addr)
        if instruction is not None:
            return instruction

        containing_instruction = getattr(listing, "getInstructionContaining", None)
        if callable(containing_instruction):
            instruction = containing_instruction(addr)
            if instruction is not None:
                return instruction

        if self._attempt_disassemble_at(addr):
            instruction = listing.getInstructionAt(addr)
            if instruction is not None:
                return instruction
            if callable(containing_instruction):
                instruction = containing_instruction(addr)
                if instruction is not None:
                    return instruction

        return None

    def _attempt_disassemble_at(self, addr) -> bool:
        try:
            from ghidra.app.cmd.disassemble import DisassembleCommand  # type: ignore[import]
        except Exception:
            self._debug_print(f"Local target disassembly unavailable at {addr}: import failed")
            return False

        try:
            command = DisassembleCommand(addr, None, True)
        except TypeError:
            try:
                command = DisassembleCommand(addr, None)
            except Exception as exc:
                self._debug_print(f"Local target disassembly setup failed at {addr}: {exc}")
                return False
        except Exception as exc:
            self._debug_print(f"Local target disassembly setup failed at {addr}: {exc}")
            return False

        try:
            with self._program_transaction(f"Disassemble local target {addr}"):
                applied = command.applyTo(self.program)
        except Exception as exc:
            self._debug_print(f"Local target disassembly failed at {addr}: {exc}")
            return False

        if applied:
            self._debug_print(f"Local target disassembly materialized instructions at {addr}")
        else:
            self._debug_print(f"Local target disassembly produced no instructions at {addr}")
        return bool(applied)

    def _resolve_local_branch_target(self, instruction):
        try:
            flows = instruction.getFlows()
        except Exception:
            flows = None
        if flows:
            try:
                if len(flows) == 1 and flows[0] is not None:
                    return flows[0]
            except Exception:
                pass

        try:
            fallthrough = instruction.getFallThrough()
        except Exception:
            fallthrough = None
        return fallthrough

    def _get_or_analyze_call_target(
        self,
        target,
        active_functions: Set[Tuple[Any, ...]],
        minimum_param_count: int = 0,
        args: Optional[Sequence[Expression]] = None,
    ) -> Optional[FunctionReturnAnalysis]:
        target_ref = self._coerce_runtime_target_ref(target)
        callee = self._resolve_target_function(target_ref)
        if callee is None:
            return None

        bound_parameter_values = self._bound_parameter_values_from_args(args)
        cache_key = self._analysis_scope_key(callee, bound_parameter_values)
        generic_cache_key = self._function_cache_key(callee)
        cached = self._call_analysis_cache.get(cache_key)
        if cached is not None and len(getattr(cached, "parameters", []) or []) >= minimum_param_count:
            return cached

        analysis = self.analyze_function(
            callee,
            timeout=60,
            active_functions=self._extend_active_functions(active_functions, target_ref),
            bound_parameter_values=bound_parameter_values,
        )
        if cached is None:
            self._call_analysis_cache[cache_key] = analysis
            if generic_cache_key is not None and not bound_parameter_values:
                self._call_analysis_cache[generic_cache_key] = analysis
            return analysis
        if analysis is None:
            return cached
        if len(getattr(analysis, "parameters", []) or []) >= len(getattr(cached, "parameters", []) or []):
            self._call_analysis_cache[cache_key] = analysis
            if generic_cache_key is not None and not bound_parameter_values:
                self._call_analysis_cache[generic_cache_key] = analysis
            return analysis
        return cached

    def _call_summary_is_safe(
        self,
        value: Expression,
        conditions: List[Condition],
        args: List[Expression],
    ) -> bool:
        if self._expression_contains_unknown_or_call(value):
            return False
        if not self._expression_references_only_allowed_objects(value, args):
            return False

        for cond in conditions:
            if self._expression_contains_unknown_or_call(cond.expression):
                return False
            if not self._expression_references_only_allowed_objects(cond.expression, args):
                return False

        return True

    def _expression_contains_unknown_or_call(self, expr: Optional[Expression]) -> bool:
        if expr is None:
            return False

        if expr.expr_type == ExpressionType.UNKNOWN:
            return True
        if expr.expr_type == ExpressionType.CALL:
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

    def _expression_contains_phi(self, expr: Optional[Expression]) -> bool:
        if expr is None:
            return False
        if expr.expr_type == ExpressionType.PHI:
            return True
        for operand in getattr(expr, "operands", []) or []:
            if self._expression_contains_phi(operand):
                return True
        return False

    def _specialize_call_analysis(
        self,
        analysis: FunctionReturnAnalysis,
        args: List[Expression],
    ) -> FunctionReturnAnalysis:
        replacements = _build_parameter_replacements(analysis.parameters, args)
        specialized_deferred_calls: Dict[Tuple[object, ...], DeferredCallInfo] = {}
        original_to_specialized: Dict[Tuple[object, ...], DeferredCallInfo] = {}

        for info in (analysis.deferred_calls or {}).values():
            specialized_info = DeferredCallInfo(
                placeholder_name=info.placeholder_name,
                target_ref=info.target_ref,
                arguments=[
                    substitute_expression(arg, replacements, analysis.parameters)
                    for arg in (info.arguments or [])
                ],
                call_target_expr=(
                    substitute_expression(info.call_target_expr, replacements, analysis.parameters)
                    if info.call_target_expr is not None
                    else None
                ),
                deferred_call_ref=info.deferred_call_ref,
            )
            specialized_deferred_calls[info.deferred_call_ref.stable_key()] = specialized_info
            original_to_specialized[info.deferred_call_ref.stable_key()] = specialized_info

        for info in specialized_deferred_calls.values():
            info.arguments = [
                self._rewrite_deferred_runtime_refs_in_expression(arg, original_to_specialized)
                for arg in (info.arguments or [])
            ]
            if info.call_target_expr is not None:
                rewritten_target_expr = self._rewrite_deferred_runtime_refs_in_expression(
                    info.call_target_expr,
                    original_to_specialized,
                )
                info.call_target_expr = self._normalize_call_target_expression(
                    rewritten_target_expr,
                )

        specialized_returns: List[ReturnInfo] = []
        for ret in analysis.returns:
            specialized_value = substitute_expression(ret.value, replacements, analysis.parameters)
            specialized_value = self._rewrite_deferred_runtime_refs_in_expression(
                specialized_value,
                original_to_specialized,
            )
            specialized_conditions = [
                Condition(
                    self._rewrite_deferred_runtime_refs_in_expression(
                        substitute_condition(cond, replacements, analysis.parameters).expression,
                        original_to_specialized,
                    ),
                    cond.negated,
                )
                for cond in ret.conditions
            ]
            specialized_returns.append(
                ReturnInfo(
                    address=ret.address,
                    value=specialized_value,
                    conditions=specialized_conditions,
                    branch_index=ret.branch_index,
                    pcode_identity=ret.pcode_identity,
                    pcode_order=ret.pcode_order,
                    pcode_time=ret.pcode_time,
                    pcode_op_ref=getattr(ret, "pcode_op_ref", None),
                )
            )

        return FunctionReturnAnalysis(
            function_name=analysis.function_name,
            entry_point=analysis.entry_point,
            parameters=[dict(param) for param in (analysis.parameters or [])],
            returns=specialized_returns,
            function_ref=analysis.function_ref,
            return_type=analysis.return_type,
            return_type_obj=analysis.return_type_obj,
            signedness_result=analysis.signedness_result,
            unknown_event_count=analysis.unknown_event_count,
            unknown_event_reasons=list(analysis.unknown_event_reasons),
            analysis_notes=list(analysis.analysis_notes),
            recovered_from_decompiler=analysis.recovered_from_decompiler,
            incomplete_control_flow=analysis.incomplete_control_flow,
            deferred_calls=specialized_deferred_calls,
            effect_summary=analysis.effect_summary,
            signature_hypotheses=list(getattr(analysis, "signature_hypotheses", []) or []),
            comparison_surface=analysis.comparison_surface,
            analysis_scope_key=analysis.analysis_scope_key,
            program_is_big_endian=analysis.program_is_big_endian,
        )

    def _merge_deferred_calls_into_current_analysis(
        self,
        deferred_calls: Optional[Dict[Tuple[object, ...], DeferredCallInfo]],
    ) -> None:
        if not deferred_calls:
            return

        for info in deferred_calls.values():
            if info is None or getattr(info, "deferred_call_ref", None) is None:
                continue
            deferred_key = info.deferred_call_ref.stable_key()
            if deferred_key in self._current_deferred_calls:
                continue

            cloned_target_expr = (
                self._normalize_call_target_expression(
                    self._clone_expression(info.call_target_expr)
                )
                if info.call_target_expr is not None
                else None
            )
            self._current_deferred_calls[deferred_key] = DeferredCallInfo(
                placeholder_name=info.placeholder_name,
                target_ref=info.target_ref,
                arguments=[
                    self._clone_expression(arg)
                    for arg in (info.arguments or [])
                ],
                call_target_expr=cloned_target_expr,
                deferred_call_ref=info.deferred_call_ref,
            )

    def _normalize_call_target_expression(
        self,
        expr: Optional[Expression],
    ) -> Optional[Expression]:
        if expr is None:
            return None

        if expr.expr_type == ExpressionType.PHI and expr.value:
            rebuilt_branches = []
            changed = False
            for cond, value in expr.value:
                rewritten_value = self._normalize_call_target_expression(value)
                changed = changed or (rewritten_value is not value)
                rebuilt_branches.append((cond, rewritten_value))
            if not changed:
                return expr
            rebuilt = Expression.phi(rebuilt_branches)
            rebuilt.size = expr.size
            return rebuilt

        if expr.expr_type == ExpressionType.CONSTANT:
            try:
                address_value = int(expr.value)
            except Exception:
                return expr

            if self._resolve_function_from_program_offset(address_value) is not None:
                return expr

            try:
                pointer_size = int(self.program.getDefaultPointerSize()) if self.program is not None else 0
            except Exception:
                pointer_size = int(expr.size or 0)
            if pointer_size <= 0:
                return expr

            loaded_value = self._read_memory_value(address_value, pointer_size)
            if loaded_value is None:
                return expr

            function = self._resolve_function_from_program_offset(loaded_value)
            if function is None:
                return expr

            return Expression.constant(
                loaded_value,
                size=max(expr.size or 0, pointer_size),
                runtime_ref=AddressValueRef(
                    address_offset=loaded_value,
                    source="readonly_call_target",
                    display_hint=function.getName(),
                    can_execute=True,
                ),
            )

        if not expr.operands:
            return expr

        rewritten_operands = [
            self._normalize_call_target_expression(operand)
            for operand in expr.operands
        ]
        if all(new is old for new, old in zip(rewritten_operands, expr.operands)):
            return expr
        return expr.clone_with(operands=rewritten_operands)

    def _rewrite_deferred_runtime_refs_in_expression(
        self,
        expr: Optional[Expression],
        deferred_mapping: Dict[Tuple[object, ...], DeferredCallInfo],
    ) -> Optional[Expression]:
        if expr is None or not deferred_mapping:
            return expr

        if expr.expr_type == ExpressionType.UNKNOWN:
            runtime_ref = getattr(expr, "runtime_ref", None)
            deferred_call_ref = getattr(runtime_ref, "deferred_call_ref", None)
            deferred_key = (
                deferred_call_ref.stable_key()
                if hasattr(deferred_call_ref, "stable_key")
                else None
            )
            replacement_info = deferred_mapping.get(deferred_key)
            if replacement_info is not None:
                return expr.clone_with(runtime_ref=replacement_info.unknown_ref)
            return expr

        if expr.expr_type == ExpressionType.PHI and expr.value:
            rebuilt_branches = []
            changed = False
            for cond, value in expr.value:
                rewritten_cond = None
                if cond is not None:
                    rewritten_expr = self._rewrite_deferred_runtime_refs_in_expression(
                        cond.expression,
                        deferred_mapping,
                    )
                    rewritten_cond = cond if rewritten_expr is cond.expression else Condition(rewritten_expr, cond.negated)
                    changed = changed or (rewritten_cond is not cond)
                rewritten_value = self._rewrite_deferred_runtime_refs_in_expression(
                    value,
                    deferred_mapping,
                )
                changed = changed or (rewritten_value is not value)
                rebuilt_branches.append((rewritten_cond, rewritten_value))
            if not changed:
                return expr
            rebuilt = Expression.phi(rebuilt_branches)
            rebuilt.size = expr.size
            return rebuilt

        if not expr.operands:
            return expr

        rewritten_operands = [
            self._rewrite_deferred_runtime_refs_in_expression(operand, deferred_mapping)
            for operand in expr.operands
        ]
        if all(new is old for new, old in zip(rewritten_operands, expr.operands)):
            return expr
        return expr.clone_with(operands=rewritten_operands)

    def _collect_expression_object_keys(
        self,
        expr: Optional[Expression],
        out: Set[Tuple[object, ...]],
    ) -> None:
        if expr is None:
            return
        key = expression_key_safe(expr, include_memory_read_order=False)
        if key is not None:
            out.add(key)
        if expr.expr_type == ExpressionType.PHI and expr.value:
            for cond, value in expr.value:
                if cond is not None:
                    self._collect_expression_object_keys(cond.expression, out)
                self._collect_expression_object_keys(value, out)
            return
        for operand in expr.operands or []:
            self._collect_expression_object_keys(operand, out)

    def _expression_references_only_allowed_objects(
        self,
        expr: Optional[Expression],
        args: List[Expression],
    ) -> bool:
        if expr is None:
            return True

        allowed_subtrees: Set[Tuple[object, ...]] = set()
        for arg in args or []:
            self._collect_expression_object_keys(arg, allowed_subtrees)
        return self._expression_references_allowed_subtrees(expr, allowed_subtrees)

    def _expression_references_allowed_subtrees(
        self,
        expr: Optional[Expression],
        allowed_subtrees: Set[Tuple[object, ...]],
    ) -> bool:
        if expr is None:
            return True
        expr_key = expression_key_safe(expr, include_memory_read_order=False)
        if expr_key in allowed_subtrees:
            return True

        if self._expression_contains_unknown_or_call(expr):
            return False

        if expr.expr_type in {ExpressionType.CONSTANT, ExpressionType.LITERAL}:
            return True

        if expr.expr_type in {ExpressionType.PARAMETER, ExpressionType.VARIABLE}:
            if getattr(expr, "runtime_ref", None) is not None:
                return True
            return False

        if expr.expr_type == ExpressionType.PHI and expr.value:
            for cond, value in expr.value:
                if cond is not None and not self._expression_references_allowed_subtrees(
                    cond.expression,
                    allowed_subtrees,
                ):
                    return False
                if not self._expression_references_allowed_subtrees(value, allowed_subtrees):
                    return False
            return True

        if expr.expr_type == ExpressionType.MEMORY and not expr.operands:
            return getattr(expr, "runtime_ref", None) is not None

        for operand in expr.operands or []:
            if not self._expression_references_allowed_subtrees(operand, allowed_subtrees):
                return False
        return True
    
    def _detect_signedness(self, high_function) -> Optional[SignednessResult]:
        """
        Phase 1: P-code証拠から符号性を推定
        
        Args:
            high_function: GhidraのHighFunctionオブジェクト
        
        Returns:
            SignednessResult: 推定結果（エラー時はNone）
        """
        try:
            detector = SignednessDetector(high_function, debug=self.debug)
            evidence = detector.detect()
            return SignednessResult.from_evidence(evidence)
        except Exception as e:
            self._debug_print(f"Signedness detection failed: {e}")
            return None
    
    def _get_return_type_info(self, high_function):
        """戻り値の型オブジェクトと表示名を取得"""
        try:
            func_proto = high_function.getFunctionPrototype()
            if func_proto:
                ret_type = func_proto.getReturnType()
                if ret_type:
                    return ret_type, self._get_return_type(high_function) or str(ret_type)
        except Exception as e:
            self._debug_print(f"Failed to get return type: {e}")
        return None, None

    def _get_return_type(self, high_function) -> Optional[str]:
        """後方互換: 戻り値の表示名だけを返す。"""
        try:
            func_proto = high_function.getFunctionPrototype()
            if func_proto:
                ret_type = func_proto.getReturnType()
                if ret_type:
                    return str(ret_type)
        except Exception as e:
            self._debug_print(f"Failed to get return type: {e}")
        return None
    
    def _collect_parameters(self, high_function) -> List[Dict]:
        """パラメータ情報を収集（ストレージ情報付き）"""
        params = []
        local_map = high_function.getLocalSymbolMap()
        owner_program_id = None
        owner_entry_offset = None
        try:
            if self.program is not None and hasattr(self.program, "getUniqueProgramID"):
                owner_program_id = int(self.program.getUniqueProgramID())
        except Exception:
            owner_program_id = None
        try:
            function = getattr(high_function, "getFunction", lambda: None)()
            if function is not None and hasattr(function, "getEntryPoint"):
                entry_point = function.getEntryPoint()
                if entry_point is not None:
                    owner_entry_offset = int(entry_point.getOffset())
        except Exception:
            owner_entry_offset = None
        
        if local_map:
            for sym in local_map.getSymbols():
                if sym.isParameter():
                    data_type = sym.getDataType()
                    param_info = {
                        "name": sym.getName(),
                        "data_type": str(data_type) if data_type else None,
                        "data_type_obj": data_type,
                        "size": sym.getSize(),
                        "is_signed": self._is_signed_type(data_type),
                        "storage": self._get_storage_info(sym),
                        "owner_program_id": owner_program_id,
                        "owner_entry_offset": owner_entry_offset,
                    }
                    try:
                        param_info["index"] = sym.getCategoryIndex()
                    except:
                        param_info["index"] = -1
                    
                    if self.debug:
                        self._debug_print(f"Parameter '{sym.getName()}': "
                                         f"type={param_info['data_type']}, "
                                         f"signed={param_info['is_signed']}, "
                                         f"storage={param_info['storage']}")
                    
                    params.append(param_info)
        
        params.sort(key=lambda x: x.get("index", -1))
        return params
    
    def _is_signed_type(self, data_type) -> bool:
        """データ型が符号付きかどうかを判定"""
        return get_declared_type_signedness(data_type, fallback_signed=True)

    def _is_void_type(self, data_type) -> bool:
        """データ型が void かどうかを判定"""
        return is_void_data_type(data_type)
    
    def _get_storage_info(self, sym) -> Optional[Dict]:
        """シンボルのストレージ情報を取得"""
        try:
            storage = sym.getStorage()
            if storage is None:
                return None
            
            # Varnodeリストを取得
            raw_varnodes = getattr(storage, "getVarnodes", lambda: [])()
            varnodes = [vn for vn in cast(Iterable[Any], raw_varnodes) if vn is not None]
            if not varnodes:
                return None
            
            first_vn = varnodes[0]
            addr = first_vn.getAddress()
            space = addr.getAddressSpace()
            
            storage_info = {
                "is_register": space.isRegisterSpace(),
                "offset": first_vn.getOffset(),
                "size": first_vn.getSize(),
                "size_bits": first_vn.getSize() * 8,
                "space_name": space.getName(),
            }
            
            if space.isRegisterSpace():
                # レジスタ情報を取得
                reg = self.program.getRegister(addr, first_vn.getSize())
                if reg:
                    storage_info["register_name"] = reg.getName()
                    
                    # 親レジスタ情報
                    base_reg = reg.getBaseRegister()
                    if base_reg and base_reg != reg:
                        storage_info["base_register_name"] = base_reg.getName()
                        storage_info["base_register_size"] = base_reg.getBitLength() // 8
                        storage_info["base_register_size_bits"] = base_reg.getBitLength()
                        # パラメータのビットオフセット（親レジスタ内での位置）
                        byte_offset_in_base = reg.getOffset() - base_reg.getOffset()
                        storage_info["bit_offset_in_base"] = byte_offset_in_base * 8
                    else:
                        # 親レジスタと同じ場合
                        storage_info["base_register_name"] = reg.getName()
                        storage_info["base_register_size"] = reg.getBitLength() // 8
                        storage_info["base_register_size_bits"] = reg.getBitLength()
                        storage_info["bit_offset_in_base"] = 0
            
            return storage_info
        except Exception as e:
            if self.debug:
                self._debug_print(f"Failed to get storage info: {e}")
            return None
    
    def _analyze_return_op(
        self,
        return_op,
        tracer: PcodeTracer,
        condition_tracker: ConditionTracker,
        return_index: int,
        current_function,
        active_functions: Set[Tuple[Any, ...]],
    ) -> List[ReturnInfo]:
        """単一のRETURNを解析"""
        site_metadata = self._describe_pcode_site(return_op, "unknown")
        address = cast(str, site_metadata.get("address") or "unknown")
        
        num_inputs = return_op.getNumInputs()
        self._debug_print(f"RETURN at {address}, inputs: {num_inputs}")

        raw_path_entries = None
        get_block_paths = getattr(condition_tracker, "get_all_valid_block_paths_to_return", None)
        if callable(get_block_paths):
            raw_path_entries = get_block_paths(return_op)

        path_entries = self._coerce_block_path_entries(raw_path_entries)
        blocked_path_conditions: List[List[Condition]] = []
        if path_entries:
            path_entries, blocked_path_conditions = self._filter_noreturn_return_path_entries(
                path_entries,
                tracer,
                return_op,
            )
            if not path_entries:
                if self.debug:
                    self._debug_print(
                        "All RETURN path variants were pruned as noreturn/unreachable; skipping RETURN"
                    )
                return []
            all_valid_path_conditions = [list(conditions) for _blocks, conditions in path_entries]
            path_conditions = list(all_valid_path_conditions[0]) if all_valid_path_conditions else []
        else:
            # Fall back to the pre-existing condition-only API if block paths are unavailable.
            path_conditions = condition_tracker.get_path_conditions_to_return(return_op)
            all_valid_path_conditions = condition_tracker.get_all_valid_paths_to_return(return_op)

        if self.debug and path_conditions:
            cond_strs = [ConditionSimplifier.get_simplified_condition_string(c) for c in path_conditions]
            self._debug_print(f"Path conditions to RETURN: {cond_strs}")
        if self.debug and len(all_valid_path_conditions) > 1:
            self._debug_print(
                f"RETURN has {len(all_valid_path_conditions)} valid path variants",
            )

        previous_blocked = list(self._current_blocked_return_path_conditions)
        self._current_blocked_return_path_conditions = [
            list(conditions) for conditions in blocked_path_conditions
        ]
        try:
            if num_inputs >= 2:
                return_varnode = return_op.getInput(1)
                return self._analyze_return_value(
                    return_varnode,
                    address,
                    tracer,
                    condition_tracker,
                    path_conditions,
                    return_index,
                    all_path_conditions=all_valid_path_conditions,
                    active_functions=active_functions,
                    current_function=current_function,
                    site_metadata=site_metadata,
                )
            else:
                implicit_results = self._analyze_implicit_return_value(
                    return_op,
                    address,
                    tracer,
                    condition_tracker,
                    path_conditions,
                    return_index,
                    all_path_conditions=all_valid_path_conditions,
                    path_entries=path_entries,
                    active_functions=active_functions,
                    current_function=current_function,
                    site_metadata=site_metadata,
                )
                if implicit_results is not None:
                    return implicit_results
                simplified_conds = ConditionSimplifier.simplify_conditions_object_centric(
                    path_conditions
                )
                return [self._make_return_info(
                    address=address,
                    value=Expression.unknown("void"),
                    conditions=simplified_conds,
                    branch_index=return_index,
                    site_metadata=site_metadata,
                )]
        finally:
            self._current_blocked_return_path_conditions = previous_blocked

    def _coerce_block_path_entries(self, path_entries) -> Optional[List[Tuple[List[Any], List[Condition]]]]:
        if not isinstance(path_entries, (list, tuple)):
            return None

        normalized: List[Tuple[List[Any], List[Condition]]] = []
        for entry in path_entries:
            if not isinstance(entry, (list, tuple)) or len(entry) != 2:
                return None
            block_path, conditions = entry
            if not isinstance(block_path, (list, tuple)):
                return None
            if not isinstance(conditions, (list, tuple)):
                return None
            normalized.append((list(block_path), list(conditions)))
        return normalized

    def _filter_noreturn_return_path_entries(
        self,
        path_entries,
        tracer: PcodeTracer,
        return_op,
    ):
        if not path_entries:
            return path_entries, []

        filtered = []
        blocked_conditions: List[List[Condition]] = []
        for block_path, conditions in path_entries:
            if self._block_path_contains_noreturn_call(block_path, tracer, return_op):
                blocked_conditions.append(list(conditions))
                if self.debug:
                    cond_strs = [
                        ConditionSimplifier.get_simplified_condition_string(c)
                        for c in conditions
                    ]
                    block_indexes = [getattr(block, "index", "?") for block in block_path]
                    self._debug_print(
                        "Pruned RETURN path that contains a noreturn call: "
                        f"blocks={block_indexes}, conditions={cond_strs}"
                    )
                continue
            filtered.append((block_path, conditions))

        return filtered, blocked_conditions

    def _block_path_contains_noreturn_call(
        self,
        block_path,
        tracer: PcodeTracer,
        return_op,
    ) -> bool:
        for block_info in block_path:
            for pcode_op in getattr(block_info, "pcode_ops", []) or []:
                if self._pcode_ops_match(pcode_op, return_op):
                    return False
                if self._is_noreturn_control_transfer_op(pcode_op, tracer):
                    return True
        return False

    def _is_noreturn_call_op(self, pcode_op, tracer: PcodeTracer) -> bool:
        return self._is_noreturn_control_transfer_op(pcode_op, tracer)

    def _is_noreturn_control_transfer_op(self, pcode_op, tracer: PcodeTracer) -> bool:
        if pcode_op is None or pcode_op.getMnemonic() not in {"CALL", "CALLIND", "BRANCHIND"}:
            return False

        resolved_targets = self._resolve_object_centric_transfer_targets(pcode_op, tracer)
        if self.debug and not resolved_targets:
            try:
                traced_target = tracer.trace_varnode(pcode_op.getInput(0), use_cache=False)
                traced_summary = traced_target.to_string()
            except Exception:
                traced_summary = "<unavailable>"
            self._debug_print(
                f"CALL noreturn resolution failed to resolve targets for {pcode_op.getMnemonic()} "
                f"target={traced_summary}"
            )

        if not resolved_targets:
            return False

        resolved_functions = []
        for target_ref in resolved_targets:
            target_function = self._resolve_function_from_call_target_ref(target_ref)
            if target_function is None:
                if self.debug:
                    self._debug_print(
                        "Control-transfer target stayed unresolved for noreturn pruning: "
                        f"{target_ref.display_name()}"
                    )
                return False
            resolved_functions.append((target_ref, target_function))

        if resolved_functions and all(self._function_has_no_return(function) for _target_ref, function in resolved_functions):
            if self.debug:
                names = ", ".join(target_ref.display_name() for target_ref, _function in resolved_functions)
                self._debug_print(
                    "Detected noreturn control transfer via object-centric resolution: "
                    f"{names}"
                )
            return True
        return False

    def _resolve_object_centric_call_targets(
        self,
        pcode_op,
        tracer: Optional[PcodeTracer],
    ) -> List[CallTargetRef]:
        return self._resolve_object_centric_transfer_targets(pcode_op, tracer)

    def _resolve_object_centric_transfer_targets(
        self,
        pcode_op,
        tracer: Optional[PcodeTracer],
    ) -> List[CallTargetRef]:
        if pcode_op is None or tracer is None:
            return []

        resolved: List[CallTargetRef] = []

        try:
            mnemonic = str(pcode_op.getMnemonic())
        except Exception:
            mnemonic = ""

        if mnemonic in {"CALL", "CALLIND"}:
            try:
                image_base = None
                if self.program is not None:
                    image_base = self.program.getImageBase().getOffset()
                for target_ref, _conditions in resolve_call_targets(
                    tracer,
                    pcode_op,
                    conditions=[],
                    parameters=list(self._current_parameters or []),
                    read_memory_value=self._read_memory_value if self.program is not None else None,
                    image_base=image_base,
                    debug=self.debug,
                ):
                    if target_ref is not None:
                        resolved.append(target_ref)
            except Exception:
                pass
        elif mnemonic == "BRANCHIND":
            try:
                target_varnode = pcode_op.getInput(0)
            except Exception:
                target_varnode = None

            if target_varnode is not None:
                resolver = getattr(tracer, "resolve_call_target_ref", None)
                if callable(resolver):
                    try:
                        direct_target = resolver(
                            target_varnode,
                            allow_containing=True,
                            allow_code_address=True,
                        )
                    except Exception:
                        direct_target = None
                    direct_target_ref = coerce_call_target_ref(direct_target)
                    if direct_target_ref is not None:
                        resolved.append(direct_target_ref)

                try:
                    target_expr = tracer.trace_varnode(target_varnode, use_cache=False)
                except Exception:
                    target_expr = None
                if target_expr is not None:
                    target_expr = self._concretize_readonly_loads(
                        target_expr,
                        [],
                        self._current_parameters,
                    )
                    for _branch_conditions, address_value in _enumerate_constant_expression_branches(target_expr):
                        target_function = self._resolve_function_from_program_offset(int(address_value))
                        if target_function is not None:
                            resolved.append(CallTargetRef.from_function(target_function))
                        else:
                            resolved.append(CallTargetRef.from_code_address(int(address_value)))

        if not resolved:
            fallback_target = _resolve_call_target_ref(tracer, pcode_op)
            if fallback_target is not None:
                resolved.append(fallback_target)

        deduped: List[CallTargetRef] = []
        seen_keys = set()
        for target_ref in resolved:
            stable_key = target_ref.stable_key()
            if stable_key in seen_keys:
                continue
            seen_keys.add(stable_key)
            deduped.append(target_ref)
        return deduped

    def _resolve_function_from_call_target_ref(
        self,
        target_ref: Optional[CallTargetRef],
    ):
        if target_ref is None or target_ref.is_unknown():
            return None

        function_obj = getattr(target_ref, "function_obj", None)
        if function_obj is not None:
            return function_obj

        if target_ref.entry_offset is not None:
            return self._resolve_function_from_program_offset(target_ref.entry_offset)

        if target_ref.address_offset is not None:
            return self._resolve_function_from_program_offset(target_ref.address_offset)

        return None

    def _get_function_manager(self):
        if self.program is None:
            return None
        try:
            return self.program.getFunctionManager()
        except Exception:
            return None

    def _resolve_function_from_address(self, address):
        if address is None:
            return None
        try:
            function_manager = self._get_function_manager()
            if function_manager is None:
                return None
            get_function_at = getattr(function_manager, "getFunctionAt", None)
            if callable(get_function_at):
                function = get_function_at(address)
                if function is not None:
                    return function
            get_referenced_function = getattr(function_manager, "getReferencedFunction", None)
            if callable(get_referenced_function):
                function = get_referenced_function(address)
                if function is not None:
                    return function
        except Exception:
            return None
        return None

    def _resolve_function_from_program_offset(self, address_value: int):
        if self.program is None or address_value < 0:
            return None
        try:
            address_factory = self.program.getAddressFactory()
            if address_factory is None:
                return None
            default_space = address_factory.getDefaultAddressSpace()
            if default_space is None:
                return None
            address = default_space.getAddress(address_value)
        except Exception:
            return None
        return self._resolve_function_from_address(address)

    def _function_has_no_return(self, function) -> bool:
        if function is None:
            return False
        for attr_name in ("hasNoReturn", "isNoReturn", "getNoReturn"):
            attr = getattr(function, attr_name, None)
            if callable(attr):
                try:
                    if bool(attr()):
                        return True
                except Exception:
                    continue
        return False

    def _analyze_implicit_return_value(
        self,
        return_op,
        address: str,
        tracer: PcodeTracer,
        condition_tracker: ConditionTracker,
        path_conditions: List[Condition],
        return_index: int,
        all_path_conditions: Optional[List[List[Condition]]] = None,
        path_entries=None,
        active_functions: Optional[Set[Tuple[Any, ...]]] = None,
        current_function=None,
        site_metadata: Optional[Dict[str, Optional[object]]] = None,
    ) -> Optional[List[ReturnInfo]]:
        """RETURN オペランドが欠落している場合に、返り値レジスタ由来の値を復元する。"""
        path_recovered = self._recover_implicit_return_from_block_paths(
            return_op,
            address,
            tracer,
            condition_tracker,
            return_index,
            path_entries,
            active_functions=active_functions,
            current_function=current_function,
            site_metadata=site_metadata,
        )
        if path_recovered is not None:
            return path_recovered

        tracked_sources = self._resolve_implicit_return_tracked_values(
            return_op,
            tracer,
            condition_tracker,
            current_function,
        )
        if tracked_sources:
            self._debug_print(
                "RETURN has no explicit value; retrying via object-centric return provenance"
            )
            recovered_results = self._recover_return_infos_from_tracked_sources(
                tracked_sources,
                address,
                tracer,
                condition_tracker,
                path_conditions,
                return_index,
                all_path_conditions=all_path_conditions,
                active_functions=active_functions,
                current_function=current_function,
                site_metadata=site_metadata,
            )
            if recovered_results is not None:
                return recovered_results
        elif self.debug:
            self._debug_print(
                "Implicit return storage recovery did not find a terminal producer"
            )

        if self.debug:
            self._debug_print(
                "Implicit return object-centric recovery did not find a materializable producer"
            )
        return None

    def _recover_implicit_return_from_block_paths(
        self,
        return_op,
        address: str,
        tracer: PcodeTracer,
        condition_tracker: ConditionTracker,
        return_index: int,
        path_entries,
        active_functions: Optional[Set[Tuple[Any, ...]]] = None,
        current_function=None,
        site_metadata: Optional[Dict[str, Optional[object]]] = None,
    ) -> Optional[List[ReturnInfo]]:
        """RETURN block 以前の path 上にある返り値レジスタ更新から暗黙 return を復元する。"""
        normalized_entries = self._coerce_block_path_entries(path_entries)
        if not normalized_entries:
            return None

        recovered_results: List[ReturnInfo] = []
        unresolved_paths: List[int] = []

        for path_idx, (block_path, conditions) in enumerate(normalized_entries):
            tracked_sources = self._resolve_implicit_return_tracked_values(
                return_op,
                tracer,
                condition_tracker,
                current_function,
                block_path=block_path,
            )
            if not tracked_sources:
                unresolved_paths.append(path_idx)
                continue

            path_results = self._recover_return_infos_from_tracked_sources(
                tracked_sources,
                address,
                tracer,
                condition_tracker,
                list(conditions),
                return_index * 1000 + path_idx * 100,
                all_path_conditions=[list(conditions)],
                active_functions=active_functions,
                current_function=current_function,
                site_metadata=site_metadata,
            )
            if not path_results:
                unresolved_paths.append(path_idx)
                continue

            recovered_results.extend(path_results)

        if recovered_results and not unresolved_paths:
            if self.debug:
                self._debug_print(
                    "Implicit return path recovery succeeded for all RETURN path variants"
                )
            return self._merge_equivalent_return_infos(recovered_results)

        if self.debug and unresolved_paths:
            self._debug_print(
                "Implicit return path recovery could not resolve terminal producer on "
                f"path(s) {unresolved_paths}"
            )
        return None

    def _recover_return_infos_from_tracked_sources(
        self,
        tracked_sources: List[_TrackedReturnValue],
        address: str,
        tracer: PcodeTracer,
        condition_tracker: ConditionTracker,
        path_conditions: List[Condition],
        return_index_base: int,
        all_path_conditions: Optional[List[List[Condition]]] = None,
        active_functions: Optional[Set[Tuple[Any, ...]]] = None,
        current_function=None,
        site_metadata: Optional[Dict[str, Optional[object]]] = None,
    ) -> Optional[List[ReturnInfo]]:
        recovered_results: List[ReturnInfo] = []
        for tracked_index, tracked in enumerate(tracked_sources):
            materialized = self._materialize_tracked_return_source(
                tracked,
                address,
                tracer,
                condition_tracker,
                path_conditions,
                return_index_base + tracked_index,
                all_path_conditions=all_path_conditions,
                active_functions=active_functions,
                current_function=current_function,
                site_metadata=site_metadata,
            )
            if materialized:
                recovered_results.extend(materialized)

        if not recovered_results:
            return None
        return self._merge_equivalent_return_infos(recovered_results)

    def _materialize_tracked_return_source(
        self,
        tracked: _TrackedReturnValue,
        address: str,
        tracer: PcodeTracer,
        condition_tracker: ConditionTracker,
        path_conditions: List[Condition],
        return_index: int,
        all_path_conditions: Optional[List[List[Condition]]] = None,
        active_functions: Optional[Set[Tuple[Any, ...]]] = None,
        current_function=None,
        site_metadata: Optional[Dict[str, Optional[object]]] = None,
    ) -> Optional[List[ReturnInfo]]:
        producer_op = tracked.producer_op
        if producer_op is not None and self._is_pcode_call_op(producer_op):
            return self._recover_implicit_return_from_terminal_call(
                producer_op,
                address,
                tracer,
                condition_tracker,
                path_conditions,
                return_index,
                all_path_conditions=all_path_conditions,
                active_functions=active_functions,
                current_function=current_function,
                site_metadata=site_metadata,
            )

        if tracked.varnode is None:
            return None

        return self._analyze_return_value(
            tracked.varnode,
            address,
            tracer,
            condition_tracker,
            path_conditions,
            return_index,
            all_path_conditions=all_path_conditions,
            active_functions=active_functions,
            current_function=current_function,
            site_metadata=site_metadata,
        )

    def _select_path_specific_return_source(
        self,
        candidate,
        block_path,
        condition_tracker: Optional[ConditionTracker] = None,
        path_conditions: Optional[List[Condition]] = None,
    ):
        """PHI 出力をそのまま返す代わりに、実際の predecessor に対応する入力へ絞る。"""
        if candidate is None or not block_path or len(block_path) < 2:
            return candidate

        normalized_path = [getattr(entry, "block", entry) for entry in block_path]
        selected = candidate
        max_refinements = max(1, len(normalized_path))

        for _ in range(max_refinements):
            def_op = getattr(selected, "getDef", lambda: None)()
            if def_op is None or getattr(def_op, "getMnemonic", lambda: None)() != "MULTIEQUAL":
                break

            phi_parent = getattr(def_op, "getParent", lambda: None)()
            phi_index = self._find_block_index_on_path(normalized_path, phi_parent)
            if phi_index is None or phi_index <= 0:
                break

            predecessor = normalized_path[phi_index - 1]
            refined = self._select_multiequal_input_for_return_path(
                multiequal_op=def_op,
                predecessor=predecessor,
                condition_tracker=condition_tracker,
                path_conditions=path_conditions,
            )
            if refined is None or refined is selected:
                break

            if self.debug:
                self._debug_print(
                    "Refined implicit return PHI source to predecessor-specific input "
                    f"{refined}"
                )
            selected = refined

        return selected

    def _find_block_index_on_path(self, block_path, target_block) -> Optional[int]:
        if target_block is None:
            return None

        for index in range(len(block_path) - 1, -1, -1):
            if self._blocks_match(block_path[index], target_block):
                return index
        return None

    def _select_multiequal_input_for_return_path(
        self,
        multiequal_op,
        predecessor,
        condition_tracker: Optional[ConditionTracker] = None,
        path_conditions: Optional[List[Condition]] = None,
    ):
        phi_parent = getattr(multiequal_op, "getParent", lambda: None)()
        get_in_size = getattr(phi_parent, "getInSize", None)
        get_in = getattr(phi_parent, "getIn", None)
        if not callable(get_in_size) or not callable(get_in):
            return None

        current_condition_keys = self._build_condition_signature_set(path_conditions or [])
        exact_matches = []
        best_input = None
        best_score: Optional[Tuple[int, int, int]] = None
        exact_best_input = None
        exact_best_score: Optional[Tuple[int, int, int]] = None

        try:
            for index in range(int(get_in_size())):
                incoming = get_in(index)
                candidate_input = multiequal_op.getInput(index)
                if candidate_input is None:
                    continue
                is_exact_match = self._blocks_match(incoming, predecessor)
                if is_exact_match:
                    exact_matches.append(candidate_input)
                score = self._score_multiequal_incoming_for_return_path(
                    incoming,
                    predecessor,
                    condition_tracker,
                    current_condition_keys,
                )
                if is_exact_match and (exact_best_score is None or score > exact_best_score):
                    exact_best_score = score
                    exact_best_input = candidate_input
                if best_score is None or score > best_score:
                    best_score = score
                    best_input = candidate_input
        except Exception:
            return None

        if exact_best_input is not None:
            if (
                best_input is not None
                and best_input is not exact_best_input
                and best_score is not None
                and exact_best_score is not None
                and bool(current_condition_keys)
                and best_score[0] == len(current_condition_keys)
                and best_score[0] > exact_best_score[0]
            ):
                return best_input
            return exact_best_input
        if len(exact_matches) == 1:
            return exact_matches[0]
        if exact_matches:
            return exact_matches[0]

        return best_input

    def _score_multiequal_incoming_for_return_path(
        self,
        incoming_block,
        predecessor,
        condition_tracker: Optional[ConditionTracker],
        current_condition_keys: Set[object],
    ) -> Tuple[int, int, int]:
        predecessor_match = 1 if self._blocks_match(incoming_block, predecessor) else 0
        if condition_tracker is None or not current_condition_keys:
            return (0, predecessor_match, 0)

        block_info = condition_tracker.get_block_by_hash(incoming_block)
        if block_info is None:
            return (0, predecessor_match, 0)

        incoming_conditions = condition_tracker.get_path_conditions_to_block(block_info)
        incoming_keys = self._build_condition_signature_set(incoming_conditions)
        if not incoming_keys:
            return (0, predecessor_match, 0)

        matched = len(incoming_keys & current_condition_keys)
        specificity = len(incoming_keys)
        return (matched, predecessor_match, specificity)

    def _build_condition_signature_set(self, conditions: List[Condition]) -> Set[object]:
        signatures: Set[object] = set()
        for condition in conditions:
            try:
                signatures.add(condition.structural_key(budget=256))
            except Exception:
                try:
                    signatures.add(ConditionNormalizer.normalize_for_contradiction(condition))
                except Exception:
                    continue
        return signatures

    def _blocks_match(self, lhs, rhs) -> bool:
        if lhs is rhs:
            return True
        try:
            if lhs == rhs:
                return True
        except Exception:
            pass

        lhs_start = self._get_block_start_address(lhs)
        rhs_start = self._get_block_start_address(rhs)
        if lhs_start is not None and rhs_start is not None:
            return lhs_start == rhs_start

        return False

    def _get_block_start_address(self, block) -> Optional[str]:
        get_start = getattr(block, "getStart", None)
        if not callable(get_start):
            return None
        try:
            start = get_start()
        except Exception:
            return None
        if start is None:
            return None
        return str(start)

    def _find_terminal_call_before_return(
        self,
        return_op,
        condition_tracker: ConditionTracker,
        tracer: Optional[PcodeTracer] = None,
        current_function=None,
    ):
        """同一 basic block 内で wrapper return とみなせる末尾 CALL/CALLIND を探す。"""
        return_parent = getattr(return_op, "getParent", lambda: None)()
        return_block = condition_tracker.get_block_by_hash(return_parent)
        if return_block is None:
            return None

        linear_ops = self._collect_linear_ops_to_return([return_block], return_op)
        if not linear_ops:
            return None
        return self._find_terminal_call_from_linear_ops(
            linear_ops,
            return_op,
            tracer=tracer,
            condition_tracker=condition_tracker,
            current_function=current_function,
            block_path=[return_block],
            path_conditions=None,
        )

    @staticmethod
    def _varnode_location_key(varnode) -> Optional[Tuple[str, int, int]]:
        if varnode is None:
            return None
        try:
            address = varnode.getAddress()
            size = int(varnode.getSize())
            if address is None:
                return None
            space = address.getAddressSpace()
            space_name = space.getName() if space is not None else "unknown"
            return (space_name, int(address.getOffset()), size)
        except Exception:
            return None

    @classmethod
    def _varnodes_may_alias(cls, lhs, rhs) -> bool:
        if lhs is None or rhs is None:
            return False
        if lhs is rhs:
            return True
        return cls._varnode_location_key(lhs) == cls._varnode_location_key(rhs)

    def _recover_implicit_return_from_terminal_call(
        self,
        call_op,
        address: str,
        tracer: PcodeTracer,
        condition_tracker: ConditionTracker,
        path_conditions: List[Condition],
        return_index: int,
        all_path_conditions: Optional[List[List[Condition]]] = None,
        active_functions: Optional[Set[Tuple[Any, ...]]] = None,
        current_function=None,
        site_metadata: Optional[Dict[str, Optional[object]]] = None,
    ) -> Optional[List[ReturnInfo]]:
        """`call foo(...); return;` 形式の wrapper を callee summary から復元する。"""
        from ..transform import ExpressionExpander

        expander = ExpressionExpander(
            tracer,
            condition_tracker,
            debug=self.debug,
            call_resolver=self._make_call_resolver(active_functions or set(), current_function),
            effect_summary=self._current_effect_summary,
            parameters=self._current_parameters,
            resolve_callee_parameters=self._get_freshest_callee_parameters,
            read_memory_value=self._read_memory_value,
            image_base=self.program.getImageBase().getOffset(),
            record_deferred_call=self._make_deferred_call_recorder(current_function),
        )

        path_condition_sets = all_path_conditions or []
        if not path_condition_sets:
            path_condition_sets = [path_conditions] if path_conditions else [[]]

        expanded_values = []
        for conds in path_condition_sets:
            expanded_values.extend(
                expander._expand_call_operation(
                    call_op,
                    conds,
                    depth=0,
                    output_size=0,
                )
            )

        if not expanded_values:
            return None

        results = self._build_return_infos_from_expansions(
            address,
            expanded_values,
            return_index,
            site_metadata=site_metadata,
        )
        return results or None

    def _storages_overlap_for_return_recovery(self, left, right) -> bool:
        if left is None or right is None:
            return False
        try:
            if getattr(left, "is_register", False) and getattr(right, "is_register", False):
                return (
                    left.shares_base_register_with(right)
                    and left.bit_range_overlaps_with(right)
                )
        except Exception:
            return False

        return (
            getattr(left, "space_name", None) == getattr(right, "space_name", None)
            and getattr(left, "offset", None) == getattr(right, "offset", None)
            and getattr(left, "size", None) == getattr(right, "size", None)
        )
    
    def _analyze_return_value(
        self,
        return_varnode,
        address: str,
        tracer: PcodeTracer,
        condition_tracker: ConditionTracker,
        path_conditions: List[Condition],
        return_index: int,
        all_path_conditions: Optional[List[List[Condition]]] = None,
        active_functions: Optional[Set[Tuple[Any, ...]]] = None,
        current_function=None,
        site_metadata: Optional[Dict[str, Optional[object]]] = None,
    ) -> List[ReturnInfo]:
        """Return値を解析"""
        from ..transform import ExpressionExpander
        
        tracer.clear_cache()
        
        # MULTIEQUALが含まれるかチェック
        has_multiequal = self._contains_multiequal(return_varnode)
        if has_multiequal:
            self._debug_print("Return value contains MULTIEQUAL - using PHI-based expansion")
            expander = ExpressionExpander(
                tracer,
                condition_tracker,
                debug=self.debug,
                call_resolver=self._make_call_resolver(active_functions or set(), current_function),
                effect_summary=self._current_effect_summary,
                parameters=self._current_parameters,
                resolve_callee_parameters=self._get_freshest_callee_parameters,
                read_memory_value=self._read_memory_value,
                image_base=self.program.getImageBase().getOffset(),
                record_deferred_call=self._make_deferred_call_recorder(current_function),
            )
            expanded_values = expander.expand_from_varnode(return_varnode, [])
        else:
            self._debug_print("Return value has no MULTIEQUAL - using path conditions")
            expander = ExpressionExpander(
                tracer,
                condition_tracker,
                debug=self.debug,
                call_resolver=self._make_call_resolver(active_functions or set(), current_function),
                effect_summary=self._current_effect_summary,
                parameters=self._current_parameters,
                resolve_callee_parameters=self._get_freshest_callee_parameters,
                read_memory_value=self._read_memory_value,
                image_base=self.program.getImageBase().getOffset(),
                record_deferred_call=self._make_deferred_call_recorder(current_function),
            )
            path_condition_sets = all_path_conditions or []
            if not path_condition_sets:
                path_condition_sets = [path_conditions] if path_conditions else [[]]

            expanded_values = []
            for path_idx, conds in enumerate(path_condition_sets):
                if self.debug and len(path_condition_sets) > 1:
                    cond_strs = [
                        ConditionSimplifier.get_simplified_condition_string(c)
                        for c in conds
                    ]
                    self._debug_print(
                        f"Expanding non-PHI return with path[{path_idx}]: {cond_strs}"
                    )
                expanded_values.extend(
                    expander.expand_from_varnode(return_varnode, conds)
                )
        
        self._debug_print(f"Expanded to {len(expanded_values)} candidate(s)")

        results = self._build_return_infos_from_expansions(
            address,
            expanded_values,
            return_index,
            site_metadata=site_metadata,
        )
        
        if not results:
            self._debug_print("WARNING: No valid expansions, falling back to simple trace")
            value = tracer.trace_varnode(return_varnode, use_cache=False)
            simplified_conds = ConditionSimplifier.simplify_conditions_object_centric(
                path_conditions
            )
            resolved_value = self._concretize_readonly_loads(value, simplified_conds, self._current_parameters)
            return [self._make_return_info(
                address=address,
                value=resolved_value,
                conditions=simplified_conds,
                branch_index=return_index,
                site_metadata=site_metadata,
            )]
        
        return results

    def _build_return_infos_from_expansions(
        self,
        address: str,
        expanded_values,
        return_index: int,
        site_metadata: Optional[Dict[str, Optional[object]]] = None,
    ) -> List[ReturnInfo]:
        results = []
        for i, ev in enumerate(expanded_values):
            if not ev.is_valid():
                self._debug_print(f"Skipping contradictory expansion {i}")
                continue

            simplified_conds = ConditionSimplifier.simplify_conditions_object_centric(
                ev.conditions
            )
            if self.debug:
                cond_strs = [
                    ConditionSimplifier.get_simplified_condition_string(c)
                    for c in simplified_conds
                ]
                self._debug_print(
                    f"Expansion {i}: raw={self._debug_expr_identity_summary(ev.value)}"
                )
                self._debug_print(f"  raw_conditions={cond_strs}")
            split_cases = self._split_effect_sensitive_return_case(
                ev.value,
                simplified_conds,
            )
            object_centric_cases: List[Tuple[Expression, List[Condition]]] = []
            for split_value, split_conditions in split_cases:
                object_centric_cases.extend(
                    self._split_object_centric_return_case(
                        split_value,
                        split_conditions,
                    )
                )
            split_cases = object_centric_cases or split_cases
            branch_base = return_index * 100 + i
            for split_index, (split_value, split_conditions) in enumerate(split_cases):
                if self.debug:
                    split_cond_strs = [
                        ConditionSimplifier.get_simplified_condition_string(c)
                        for c in split_conditions
                    ]
                    self._debug_print(
                        f"Expansion {i}.{split_index}: split={self._debug_expr_identity_summary(split_value)}"
                    )
                    self._debug_print(f"  split_conditions={split_cond_strs}")
                preserve_split_value = (
                    not _expressions_equivalent(split_value, ev.value)
                    and not expression_contains_post_state_reads(split_value)
                    and not _expression_contains_observed_loads(split_value)
                )
                normalized_value = (
                    split_value
                    if preserve_split_value
                    else self._normalize_expanded_return_value(
                        split_value,
                        split_conditions,
                    )
                )
                if self.debug and normalized_value is not split_value:
                    self._debug_print(
                        "  normalized="
                        f"{self._debug_expr_identity_summary(normalized_value)}"
                    )
                resolved_value = self._concretize_readonly_loads(
                    normalized_value,
                    split_conditions,
                    self._current_parameters,
                )
                if self.debug and resolved_value is not normalized_value:
                    self._debug_print(
                        "  concretized="
                        f"{self._debug_expr_identity_summary(resolved_value)}"
                    )

                if self.debug:
                    cond_strs = [
                        ConditionSimplifier.get_simplified_condition_string(c)
                        for c in split_conditions
                    ]
                    self._debug_print(
                        f"Expansion {i}.{split_index}: value={self._debug_expr_summary(resolved_value)}"
                    )
                    self._debug_print(f"  conditions={cond_strs}")

                if self._matches_blocked_return_path_conditions(split_conditions):
                    if self.debug:
                        self._debug_print(
                            f"Skipping expansion {i}.{split_index} because its conditions match a blocked noreturn path"
                        )
                    continue

                results.append(
                    self._make_return_info(
                        address=address,
                        value=resolved_value,
                        conditions=split_conditions,
                        branch_index=(
                            branch_base
                            if len(split_cases) == 1
                            else branch_base * 10 + split_index
                        ),
                        site_metadata=site_metadata,
                    )
                )
        pruned = self._prune_less_precise_return_infos(results)
        return self._merge_equivalent_return_infos(pruned)

    def _matches_blocked_return_path_conditions(
        self,
        conditions: List[Condition],
    ) -> bool:
        blocked_sets = getattr(self, "_current_blocked_return_path_conditions", None) or []
        if not blocked_sets:
            return False

        condition_keys = self._build_condition_signature_set(conditions)
        if not condition_keys:
            return False

        for blocked_conditions in blocked_sets:
            blocked_keys = self._build_condition_signature_set(blocked_conditions)
            if blocked_keys and blocked_keys.issubset(condition_keys):
                return True
        return False

    def _split_object_centric_return_case(
        self,
        value: Expression,
        conditions: List[Condition],
    ) -> List[Tuple[Expression, List[Condition]]]:
        expanded = self._expand_object_centric_expression_cases(
            value,
            conditions,
        )
        if not expanded:
            return [(value, conditions)]

        normalized: List[Tuple[Expression, List[Condition]]] = []
        for case_value, case_conditions in expanded:
            simplified_conditions = ConditionSimplifier.simplify_conditions_object_centric(
                list(case_conditions or [])
            )
            if ConditionSimplifier.object_centric_is_contradiction(simplified_conditions):
                continue
            folded_value = self._fold_constant_expression(case_value, fallback_expr=case_value)
            normalized.append((folded_value, simplified_conditions))

        deduplicated = self._deduplicate_expression_cases(normalized)
        if (
            len(deduplicated) == 1
            and _expressions_equivalent(deduplicated[0][0], value)
            and self._condition_lists_equivalent(deduplicated[0][1], conditions)
        ):
            return [(value, conditions)]

        if self.debug and len(deduplicated) > 1:
            self._debug_print(
                "Split return into object-centric value cases: "
                f"{self._debug_expr_identity_summary(value)}"
            )
            for case_index, (case_value, case_conditions) in enumerate(deduplicated):
                cond_dump = [
                    ConditionSimplifier.get_simplified_condition_string(cond)
                    for cond in case_conditions
                ]
                self._debug_print(
                    f"  value-case[{case_index}]: {self._debug_expr_identity_summary(case_value)}"
                )
                self._debug_print(f"    conditions={cond_dump}")
        return deduplicated or [(value, conditions)]

    def _fold_constant_expression(
        self,
        expr: Optional[Expression],
        *,
        fallback_expr: Optional[Expression] = None,
    ) -> Optional[Expression]:
        if expr is None:
            return None
        evaluated = eval_constant_raw(expr)
        if evaluated is None:
            return expr
        raw_value, bits = evaluated
        template = fallback_expr or expr
        size_bytes = int(getattr(template, "size", 0) or 0)
        if size_bytes <= 0:
            size_bytes = max(1, (bits + 7) // 8)
        return Expression.constant(raw_value, size=size_bytes)

    def _split_effect_sensitive_return_case(
        self,
        value: Expression,
        conditions: List[Condition],
    ) -> List[Tuple[Expression, List[Condition]]]:
        effect_summary = self._current_effect_summary
        if effect_summary is None or not effect_summary.effects:
            return [(value, conditions)]

        rewritten = self._rewrite_effect_sensitive_return_value(
            value,
            conditions,
            effect_summary,
        )
        if self.debug and rewritten is not None and not _expressions_equivalent(rewritten, value):
            self._debug_print(
                "Effect-sensitive rewrite candidate: "
                f"{self._debug_expr_identity_summary(value)} -> "
                f"{self._debug_expr_identity_summary(rewritten)}"
            )
        if rewritten is None or _expressions_equivalent(rewritten, value):
            return [(value, conditions)]

        expanded = self._expand_object_centric_expression_cases(
            rewritten,
            conditions,
        )
        if not expanded:
            return [(value, conditions)]
        expanded = [
            (
                self._collapse_effect_sensitive_case_wrapper(
                    value,
                    case_value,
                    case_conditions,
                    effect_summary,
                ),
                case_conditions,
            )
            for case_value, case_conditions in expanded
        ]

        deduplicated = self._deduplicate_expression_cases(expanded)
        if self.debug and deduplicated:
            for case_index, (case_value, case_conditions) in enumerate(deduplicated):
                cond_dump = [
                    ConditionSimplifier.get_simplified_condition_string(cond)
                    for cond in case_conditions
                ]
                self._debug_print(
                    "  effect-sensitive case "
                    f"[{case_index}]: {self._debug_expr_identity_summary(case_value)}"
                )
                self._debug_print(f"    conditions={cond_dump}")
        if (
            len(deduplicated) == 1
            and _expressions_equivalent(deduplicated[0][0], value)
            and self._condition_lists_equivalent(deduplicated[0][1], conditions)
        ):
            return [(value, conditions)]

        if self.debug and len(deduplicated) > 1:
            self._debug_print(
                "Split effect-sensitive expanded return into "
                f"{len(deduplicated)} object-centric cases: "
                f"{self._debug_expr_summary(value)} -> {self._debug_expr_summary(rewritten)}"
            )
        return deduplicated

    def _rewrite_effect_sensitive_return_value(
        self,
        value: Expression,
        conditions: List[Condition],
        effect_summary: EffectSummary,
    ) -> Optional[Expression]:
        precise_object_state_value = self._resolve_precise_object_state_value(
            value,
            conditions,
            effect_summary,
        )
        if precise_object_state_value is not None and precise_object_state_value is not value:
            if self.debug:
                self._debug_print(
                    "Resolved return to precise object-state carrier before generic rewrite: "
                    f"{self._debug_expr_identity_summary(value)} -> "
                    f"{self._debug_expr_identity_summary(precise_object_state_value)}"
                )
            return precise_object_state_value

        for rewrite_kind, rewritten in self._iter_effect_sensitive_rewrite_candidates(
            value,
            conditions,
            effect_summary,
        ):
            accepted = self._accept_effect_sensitive_rewrite(
                value,
                rewritten,
                conditions,
                effect_summary,
                rewrite_kind=rewrite_kind,
            )
            if (
                not accepted
                and self._accept_effect_rewrite_without_rank_gain(
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

    def _resolve_precise_object_state_value(
        self,
        value: Optional[Expression],
        conditions: List[Condition],
        effect_summary: EffectSummary,
    ) -> Optional[Expression]:
        if value is None:
            return None

        candidates: List[Expression] = [value]
        comparison_targets: List[Expression] = [value]
        if _expression_contains_observed_loads(value):
            observed_rewritten = rewrite_observed_loads_from_effects(
                value,
                conditions,
                effect_summary.effects,
                self._current_parameters,
            )
            if observed_rewritten is not None:
                candidates.append(observed_rewritten)
                comparison_targets.append(observed_rewritten)
            observed_post_state = promote_observed_loads_to_post_state_reads(
                value,
                conditions,
                effect_summary.effects,
                self._current_parameters,
                symbolic_post_state=True,
            )
            if observed_post_state is not None:
                comparison_targets.append(observed_post_state)
                lowered_observed_post_state = lower_post_state_expression_for_smt(
                    observed_post_state,
                    conditions,
                    effect_summary.effects,
                    self._current_parameters,
                )
                if lowered_observed_post_state is not None:
                    comparison_targets.append(lowered_observed_post_state)

        for candidate in candidates:
            materialized = _materialize_existing_effect_value_carrier(
                candidate,
                conditions,
                effect_summary.effects,
                self._current_parameters,
            )
            if materialized is None or materialized is candidate:
                continue
            if expression_contains_post_state_reads(materialized):
                continue
            if not any(
                _expressions_equivalent_under_conditions(
                    materialized,
                    comparison_target,
                    conditions,
                    self._current_parameters,
                )
                for comparison_target in comparison_targets
            ):
                continue
            return materialized

        return value

    def _accept_effect_rewrite_without_rank_gain(
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
        if self._rewrite_drops_composite_location_wrapper(original, rewritten, conditions):
            return False
        if expression_contains_post_state_reads(rewritten):
            return True
        original_effect_locations = self._matched_effect_locations(
            original,
            conditions,
            effect_summary,
        )
        rewritten_effect_locations = self._matched_effect_locations(
            rewritten,
            conditions,
            effect_summary,
        )
        if rewritten_effect_locations > original_effect_locations:
            return True

        location = canonicalize_expr_read_location(
            original,
            self._current_parameters,
        )
        if location is None:
            return False

        original_match = _find_matching_effect_value(
            original,
            location,
            conditions,
            effect_summary.effects,
            self._current_parameters,
        )
        rewritten_match = _find_matching_effect_value(
            rewritten,
            location,
            conditions,
            effect_summary.effects,
            self._current_parameters,
        )
        return original_match is None and rewritten_match is not None

    def _rewrite_drops_composite_location_wrapper(
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
            self._current_parameters,
        )
        rewritten_location = canonicalize_expr_read_location(
            rewritten,
            self._current_parameters,
        )
        if (
            original_location is None
            or rewritten_location is None
            or not locations_match(original_location, rewritten_location, conditions)
        ):
            return False
        if not self._is_direct_location_carrier(rewritten):
            return False
        current_effect_summary = self._current_effect_summary
        if (
            current_effect_summary is not None
            and (
                (
                    promote_effect_value_match_to_post_state_read(
                        original,
                        original_location,
                        conditions,
                        current_effect_summary.effects,
                        self._current_parameters,
                        symbolic_post_state=True,
                    )
                    is not None
                )
                or expression_matches_stale_post_state_replay(
                    original,
                    rewritten,
                    conditions,
                    current_effect_summary.effects,
                    self._current_parameters,
                )
            )
        ):
            return False
        return self._expression_has_nontrivial_location_wrapper(
            original,
            original_location,
        )

    def _is_direct_location_carrier(self, expr: Optional[Expression]) -> bool:
        if expr is None:
            return False
        if _expression_location_ref(expr) is not None:
            return True
        return expr.expr_type == ExpressionType.MEMORY and bool(expr.operands)

    def _expression_has_nontrivial_location_wrapper(
        self,
        expr: Optional[Expression],
        location: CanonicalLocation,
    ) -> bool:
        if expr is None:
            return False
        if expr.expr_type == ExpressionType.BINARY_OP and len(expr.operands) == 2:
            for index, operand in enumerate(expr.operands):
                operand_location = canonicalize_expr_read_location(
                    operand,
                    self._current_parameters,
                )
                if operand_location is None or operand_location != location:
                    continue
                other_operand = expr.operands[1 - index]
                if self._wrapper_preserves_collapsed_operand(
                    expr.operator,
                    other_operand,
                    kept_operand_index=index,
                ):
                    return False
                return True
            return False
        if expr.expr_type == ExpressionType.UNARY_OP:
            return True
        if expr.expr_type in {ExpressionType.CALL, ExpressionType.INTRINSIC}:
            return True
        return False

    def _matched_effect_locations(
        self,
        expr: Optional[Expression],
        conditions: List[Condition],
        effect_summary: EffectSummary,
    ) -> set[tuple]:
        matched_locations: set[tuple] = set()
        if expr is None:
            return matched_locations

        for current in _iter_expression_nodes(expr, include_phi_conditions=False):
            location = canonicalize_expr_read_location(current, self._current_parameters)
            if location is None:
                continue
            if _find_matching_effect_value(
                current,
                location,
                conditions,
                effect_summary.effects,
                self._current_parameters,
            ) is None:
                continue
            matched_locations.add(location.stable_key())
        return matched_locations

    def _iter_effect_sensitive_rewrite_candidates(
        self,
        value: Expression,
        conditions: List[Condition],
        effect_summary: EffectSummary,
    ) -> Iterable[Tuple[str, Optional[Expression]]]:
        expr_location = canonicalize_expr_read_location(
            value,
            self._current_parameters,
        )
        nontrivial_location_wrapper = False
        effect_value_matches_wrapper = False
        if expr_location is not None:
            nontrivial_location_wrapper = self._expression_has_nontrivial_location_wrapper(
                value,
                expr_location,
            )
            if nontrivial_location_wrapper:
                effect_value_matches_wrapper = _find_matching_effect_value(
                    value,
                    expr_location,
                    conditions,
                    effect_summary.effects,
                    self._current_parameters,
                ) is not None
        if expr_location is not None:
            post_state_read = resolve_definite_post_state_read_for_location(
                expr_location,
                conditions,
                effect_summary.effects,
                self._current_parameters,
                symbolic_post_state=True,
            )
            if post_state_read is not None:
                yield ("final object-state concrete", lower_post_state_expression_for_smt(
                    post_state_read,
                    conditions,
                    effect_summary.effects,
                    self._current_parameters,
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
                    self._current_parameters,
                ),
            )
        yield (
            "wrapper-preserving effect-sensitive",
            normalize_post_state_expression(
                value,
                conditions,
                effect_summary.effects,
                self._current_parameters,
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
                self._current_parameters,
            ),
        )

    def _collapse_effect_sensitive_case_wrapper(
        self,
        original: Optional[Expression],
        rewritten: Optional[Expression],
        conditions: List[Condition],
        effect_summary: EffectSummary,
    ) -> Optional[Expression]:
        if original is None or rewritten is None:
            return rewritten
        rebuilt_wrapper = self._rebuild_effect_sensitive_case_wrapper(
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
                self._current_parameters,
            )
            if location is None:
                continue
            shared_original = original_operands[1 - original_index]
            for rewritten_index, rewritten_operand in enumerate(rewritten_operands):
                shared_rewritten = rewritten_operands[1 - rewritten_index]
                if not _expressions_equivalent(shared_rewritten, shared_original):
                    continue
                if not self._wrapper_preserves_collapsed_operand(
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
                        self._current_parameters,
                    )
                    is None
                ):
                    continue
                post_state_read = promote_effect_value_carrier_to_post_state_read(
                    rewritten_operand,
                    conditions,
                    effect_summary.effects,
                    self._current_parameters,
                    symbolic_post_state=True,
                )
                if post_state_read is not None:
                    final_replayed = _replay_definite_active_effects_for_location(
                        location,
                        conditions,
                        effect_summary.effects,
                        self._current_parameters,
                    )
                    if final_replayed is not None and _expressions_equivalent_under_conditions(
                        final_replayed,
                        rewritten_operand,
                        conditions,
                        self._current_parameters,
                    ):
                        post_state_read = None
                if self.debug:
                    self._debug_print(
                        "Collapsed duplicate effect-sensitive binary wrapper: "
                        f"{self._debug_expr_identity_summary(rewritten)} -> "
                        f"{self._debug_expr_identity_summary(post_state_read or rewritten_operand)}"
                    )
                return post_state_read or rewritten_operand

        return rewritten

    def _rebuild_effect_sensitive_case_wrapper(
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
                self._current_parameters,
            )
            if location is None:
                continue
            rewritten_without_carrier_ref = _strip_materialized_post_state_value_refs(rewritten)
            if _expression_reads_location(
                rewritten_without_carrier_ref,
                location,
                conditions,
                self._current_parameters,
            ):
                continue
            shared_original = original_operands[1 - original_index]
            if self._wrapper_preserves_collapsed_operand(
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
                    self._current_parameters,
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
            rebuilt = self._fold_constant_expression(rebuilt, fallback_expr=original)
            if self.debug:
                self._debug_print(
                    "Rebuilt effect-sensitive wrapper around branch-local effect value: "
                    f"{self._debug_expr_identity_summary(rewritten)} -> "
                    f"{self._debug_expr_identity_summary(rebuilt)}"
                )
            return rebuilt

        return None

    def _wrapper_preserves_collapsed_operand(
        self,
        operator: Optional[str],
        shared_operand: Optional[Expression],
        *,
        kept_operand_index: int,
    ) -> bool:
        if shared_operand is None or shared_operand.expr_type != ExpressionType.CONSTANT:
            return False

        try:
            shared_value = int(shared_operand.value)
        except Exception:
            return False

        bit_width = max(1, int(shared_operand.get_bit_width() or 0))
        mask = (1 << bit_width) - 1
        normalized = shared_value & mask

        if operator in {"INT_ADD", "INT_OR", "INT_XOR"}:
            return normalized == 0
        if operator == "INT_AND":
            return normalized == mask
        if operator in {"INT_LEFT", "INT_RIGHT", "INT_SRIGHT"}:
            return kept_operand_index == 0 and normalized == 0
        if operator == "INT_SUB":
            return kept_operand_index == 0 and normalized == 0
        return False

    def _accept_effect_sensitive_rewrite(
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

        if self._is_semantically_lossless_effect_sensitive_rewrite(
            original,
            rewritten,
            conditions,
            effect_summary,
        ):
            original_precision = self._effect_sensitive_rewrite_precision(
                original,
                conditions,
                effect_summary,
            )
            rewritten_precision = self._effect_sensitive_rewrite_precision(
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

        original_precision = self._effect_sensitive_rewrite_precision(
            original,
            conditions,
            effect_summary,
        )
        rewritten_precision = self._effect_sensitive_rewrite_precision(
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
            original_rank = self._effect_sensitive_rewrite_rank(original)
            rewritten_rank = self._effect_sensitive_rewrite_rank(rewritten)
            accepted = rewritten_rank > original_rank
        else:
            original_rank = self._effect_sensitive_rewrite_rank(original)
            rewritten_rank = self._effect_sensitive_rewrite_rank(rewritten)

        if self.debug and not accepted:
            self._debug_print(
                f"Rejected {rewrite_kind} rewrite without object-centric precision gain: "
                f"{self._debug_expr_identity_summary(original)} -> "
                f"{self._debug_expr_identity_summary(rewritten)} "
                f"rank {original_rank} -> {rewritten_rank} "
                f"precision {original_precision} -> {rewritten_precision}"
            )

        return accepted

    def _is_semantically_lossless_effect_sensitive_rewrite(
        self,
        original: Optional[Expression],
        rewritten: Optional[Expression],
        conditions: List[Condition],
        effect_summary: EffectSummary,
    ) -> bool:
        if original is None or rewritten is None:
            return False
        if not expression_contains_post_state_reads(rewritten):
            return False
        if not _expression_contains_observed_loads(original):
            return False
        rewritten_location = canonicalize_expr_read_location(
            rewritten,
            self._current_parameters,
        )
        if rewritten_location is not None:
            existing_effect_carrier = promote_effect_value_match_to_post_state_read(
                original,
                rewritten_location,
                conditions,
                effect_summary.effects,
                self._current_parameters,
                symbolic_post_state=True,
            )
            if existing_effect_carrier is not None:
                return False

        comparison_targets: List[Expression] = [original]
        if _expression_contains_observed_loads(original):
            observed_post_state = promote_observed_loads_to_post_state_reads(
                original,
                conditions,
                effect_summary.effects,
                self._current_parameters,
                symbolic_post_state=True,
            )
            if observed_post_state is not None:
                comparison_targets.append(observed_post_state)
                lowered_observed_post_state = lower_post_state_expression_for_smt(
                    observed_post_state,
                    conditions,
                    effect_summary.effects,
                    self._current_parameters,
                )
                if lowered_observed_post_state is not None:
                    comparison_targets.append(lowered_observed_post_state)
            observed_rewritten = rewrite_observed_loads_from_effects(
                original,
                conditions,
                effect_summary.effects,
                self._current_parameters,
            )
            if observed_rewritten is not None:
                comparison_targets.append(observed_rewritten)

        lowered_rewritten = lower_post_state_expression_for_smt(
            rewritten,
            conditions,
            effect_summary.effects,
            self._current_parameters,
        )
        lowered_rewritten = lowered_rewritten if lowered_rewritten is not None else rewritten
        if expression_contains_post_state_reads(lowered_rewritten):
            return False

        for target in comparison_targets:
            lowered_target = lower_post_state_expression_for_smt(
                target,
                conditions,
                effect_summary.effects,
                self._current_parameters,
            )
            candidate = lowered_target if lowered_target is not None else target
            if _expressions_equivalent_under_conditions(
                lowered_rewritten,
                candidate,
                conditions,
                self._current_parameters,
            ):
                return True
        return False

    def _effect_sensitive_rewrite_precision(
        self,
        expr: Optional[Expression],
        conditions: List[Condition],
        effect_summary: EffectSummary,
    ) -> _EffectRewritePrecision:
        matched_locations = len(
            self._matched_effect_locations(expr, conditions, effect_summary)
        )
        post_state_reads = 1 if expression_contains_post_state_reads(expr) else 0
        lowered = expr
        if expr is not None and effect_summary is not None and getattr(effect_summary, "effects", None):
            lowered_candidate = lower_post_state_expression_for_smt(
                expr,
                conditions,
                effect_summary.effects,
                self._current_parameters,
            )
            if lowered_candidate is not None:
                lowered = lowered_candidate

        return _EffectRewritePrecision(
            matched_effect_locations=matched_locations,
            post_state_reads=post_state_reads,
            object_centric_unknowns=self._count_object_centric_unknowns(expr),
            opaque_unknowns=self._count_opaque_unknowns(expr),
            downstream_unresolved_values=self._count_unresolved_value_nodes(lowered),
            observed_loads=self._count_observed_loads(expr),
            phi_nodes=self._count_phi_nodes(expr),
        )

    def _effect_sensitive_rewrite_rank(
        self,
        expr: Optional[Expression],
    ) -> Tuple[int, int, int, int]:
        if expr is None:
            return (0, 0, 0, 0)
        return (
            1 if expression_contains_post_state_reads(expr) else 0,
            1 if self._expression_contains_phi(expr) else 0,
            1 if _expression_contains_observed_loads(expr) else 0,
            self._count_memory_reads(expr),
        )

    def _count_unresolved_value_nodes(self, expr: Optional[Expression]) -> int:
        if expr is None:
            return 1
        count = 1 if expr.expr_type == ExpressionType.UNKNOWN else 0
        if expr.expr_type == ExpressionType.PHI and expr.value:
            for cond, value in expr.value:
                cond_expr = getattr(cond, "expression", None) if cond is not None else None
                if cond_expr is not None:
                    count += self._count_unresolved_value_nodes(cond_expr)
                count += self._count_unresolved_value_nodes(value)
            return count
        for operand in getattr(expr, "operands", []) or []:
            count += self._count_unresolved_value_nodes(operand)
        return count

    def _count_object_centric_unknowns(self, expr: Optional[Expression]) -> int:
        count = 0
        for current in _iter_expression_nodes(expr):
            if getattr(current, "expr_type", None) != ExpressionType.UNKNOWN:
                continue
            runtime_ref = getattr(current, "runtime_ref", None)
            stable_key = getattr(runtime_ref, "stable_key", None)
            if callable(stable_key):
                try:
                    if stable_key() is not None:
                        count += 1
                except Exception:
                    continue
        return count

    def _count_opaque_unknowns(self, expr: Optional[Expression]) -> int:
        count = 0
        for current in _iter_expression_nodes(expr):
            if getattr(current, "expr_type", None) != ExpressionType.UNKNOWN:
                continue
            runtime_ref = getattr(current, "runtime_ref", None)
            kind = getattr(runtime_ref, "kind", None)
            stable_key = getattr(runtime_ref, "stable_key", None)
            if kind == "opaque_unknown" or not callable(stable_key):
                count += 1
        return count

    def _count_observed_loads(self, expr: Optional[Expression]) -> int:
        count = 0
        for current in _iter_expression_nodes(expr, include_phi_conditions=False):
            if _expression_contains_observed_loads(current):
                count += 1
        return count

    def _count_phi_nodes(self, expr: Optional[Expression]) -> int:
        count = 0
        for current in _iter_expression_nodes(expr):
            if getattr(current, "expr_type", None) == ExpressionType.PHI:
                count += 1
        return count

    def _expand_object_centric_expression_cases(
        self,
        expr: Optional[Expression],
        base_conditions: List[Condition],
    ) -> List[Tuple[Expression, List[Condition]]]:
        if expr is None:
            return []

        simplified_base = ConditionSimplifier.simplify_conditions_object_centric(base_conditions)
        if ConditionSimplifier.object_centric_is_contradiction(simplified_base):
            return []
        direct_runtime_guards = self._direct_expression_runtime_guard_conditions(expr)
        if direct_runtime_guards:
            simplified_base = ConditionSimplifier.simplify_conditions_object_centric(
                list(simplified_base) + list(direct_runtime_guards)
            )
            if ConditionSimplifier.object_centric_is_contradiction(simplified_base):
                return []

        folded_expr = self._fold_constant_expression(
            expr,
            fallback_expr=expr,
        )
        if folded_expr is not None:
            expr = folded_expr

        boolean_cases = self._expand_boolean_expression_cases(
            expr,
            simplified_base,
        )
        if boolean_cases is not None:
            return self._deduplicate_expression_cases(boolean_cases)

        if expr.expr_type == ExpressionType.PHI and expr.value:
            expanded: List[Tuple[Expression, List[Condition]]] = []
            prior_guards: List[Condition] = []
            for cond, value in expr.value:
                combined_conditions = list(simplified_base)
                for prior in prior_guards:
                    combined_conditions.append(prior.negate())
                if cond is not None:
                    combined_conditions.append(cond)
                    prior_guards.append(cond)
                nested_conditions = ConditionSimplifier.simplify_conditions_object_centric(
                    combined_conditions
                )
                if ConditionSimplifier.object_centric_is_contradiction(nested_conditions):
                    continue
                expanded.extend(
                    self._expand_object_centric_expression_cases(
                        value,
                        nested_conditions,
                    )
                )
            return self._deduplicate_expression_cases(expanded)

        if expr.expr_type == ExpressionType.MEMORY and expr.operands:
            address_cases = self._expand_object_centric_expression_cases(
                expr.operands[0],
                simplified_base,
            )
            if not address_cases:
                return [(expr, simplified_base)]
            expanded = [
                (expr.clone_with(operands=[address]), case_conditions)
                for address, case_conditions in address_cases
                if not ConditionSimplifier.object_centric_is_contradiction(case_conditions)
            ]
            return self._deduplicate_expression_cases(expanded)

        if expr.expr_type == ExpressionType.UNARY_OP and expr.operands:
            operand_cases = self._expand_object_centric_expression_cases(
                expr.operands[0],
                simplified_base,
            )
            if not operand_cases:
                return [(expr, simplified_base)]
            expanded = []
            for operand, case_conditions in operand_cases:
                if ConditionSimplifier.object_centric_is_contradiction(case_conditions):
                    continue
                rebuilt = expr.clone_with(operands=[operand])
                rebuilt = self._fold_constant_expression(rebuilt, fallback_expr=expr)
                expanded.append((rebuilt, case_conditions))
            return self._deduplicate_expression_cases(expanded)

        if expr.expr_type == ExpressionType.BINARY_OP and len(expr.operands) == 2:
            left_cases = self._expand_object_centric_expression_cases(
                expr.operands[0],
                simplified_base,
            )
            right_cases = self._expand_object_centric_expression_cases(
                expr.operands[1],
                simplified_base,
            )
            if not left_cases:
                left_cases = [(expr.operands[0], simplified_base)]
            if not right_cases:
                right_cases = [(expr.operands[1], simplified_base)]

            expanded: List[Tuple[Expression, List[Condition]]] = []
            for left_value, left_conditions in left_cases:
                for right_value, right_conditions in right_cases:
                    combined_conditions = ConditionSimplifier.simplify_conditions_object_centric(
                        list(simplified_base) + list(left_conditions) + list(right_conditions)
                    )
                    if ConditionSimplifier.object_centric_is_contradiction(combined_conditions):
                        continue
                    rebuilt = expr.clone_with(operands=[left_value, right_value])
                    rebuilt = self._fold_constant_expression(rebuilt, fallback_expr=expr)
                    expanded.append(
                        (
                            rebuilt,
                            combined_conditions,
                        )
                    )
            return self._deduplicate_expression_cases(expanded)

        return [(expr, simplified_base)]

    def _expand_boolean_expression_cases(
        self,
        expr: Optional[Expression],
        base_conditions: List[Condition],
    ) -> Optional[List[Tuple[Expression, List[Condition]]]]:
        if expr is None or not self._is_boolean_expression(expr):
            return None

        condition = Condition(expr, False)
        if ConditionSimplifier.object_centric_is_contradiction(
            list(base_conditions) + [condition.negate()]
        ):
            return [(Expression.constant(1, size=max(1, expr.size or 1)), base_conditions)]
        if ConditionSimplifier.object_centric_is_contradiction(
            list(base_conditions) + [condition]
        ):
            return [(Expression.constant(0, size=max(1, expr.size or 1)), base_conditions)]

        true_conditions = ConditionSimplifier.simplify_conditions_object_centric(
            list(base_conditions) + [condition]
        )
        false_conditions = ConditionSimplifier.simplify_conditions_object_centric(
            list(base_conditions) + [condition.negate()]
        )

        cases: List[Tuple[Expression, List[Condition]]] = []
        if not ConditionSimplifier.object_centric_is_contradiction(true_conditions):
            cases.append((Expression.constant(1, size=max(1, expr.size or 1)), true_conditions))
        if not ConditionSimplifier.object_centric_is_contradiction(false_conditions):
            cases.append((Expression.constant(0, size=max(1, expr.size or 1)), false_conditions))
        if not cases:
            return []
        return cases

    def _is_boolean_expression(self, expr: Optional[Expression]) -> bool:
        if expr is None:
            return False
        if expr.expr_type == ExpressionType.BINARY_OP:
            return expr.operator in {
                "INT_EQUAL",
                "INT_NOTEQUAL",
                "INT_LESS",
                "INT_LESSEQUAL",
                "INT_SLESS",
                "INT_SLESSEQUAL",
                "BOOL_AND",
                "BOOL_OR",
                "BOOL_XOR",
            }
        return expr.expr_type == ExpressionType.UNARY_OP and expr.operator == "BOOL_NEGATE"

    def _deduplicate_expression_cases(
        self,
        cases: List[Tuple[Expression, List[Condition]]],
    ) -> List[Tuple[Expression, List[Condition]]]:
        deduplicated: List[Tuple[Expression, List[Condition]]] = []
        for value, conditions in cases:
            simplified_conditions = ConditionSimplifier.simplify_conditions_object_centric(
                conditions
            )
            if ConditionSimplifier.object_centric_is_contradiction(simplified_conditions):
                continue
            duplicate = False
            for existing_value, existing_conditions in deduplicated:
                if (
                    _expressions_equivalent(existing_value, value)
                    and self._condition_lists_equivalent(existing_conditions, simplified_conditions)
                ):
                    duplicate = True
                    break
            if not duplicate:
                deduplicated.append((value, simplified_conditions))
        return deduplicated

    def _condition_lists_equivalent(
        self,
        left: List[Condition],
        right: List[Condition],
    ) -> bool:
        if len(left) != len(right):
            return False
        unmatched = list(right)
        for left_condition in left:
            matched_index = next(
                (
                    index for index, right_condition in enumerate(unmatched)
                    if ConditionNormalizer.are_equivalent(left_condition, right_condition)
                ),
                None,
            )
            if matched_index is None:
                return False
            unmatched.pop(matched_index)
        return not unmatched

    def _prune_less_precise_return_infos(
        self,
        return_infos: List[ReturnInfo],
    ) -> List[ReturnInfo]:
        if len(return_infos) < 2:
            return return_infos

        grouped: Dict[Tuple[str, str], List[ReturnInfo]] = {}
        for info in return_infos:
            key = (
                self._return_site_key(info),
                self._pruning_conditions_signature(info.conditions),
            )
            grouped.setdefault(key, []).append(info)

        pruned: List[ReturnInfo] = []
        for group in grouped.values():
            precise_group = [
                info
                for info in group
                if not self._expression_contains_unresolved_value(info.value)
            ]
            unresolved_group = [
                info
                for info in group
                if self._expression_contains_unresolved_value(info.value)
            ]
            if not precise_group or not unresolved_group:
                pruned.extend(group)
                continue

            canonical_precise = precise_group[0]
            precise_values_are_unanimous = all(
                _expressions_equivalent(canonical_precise.value, info.value)
                for info in precise_group[1:]
            )
            if not precise_values_are_unanimous:
                if self.debug:
                    self._debug_print(
                        "Preserved unresolved return cases because precise cases "
                        "under the same condition region disagree"
                    )
                pruned.extend(group)
                continue

            dropped = len(unresolved_group)
            if dropped > 0 and self.debug:
                self._debug_print(
                    "Dropped less precise unresolved return cases under an "
                    "already-resolved condition region"
                )
            pruned.extend(precise_group)

        return pruned

    def _exclusivize_return_regions(
        self,
        return_infos: List[ReturnInfo],
    ) -> List[ReturnInfo]:
        preserved: List[ReturnInfo] = []
        ordered_return_infos = sorted(
            enumerate(return_infos),
            key=cmp_to_key(self._compare_return_region_order),
        )
        for index, (original_index, info) in enumerate(ordered_return_infos):
            current_regions: List[List[Condition]] = [
                self._return_info_effective_region_conditions(info)
            ]
            if ConditionSimplifier.object_centric_is_contradiction(current_regions[0]):
                continue

            for other_index, (_other_original_index, other) in enumerate(ordered_return_infos):
                if other_index >= index:
                    break
                if _expressions_equivalent(other.value, info.value):
                    continue

                other_conditions = self._return_info_effective_region_conditions(other)
                next_regions: List[List[Condition]] = []
                for region in current_regions:
                    if ConditionSimplifier.object_centric_is_contradiction(region):
                        continue
                    if not ConditionSimplifier.build_constraint_set(region).overlaps_with(other_conditions):
                        next_regions.append(region)
                        continue
                    if not self._return_region_can_be_shadowed_by_prior(
                        region,
                        info,
                        other,
                        prior_conditions=other_conditions,
                    ):
                        next_regions.append(region)
                        continue
                    next_regions.extend(
                        self._subtract_return_region_conjunction(
                            region,
                            other_conditions,
                        )
                    )
                current_regions = [
                    region
                    for region in next_regions
                    if not ConditionSimplifier.object_centric_is_contradiction(region)
                ]
                if not current_regions:
                    break

            for split_index, region in enumerate(current_regions):
                preserved.append(
                    self._make_return_info(
                        address=info.address,
                        value=info.value,
                        conditions=region,
                        branch_index=self._split_branch_index(info.branch_index, original_index, split_index),
                        site_metadata={
                            "pcode_identity": info.pcode_identity,
                            "pcode_order": info.pcode_order,
                            "pcode_time": info.pcode_time,
                        },
                    )
                )
        return preserved

    def _return_info_effective_region_conditions(
        self,
        info: ReturnInfo,
    ) -> List[Condition]:
        """ReturnInfo conditions plus proof/runtime guards carried by its value."""

        conditions = list(getattr(info, "conditions", None) or [])
        conditions.extend(self._expression_runtime_guard_conditions(getattr(info, "value", None)))
        return ConditionSimplifier.simplify_conditions_object_centric(conditions)

    def _expression_runtime_guard_conditions(
        self,
        expr: Optional[Expression],
    ) -> List[Condition]:
        guards: List[Condition] = []
        seen: Set[tuple] = set()
        for node in self._iter_expression_nodes_for_unconditional_runtime_guards(expr):
            runtime_ref = getattr(node, "runtime_ref", None)
            for guard in self._runtime_ref_guard_conditions(runtime_ref):
                try:
                    key = guard.structural_key(budget=256)
                except Exception:
                    key = (id(guard),)
                if key in seen:
                    continue
                seen.add(key)
                guards.append(guard)
        return guards

    def _iter_expression_nodes_for_unconditional_runtime_guards(
        self,
        expr: Optional[Expression],
    ):
        if expr is None:
            return
        stack = [expr]
        while stack:
            current = stack.pop()
            if current is None:
                continue
            yield current
            if getattr(current, "expr_type", None) == ExpressionType.PHI:
                continue
            operands = getattr(current, "operands", None) or ()
            stack.extend(reversed([operand for operand in operands if operand is not None]))

    def _direct_expression_runtime_guard_conditions(
        self,
        expr: Optional[Expression],
    ) -> List[Condition]:
        if expr is None:
            return []
        return self._runtime_ref_guard_conditions(getattr(expr, "runtime_ref", None))

    def _runtime_ref_guard_conditions(
        self,
        runtime_ref,
    ) -> List[Condition]:
        guards: List[Condition] = []
        for owner in (
            runtime_ref,
            getattr(runtime_ref, "accumulator_proof", None),
            getattr(runtime_ref, "loop_summary", None),
        ):
            for guard in tuple(getattr(owner, "guard_constraints", ()) or ()):
                if isinstance(guard, Condition):
                    guards.append(guard)
        return guards

    def _return_region_priority_key(
        self,
        info: ReturnInfo,
        original_index: int,
    ) -> Tuple[int, int, int, int, int, int]:
        conditions = self._return_info_effective_region_conditions(info)
        exact_equality_count = sum(
            1 for condition in conditions if self._condition_is_constant_equality_guard(condition)
        )
        readonly_contract_score = self._readonly_reduction_contract_priority_score(info)
        unresolved_score = 1 if self._expression_contains_unresolved_value(info.value) else 0
        phi_score = 1 if self._expression_contains_phi(info.value) else 0
        return (
            -int(exact_equality_count),
            -int(readonly_contract_score),
            -len(conditions),
            unresolved_score,
            phi_score,
            int(original_index),
        )

    def _compare_return_region_order(
        self,
        left_item: Tuple[int, ReturnInfo],
        right_item: Tuple[int, ReturnInfo],
    ) -> int:
        left_original_index, left = left_item
        right_original_index, right = right_item
        left_conditions = self._return_info_effective_region_conditions(left)
        right_conditions = self._return_info_effective_region_conditions(right)

        if not ConditionSimplifier.object_centric_is_contradiction(
            list(left_conditions) + list(right_conditions)
        ):
            left_implies_right = self._return_region_conditions_imply(
                left_conditions,
                right_conditions,
            )
            right_implies_left = self._return_region_conditions_imply(
                right_conditions,
                left_conditions,
            )
            if left_implies_right and not right_implies_left:
                return -1
            if right_implies_left and not left_implies_right:
                return 1

        left_key = self._return_region_priority_key(left, left_original_index)
        right_key = self._return_region_priority_key(right, right_original_index)
        if left_key < right_key:
            return -1
        if left_key > right_key:
            return 1
        return 0

    def _return_region_can_be_shadowed_by_prior(
        self,
        region: Sequence[Condition],
        current: ReturnInfo,
        prior: ReturnInfo,
        *,
        prior_conditions: Optional[Sequence[Condition]] = None,
    ) -> bool:
        prior_conditions = ConditionSimplifier.simplify_conditions_object_centric(
            prior_conditions
            if prior_conditions is not None
            else self._return_info_effective_region_conditions(prior)
        )
        if not self._return_region_conditions_mutually_imply(region, prior_conditions):
            return True

        prior_score = self._readonly_reduction_contract_priority_score(prior)
        current_score = self._readonly_reduction_contract_priority_score(current)
        if prior_score > current_score:
            return True
        if current_score > prior_score:
            return False

        # Same condition region with different values is not a valid partition
        # refinement unless one side carries a proof-backed semantic contract.
        return False

    def _return_region_conditions_imply(
        self,
        antecedent: Sequence[Condition],
        consequent: Sequence[Condition],
    ) -> bool:
        consequent = list(consequent or [])
        if not consequent:
            return True
        antecedent_set = ConditionSimplifier.build_constraint_set(antecedent or [])
        if antecedent_set.is_contradictory:
            return False
        return antecedent_set.implies_all(consequent)

    def _return_region_conditions_mutually_imply(
        self,
        left: Sequence[Condition],
        right: Sequence[Condition],
    ) -> bool:
        return self._return_region_conditions_imply(
            left,
            right,
        ) and self._return_region_conditions_imply(
            right,
            left,
        )

    def _condition_is_constant_equality_guard(self, condition: Condition) -> bool:
        if condition is None:
            return False
        expr = getattr(condition, "expression", None)
        if expr is None or getattr(expr, "expr_type", None) != ExpressionType.BINARY_OP:
            return False
        if self._condition_logical_operator(condition) != "INT_EQUAL" or len(getattr(expr, "operands", ()) or ()) != 2:
            return False
        left, right = expr.operands
        left_is_const = getattr(left, "expr_type", None) == ExpressionType.CONSTANT
        right_is_const = getattr(right, "expr_type", None) == ExpressionType.CONSTANT
        return left_is_const != right_is_const

    def _condition_logical_operator(
        self,
        condition: Condition,
    ) -> Optional[str]:
        expr = getattr(condition, "expression", None)
        if expr is None or getattr(expr, "expr_type", None) != ExpressionType.BINARY_OP:
            return None
        operator = getattr(expr, "operator", None)
        if not getattr(condition, "negated", False):
            return operator
        if operator == "INT_EQUAL":
            return "INT_NOTEQUAL"
        if operator == "INT_NOTEQUAL":
            return "INT_EQUAL"
        return operator

    def _readonly_reduction_contract_priority_score(
        self,
        info: ReturnInfo,
    ) -> int:
        best_score = 0
        for node in _iter_expression_nodes(info.value, include_phi_conditions=False):
            runtime_ref = getattr(node, "runtime_ref", None)
            if isinstance(runtime_ref, ReadonlyReductionRef):
                best_score = max(
                    best_score,
                    self._readonly_reduction_ref_contract_priority_score(runtime_ref),
                )
        return best_score

    def _readonly_reduction_ref_contract_priority_score(
        self,
        runtime_ref: ReadonlyReductionRef,
    ) -> int:
        proof = getattr(runtime_ref, "accumulator_proof", None)
        if proof is None:
            return 0
        if not bool(getattr(proof, "return_region_value_proven", False)):
            return 0
        contract_key = None
        contract_key_fn = getattr(runtime_ref, "readonly_term_sequence_contract_key", None)
        if callable(contract_key_fn):
            try:
                contract_key = contract_key_fn()
            except (AttributeError, TypeError, ValueError):
                contract_key = None
        if contract_key is None:
            return 0

        semantic_witnesses = tuple(getattr(runtime_ref, "semantic_witnesses", ()) or ())
        exact_return_witnesses = tuple(getattr(proof, "exact_return_witnesses", ()) or ())
        loop_body_witnesses = tuple(getattr(proof, "loop_body_witnesses", ()) or ())
        seed_terms = tuple(getattr(proof, "seed_terms", ()) or ())
        return 1 + len(semantic_witnesses) + len(exact_return_witnesses) + len(loop_body_witnesses) + len(seed_terms)

    def _subtract_return_region_conjunction(
        self,
        base_conditions: List[Condition],
        subtract_conditions: List[Condition],
    ) -> List[List[Condition]]:
        base = ConditionSimplifier.simplify_conditions_object_centric(base_conditions or [])
        subtract = ConditionSimplifier.simplify_conditions_object_centric(subtract_conditions or [])

        if not subtract:
            return [base]

        overlap = ConditionSimplifier.simplify_conditions_object_centric(base + subtract)
        if ConditionSimplifier.object_centric_is_contradiction(overlap):
            return [base]

        base_constraint_set = ConditionSimplifier.build_constraint_set(base)
        if base_constraint_set.implies_all(subtract):
            return []

        subtract_constraint_set = ConditionSimplifier.build_constraint_set(subtract)
        subtract_residual = subtract_constraint_set.residual_against(base)
        if not subtract_residual:
            return []

        residual_regions: List[List[Condition]] = []
        required_prefix: List[Condition] = []

        for condition in subtract_residual:
            candidate = ConditionSimplifier.simplify_conditions_object_centric(
                list(base) + list(required_prefix) + [condition.negate()]
            )
            if not ConditionSimplifier.object_centric_is_contradiction(candidate):
                residual_regions.append(candidate)
            required_prefix.append(condition)

        return residual_regions

    def _split_branch_index(
        self,
        branch_index: Optional[int],
        original_index: int,
        split_index: int,
    ) -> Optional[int]:
        seed = branch_index if branch_index is not None else (original_index + 1) * 1000
        return seed * 10 + split_index

    def _analysis_has_ambiguous_condition_region_returns(
        self,
        analysis: Optional[FunctionReturnAnalysis],
    ) -> bool:
        if analysis is None or len(analysis.returns or []) < 2:
            return False

        grouped: Dict[Tuple[str, str], List[ReturnInfo]] = {}
        for info in analysis.returns or []:
            key = (
                self._return_site_key(info),
                self._pruning_conditions_signature(info.conditions),
            )
            grouped.setdefault(key, []).append(info)

        for group in grouped.values():
            precise_group = [
                info
                for info in group
                if not self._expression_contains_unresolved_value(info.value)
            ]
            if len(precise_group) < 2:
                continue
            first = precise_group[0]
            if any(
                not _expressions_equivalent(first.value, candidate.value)
                for candidate in precise_group[1:]
            ):
                return True
        return False

    def _pruning_conditions_signature(
        self,
        conditions: List[Condition],
    ):
        parts = [
            ConditionNormalizer.normalize_for_contradiction(condition)
            for condition in (conditions or [])
        ]
        parts.sort()
        return tuple(parts)

    def _merge_equivalent_return_infos(
        self,
        return_infos: List[ReturnInfo],
    ) -> List[ReturnInfo]:
        if len(return_infos) < 2:
            return return_infos

        merged = list(return_infos)
        changed = True
        while changed:
            changed = False
            for i in range(len(merged)):
                for j in range(i + 1, len(merged)):
                    combined = self._merge_return_info_pair(
                        merged[i],
                        merged[j],
                        merged,
                        i,
                        j,
                    )
                    if combined is None:
                        continue
                    merged[i] = combined
                    del merged[j]
                    changed = True
                    break
                if changed:
                    break
        return merged

    def _merge_return_info_pair(
        self,
        left: ReturnInfo,
        right: ReturnInfo,
        all_infos: Optional[List[ReturnInfo]] = None,
        left_index: Optional[int] = None,
        right_index: Optional[int] = None,
    ) -> Optional[ReturnInfo]:
        if self._return_site_key(left) != self._return_site_key(right):
            return None
        if not _expressions_equivalent(left.value, right.value):
            return None

        shared_conditions, left_residual, right_residual = self._partition_return_conditions(
            left.conditions,
            right.conditions,
        )

        if not left_residual and not right_residual:
            return self._make_merged_return_info(left, right, shared_conditions, "deduplicated identical return case")

        if (
            self._condition_sets_are_complementary(left_residual, right_residual)
            and self._can_safely_collapse_complementary_return_pair(
                left,
                right,
                shared_conditions,
                all_infos or [],
                left_index,
                right_index,
            )
        ):
            return self._make_merged_return_info(
                left,
                right,
                shared_conditions,
                "collapsed complementary return cases",
            )

        return None

    def _can_safely_collapse_complementary_return_pair(
        self,
        left: ReturnInfo,
        right: ReturnInfo,
        merged_conditions: List[Condition],
        all_infos: List[ReturnInfo],
        left_index: Optional[int],
        right_index: Optional[int],
    ) -> bool:
        current_effect_summary = self._current_effect_summary
        if (
            current_effect_summary is not None
            and (
                expression_contains_post_state_reads(left.value)
                or expression_contains_post_state_reads(right.value)
            )
        ):
            lowered_left = lower_post_state_expression_for_smt(
                left.value,
                left.conditions,
                current_effect_summary.effects,
                self._current_parameters,
            )
            lowered_right = lower_post_state_expression_for_smt(
                right.value,
                right.conditions,
                current_effect_summary.effects,
                self._current_parameters,
            )
            if (
                lowered_left is None
                or lowered_right is None
                or expression_contains_post_state_reads(lowered_left)
                or expression_contains_post_state_reads(lowered_right)
            ):
                return False
            if not _expressions_equivalent_under_conditions(
                lowered_left,
                lowered_right,
                merged_conditions,
                self._current_parameters,
            ):
                if self.debug:
                    self._debug_print(
                        "skipping complementary return-case collapse because symbolic post-state "
                        "lowers differently across branches: "
                        f"left={self._debug_expr_summary(lowered_left)} "
                        f"right={self._debug_expr_summary(lowered_right)}"
                    )
                return False

        if not all_infos:
            return True

        merged_scope = ConditionSimplifier.simplify_conditions_object_centric(list(merged_conditions))
        for index, other in enumerate(all_infos):
            if index == left_index or index == right_index:
                continue
            if self._return_site_key(other) != self._return_site_key(left):
                continue
            if _expressions_equivalent(other.value, left.value):
                continue

            overlap_conditions = ConditionSimplifier.simplify_conditions_object_centric(
                list(merged_scope) + list(other.conditions)
            )
            if ConditionSimplifier.object_centric_is_contradiction(overlap_conditions):
                continue

            if self.debug:
                cond_dump = [
                    ConditionSimplifier.get_simplified_condition_string(cond)
                    for cond in overlap_conditions
                ]
                self._debug_print(
                    "skipping complementary return-case collapse due to overlapping "
                    f"different-valued case: value={self._debug_expr_summary(other.value)} "
                    f"conditions={cond_dump}"
                )
            return False

        return True

    def _condition_sets_are_complementary(
        self,
        left_conditions: List[Condition],
        right_conditions: List[Condition],
    ) -> bool:
        if not left_conditions or not right_conditions:
            return False
        if len(left_conditions) != len(right_conditions):
            return False

        unmatched = list(right_conditions)
        for left_condition in left_conditions:
            match_index = None
            for index, right_condition in enumerate(unmatched):
                if left_condition.equals(right_condition.negate()) or left_condition.negate().equals(right_condition):
                    match_index = index
                    break
            if match_index is None:
                return False
            unmatched.pop(match_index)
        return not unmatched

    def _partition_return_conditions(
        self,
        left_conditions: List[Condition],
        right_conditions: List[Condition],
    ) -> Tuple[List[Condition], List[Condition], List[Condition]]:
        shared: List[Condition] = []
        right_used: Set[int] = set()
        left_residual: List[Condition] = []

        for left_cond in left_conditions:
            match_index = None
            for index, right_cond in enumerate(right_conditions):
                if index in right_used:
                    continue
                if left_cond.equals(right_cond):
                    match_index = index
                    break
            if match_index is None:
                left_residual.append(left_cond)
                continue
            right_used.add(match_index)
            shared.append(left_cond)

        right_residual = [
            cond for index, cond in enumerate(right_conditions) if index not in right_used
        ]
        return (
            ConditionSimplifier.simplify_conditions_object_centric(shared),
            ConditionSimplifier.simplify_conditions_object_centric(left_residual),
            ConditionSimplifier.simplify_conditions_object_centric(right_residual),
        )

    def _make_merged_return_info(
        self,
        primary: ReturnInfo,
        secondary: ReturnInfo,
        merged_conditions: List[Condition],
        reason: str,
    ) -> ReturnInfo:
        normalized_conditions = ConditionSimplifier.simplify_conditions_object_centric(
            list(merged_conditions)
        )
        if self.debug:
            cond_dump = [
                ConditionSimplifier.get_simplified_condition_string(cond)
                for cond in normalized_conditions
            ]
            self._debug_print(
                f"{reason}: value={self._debug_expr_summary(primary.value)} conditions={cond_dump}"
            )
        return self._make_return_info(
            address=primary.address,
            value=primary.value,
            conditions=normalized_conditions,
            branch_index=self._min_branch_index(primary.branch_index, secondary.branch_index),
            site_metadata={
                "pcode_identity": primary.pcode_identity,
                "pcode_order": primary.pcode_order,
                "pcode_time": primary.pcode_time,
            },
        )

    def _min_branch_index(
        self,
        left: Optional[int],
        right: Optional[int],
    ) -> Optional[int]:
        if left is None:
            return right
        if right is None:
            return left
        return min(left, right)

    def _normalize_expanded_return_value(
        self,
        value: Expression,
        conditions: List[Condition],
    ) -> Expression:
        normalized_value = value
        started_with_phi = self._expression_contains_phi(value)
        effect_summary = self._current_effect_summary
        has_effects = effect_summary is not None and bool(effect_summary.effects)

        if started_with_phi:
            reduced_value = _reduce_expression_under_conditions(value, conditions)
            if reduced_value is not None:
                normalized_value = reduced_value
            if self.debug and normalized_value is not value:
                self._debug_print(
                    "Reduced PHI-bearing expanded return under active conditions: "
                    f"{self._debug_expr_summary(value)} -> {self._debug_expr_summary(normalized_value)}"
                )

        if has_effects:
            assert effect_summary is not None
            canonicalized = self._normalize_return_value_with_effect_summary(
                normalized_value,
                conditions,
                effect_summary,
            )
            if canonicalized is not None:
                if self.debug and canonicalized is not normalized_value:
                    self._debug_print(
                        "Normalized expanded return with definite post-state replay: "
                        f"{self._debug_expr_summary(normalized_value)} -> "
                        f"{self._debug_expr_summary(canonicalized)}"
                    )
                normalized_value = canonicalized

        return normalized_value

    def _normalize_return_value_with_effect_summary(
        self,
        value: Expression,
        conditions: List[Condition],
        effect_summary: EffectSummary,
    ) -> Optional[Expression]:
        carrier_post_state_read = promote_effect_value_carrier_to_post_state_read(
            value,
            conditions,
            effect_summary.effects,
            self._current_parameters,
            symbolic_post_state=True,
        )
        atomic_object_state_value = _materialize_existing_effect_value_carrier(
            value,
            conditions,
            effect_summary.effects,
            self._current_parameters,
        )
        if (
            atomic_object_state_value is not None
            and atomic_object_state_value is not value
            and isinstance(getattr(atomic_object_state_value, "runtime_ref", None), PostStateValueRef)
            and self._count_memory_reads(value) > 1
        ):
            return atomic_object_state_value

        canonicalized = normalize_post_state_expression(
            value,
            conditions,
            effect_summary.effects,
            self._current_parameters,
            prefer_canonical_post_state=True,
            symbolic_post_state=True,
        )
        canonicalized = self._collapse_effect_sensitive_case_wrapper(
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
            self._current_parameters,
        )
        original_location = canonicalize_expr_read_location(
            value,
            self._current_parameters,
        )
        if original_location is None:
            original_location = _find_unique_effect_location_for_value(
                value,
                conditions,
                effect_summary.effects,
                self._current_parameters,
            )
        carrier_matches_wrapped_object = (
            carrier_post_state_read is not None
            and original_location is not None
            and (
                self._expression_has_nontrivial_location_wrapper(value, original_location)
                or value.expr_type != ExpressionType.MEMORY
            )
        )
        if carrier_matches_wrapped_object:
            materialized_canonicalized = carrier_post_state_read
            drops_composite_wrapper = False
        else:
            drops_composite_wrapper = self._rewrite_drops_composite_location_wrapper(
                value,
                materialized_canonicalized,
                conditions,
            )
        if (
            not drops_composite_wrapper
            and original_location is not None
            and self._expression_has_nontrivial_location_wrapper(value, original_location)
            and isinstance(getattr(materialized_canonicalized, "runtime_ref", None), PostStateValueRef)
        ):
            distinct_read_locations = {
                location.stable_key()
                for node in _iter_expression_nodes(value, include_phi_conditions=False)
                for location in (
                    canonicalize_expr_read_location(
                        node,
                        self._current_parameters,
                    ),
                )
                if location is not None
            }
            if len(distinct_read_locations) == 1:
                lowered_materialized = lower_post_state_expression_for_smt(
                    materialized_canonicalized,
                    conditions,
                    effect_summary.effects,
                    self._current_parameters,
                )
                if lowered_materialized is None or not _expressions_equivalent_under_conditions(
                    lowered_materialized,
                    value,
                    conditions,
                    self._current_parameters,
                ):
                    drops_composite_wrapper = True
        if drops_composite_wrapper:
            wrapper_preserving = normalize_post_state_expression(
                value,
                conditions,
                effect_summary.effects,
                self._current_parameters,
                prefer_canonical_post_state=False,
                preserve_composite_location_wrappers=True,
            )
            canonicalized = wrapper_preserving if wrapper_preserving is not None else canonicalized
        else:
            if carrier_post_state_read is not None:
                canonicalized = carrier_post_state_read
            else:
                canonicalized = materialized_canonicalized
        canonicalized = self._prefer_lossless_materialized_post_state_roundtrip(
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
            self._current_parameters,
        ):
            return canonicalized
        if self._should_replay_canonicalized_return(canonicalized, value):
            replayed = normalize_post_state_expression(
                canonicalized,
                conditions,
                effect_summary.effects,
                self._current_parameters,
                prefer_canonical_post_state=False,
            )
            if replayed is not None:
                canonicalized = replayed

        if self._symbolic_post_state_roundtrip_rejected(canonicalized, value, conditions, effect_summary):
            if self.debug:
                self._debug_print(
                    "Rejected symbolic post-state canonicalization due to non-equivalent round trip: "
                    f"{self._debug_expr_summary(value)} -> "
                    f"{self._debug_expr_summary(canonicalized)}"
                )
            fallback_replayed = None
            if carrier_post_state_read is not None:
                fallback_replayed = carrier_post_state_read
            if fallback_replayed is None and value.expr_type == ExpressionType.MEMORY:
                fallback_replayed = materialize_definite_post_state_expression(
                    value,
                    conditions,
                    effect_summary.effects,
                    self._current_parameters,
                    preserve_composite_location_wrappers=True,
                )
            if fallback_replayed is None or _expressions_equivalent(fallback_replayed, value):
                fallback_replayed = normalize_post_state_expression(
                    value,
                    conditions,
                    effect_summary.effects,
                    self._current_parameters,
                    prefer_canonical_post_state=False,
                    preserve_composite_location_wrappers=True,
                )
            return fallback_replayed if fallback_replayed is not None else value

        return canonicalized

    def _prefer_lossless_materialized_post_state_roundtrip(
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
            self._current_parameters,
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
            self._current_parameters,
        )
        if lowered_roundtrip is None:
            return canonicalized
        if expression_contains_post_state_reads(lowered_roundtrip):
            return canonicalized
        if not _expressions_equivalent_under_conditions(
            lowered_roundtrip,
            original,
            conditions,
            self._current_parameters,
        ):
            return canonicalized
        return lowered_roundtrip

    def _should_replay_canonicalized_return(
        self,
        canonicalized: Optional[Expression],
        original: Expression,
    ) -> bool:
        return (
            canonicalized is not None
            and not _expressions_equivalent(canonicalized, original)
            and not expression_contains_post_state_reads(canonicalized)
            and self._count_memory_reads(canonicalized) > self._count_memory_reads(original)
        )

    def _symbolic_post_state_roundtrip_rejected(
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
            self._current_parameters,
        )
        if lowered_roundtrip is None:
            return True

        comparison_targets = [original]
        if original.expr_type == ExpressionType.MEMORY:
            expected_roundtrip = materialize_definite_post_state_expression(
                original,
                conditions,
                effect_summary.effects,
                self._current_parameters,
                preserve_composite_location_wrappers=True,
            )
            if expected_roundtrip is not None:
                comparison_targets.insert(0, expected_roundtrip)
        if _expression_contains_observed_loads(original):
            observed_post_state = promote_observed_loads_to_post_state_reads(
                original,
                conditions,
                effect_summary.effects,
                self._current_parameters,
                symbolic_post_state=True,
            )
            if observed_post_state is not None:
                comparison_targets.append(observed_post_state)
                lowered_observed_post_state = lower_post_state_expression_for_smt(
                    observed_post_state,
                    conditions,
                    effect_summary.effects,
                    self._current_parameters,
                )
                if lowered_observed_post_state is not None:
                    comparison_targets.append(lowered_observed_post_state)
            observed_rewritten = rewrite_observed_loads_from_effects(
                original,
                conditions,
                effect_summary.effects,
                self._current_parameters,
            )
            if observed_rewritten is not None:
                comparison_targets.append(observed_rewritten)
            observed_roundtrip = normalize_post_state_expression(
                original,
                conditions,
                effect_summary.effects,
                self._current_parameters,
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
                self._current_parameters,
            ):
                return False
        if self._expression_contains_stale_effect_value_for_post_state(
            original,
            canonicalized,
            conditions,
            effect_summary,
        ):
            return False
        return True

    def _expression_contains_stale_effect_value_for_post_state(
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
            location = canonicalize_expr_read_location(current, self._current_parameters)
            if location is not None:
                promoted = promote_effect_value_match_to_post_state_read(
                    current,
                    location,
                    conditions,
                    effect_summary.effects,
                    self._current_parameters,
                    symbolic_post_state=True,
                )
                if promoted is not None and _expressions_equivalent(promoted, target_post_state):
                    return True
            if expression_matches_stale_post_state_replay(
                current,
                target_post_state,
                conditions,
                effect_summary.effects,
                self._current_parameters,
            ):
                return True
        return False

    def _expression_contains_unresolved_value(self, expr: Optional[Expression]) -> bool:
        if expr is None:
            return True

        expr_type = getattr(expr, "expr_type", None)
        if expr_type is None:
            return True

        if expr_type == ExpressionType.UNKNOWN:
            return True

        if expr_type == ExpressionType.PHI and expr.value:
            for cond, value in expr.value:
                cond_expr = getattr(cond, "expression", None) if cond is not None else None
                if cond_expr is not None and self._expression_contains_unresolved_value(cond_expr):
                    return True
                if self._expression_contains_unresolved_value(value):
                    return True
            return False

        for operand in getattr(expr, "operands", []) or []:
            if self._expression_contains_unresolved_value(operand):
                return True

        return False

    def _count_memory_reads(self, expr: Optional[Expression]) -> int:
        if expr is None:
            return 0
        count = 1 if expr.expr_type == ExpressionType.MEMORY else 0
        if expr.expr_type == ExpressionType.PHI and expr.value:
            return count + sum(self._count_memory_reads(value) for _cond, value in expr.value)
        for operand in getattr(expr, "operands", []) or []:
            count += self._count_memory_reads(operand)
        return count

    def _contains_multiequal(self, varnode, depth: int = 0) -> bool:
        """Return値のチェーン内にMULTIEQUALが含まれるかチェック"""
        if depth > 15:
            return False
        
        if varnode is None:
            return False
        
        def_op = varnode.getDef()
        if def_op is None:
            return False
        
        mnemonic = def_op.getMnemonic()
        
        if mnemonic == "MULTIEQUAL":
            return True
        
        for i in range(def_op.getNumInputs()):
            input_vn = def_op.getInput(i)
            if self._contains_multiequal(input_vn, depth + 1):
                return True
        
        return False
    
    def analyze_function_by_name(self, function_name: str, timeout: int = 60) -> Optional[FunctionReturnAnalysis]:
        self._last_function_lookup_error = None
        function = self._find_function_by_name(function_name)
        if function is None:
            self._last_function_lookup_error = f"Function '{function_name}' not found"
            self._debug_print(self._last_function_lookup_error)
            return None
        return self.analyze_function(function, timeout)

    def refresh_structural_recurrence_summary(
        self,
        analysis: Optional[FunctionReturnAnalysis],
        timeout: int = 60,
    ) -> Optional[FunctionReturnAnalysis]:
        """既存解析ビューに対して structural recurrence summary を再構築する。"""
        if analysis is None or not analysis.returns:
            return analysis

        function = self._find_function_by_name(analysis.function_name)
        if function is None:
            return analysis

        decompiler = self._get_decompiler()
        results = decompiler.decompileFunction(function, timeout, None)
        if not results.decompileCompleted():
            self._debug_print(
                f"Structural summary refresh decompilation failed for '{analysis.function_name}'"
            )
            return analysis

        high_function = results.getHighFunction()
        if high_function is None:
            self._debug_print(
                f"Structural summary refresh HighFunction is None for '{analysis.function_name}'"
            )
            return analysis

        tracer = self._make_tracer(high_function)
        summary = self._apply_structural_recurrence_summary(
            function,
            high_function,
            analysis,
            tracer,
        )
        if summary is None:
            return analysis

        analysis.returns = summary[0]
        if summary[1] not in analysis.analysis_notes:
            analysis.analysis_notes.append(summary[1])
        self._normalize_return_partition(analysis)
        self._mark_incomplete_control_flow(analysis)
        return analysis

    def get_last_function_lookup_error(self) -> Optional[str]:
        return self._last_function_lookup_error

    def _concretize_readonly_loads(
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
                self._read_memory_value,
                image_base=self.program.getImageBase().getOffset(),
                debug=self.debug,
            )
        except Exception as exc:
            self._debug_print(f"Readonly load concretization failed: {exc}")
            return value

    def _read_memory_value(self, address_value: int, size_bytes: int) -> Optional[int]:
        """Read an unsigned integer from program memory."""
        if address_value < 0 or size_bytes <= 0:
            return None

        try:
            memory = self.program.getMemory()
            default_space = self.program.getAddressFactory().getDefaultAddressSpace()
            addr = default_space.getAddress(address_value)
            if addr is None:
                return None

            raw_bytes = []
            for offset in range(size_bytes):
                byte_val = memory.getByte(addr.add(offset))
                raw_bytes.append(int(byte_val) & 0xFF)

            is_big_endian = self.program.getLanguage().isBigEndian()
            ordered = raw_bytes if is_big_endian else list(reversed(raw_bytes))

            result = 0
            for byte_val in ordered:
                result = (result << 8) | byte_val
            return result
        except Exception:
            return None
    
    def _find_function_by_name(self, function_name: str):
        if not function_name:
            return None
        function_manager = self._get_function_manager()
        if function_manager is None:
            return None
        try:
            for func in function_manager.getFunctions(True):
                if func.getName() == function_name:
                    return func
        except Exception:
            return None
        return None

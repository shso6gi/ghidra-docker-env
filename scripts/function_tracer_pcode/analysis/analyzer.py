# -*- coding: utf-8 -*-
"""Return解析メインモジュール（符号性検出統合版）"""

import re
from dataclasses import dataclass
from contextlib import contextmanager
from typing import Iterable, List, Dict, Optional, Any, Set, Tuple, cast

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
from ..model.runtime_refs import UnknownValueRef
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
from .debug import summarize_expression
from .signedness import SignednessDetector
from .effect_summary import (
    EffectSummary,
    _build_parameter_replacements,
    _enumerate_constant_expression_branches,
    _expressions_equivalent,
    _expressions_equivalent_under_conditions,
    _resolve_call_target_ref,
    _reduce_expression_under_conditions,
    expression_contains_post_state_reads,
    expression_contains_synthetic_location_reads,
    lower_post_state_expression_for_smt,
    materialize_definite_post_state_expression,
    normalize_post_state_expression,
    resolve_call_targets,
    rewrite_loads_from_effects,
    rewrite_observed_loads_from_effects,
    summarize_store_effects,
    substitute_condition,
    substitute_expression,
)
from .memory_resolver import concretize_readonly_loads
from .recurrence_summary import StructuralRecurrenceSummarizer


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


@dataclass
class _TrackedReturnValue:
    """RETURN provenance の逆追跡対象。"""

    varnode: Optional[Any] = None
    storage: Optional[StorageInfo] = None
    producer_op: Optional[Any] = None


class ReturnAnalyzer:
    """関数のReturn値を解析"""

    def __init__(self, program, debug: bool = False):
        self.program = program
        self.debug = debug
        self._decompiler = None
        self._current_parameters: List[Dict] = []
        self._current_effect_summary: Optional[EffectSummary] = None
        self._effect_summary_cache: Dict[str, Any] = {}
        self._effect_summary_parameter_cache: Dict[str, List[Dict]] = {}
        self._call_analysis_cache: Dict[str, Optional[FunctionReturnAnalysis]] = {}
        self._local_target_cache: Dict[int, Optional[List[Any]]] = {}
        self._current_deferred_calls: Dict[str, DeferredCallInfo] = {}
        self._deferred_call_counter: int = 0
        self._analysis_in_progress: Dict[str, FunctionReturnAnalysis] = {}
        self._bounded_call_refinement_enabled = bool(BOUNDED_CALL_REFINEMENT_ENABLED)
        self._bounded_call_unroll_limit = int(BOUNDED_CALL_UNROLL_LIMIT)
        self._bounded_call_max_cases = int(BOUNDED_CALL_MAX_CASES)
        self._last_function_lookup_error: Optional[str] = None
        self._current_function_prototype = None
    
    def _debug_print(self, msg: str, indent: int = 0):
        if self.debug:
            prefix = "  " * indent
            print(f"{prefix}[ReturnAnalyzer] {msg}")

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
        active_functions: Optional[Set[str]] = None,
    ) -> Optional[FunctionReturnAnalysis]:
         # デバッグフラグを ConditionSimplifier に伝播
        from .condition import ConditionSimplifier
        ConditionSimplifier.DEBUG = self.debug
        ConditionSimplifier.reset_debug_state()
        
        active_functions = set(active_functions or set())
        current_active_key = self._target_active_key(CallTargetRef.from_function(function))
        if current_active_key is not None:
            active_functions.add(current_active_key)
        active_functions.add(function.getName())

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
        
        # Step 1: tracer作成
        tracer = PcodeTracer(self.program, high_function, debug=self.debug)

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
            # Step 2: condition_tracker作成（まだビルドしない）
            condition_tracker = ConditionTracker(tracer)

            # Step 3: phi_handler作成 → tracerに注入
            from .phi_resolver import PhiHandler
            phi_handler = PhiHandler(tracer, condition_tracker)
            tracer.phi_handler = phi_handler

            # Step 4: ブロック情報構築（phi_handler準備後）
            condition_tracker.build()

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
            effect_summary = self._build_effect_summary(
                function,
                high_function,
                tracer,
                condition_tracker,
                parameters,
                active_functions=(
                    {function.getName()}
                    | (
                        {self._target_active_key(CallTargetRef.from_function(function))}
                        if self._target_active_key(CallTargetRef.from_function(function)) is not None
                        else set()
                    )
                ),
            )
            self._current_effect_summary = effect_summary

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

            return_infos = []
            return_ops = tracer.find_return_ops()

            self._debug_print(f"Found {len(return_ops)} RETURN operations")

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
                return_type=return_type,
                return_type_obj=return_type_obj,
                signedness_result=signedness_result,
                deferred_calls=dict(self._current_deferred_calls),
                effect_summary=effect_summary,
            )
            result.unknown_event_count = len(tracer.unknown_tracker.events)
            result.unknown_event_reasons = sorted(
                {
                    getattr(event, "reason_str", None) or getattr(event.reason, "value", "unknown")
                    for event in tracer.unknown_tracker.events
                }
            )

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

            summary = self._apply_structural_recurrence_summary(
                function,
                high_function,
                result,
                tracer,
            )
            if summary is not None:
                result.returns = summary[0]
                result.analysis_notes.append(summary[1])

            self._analysis_in_progress[function.getName()] = result
            try:
                self._apply_bounded_call_refinement(
                    result,
                    active_functions,
                    function.getName(),
                )
            finally:
                self._analysis_in_progress.pop(function.getName(), None)

            self._synchronize_parameters_with_referenced_parameter_expressions(result)
            result.returns = self._strip_stack_protector_only_conditions(result.returns)
            result.returns = self._merge_equivalent_return_infos(result.returns)
            if (
                result.has_symbolic_post_state_reads()
                and "symbolic_post_state_reads" not in result.analysis_notes
            ):
                result.analysis_notes.append("symbolic_post_state_reads")
            self._mark_incomplete_control_flow(result)

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

        should_try = analysis.has_unresolved_return_value() or any(
            reason in {"call_out_of_scope", "max_depth_exceeded", "phi_no_valid_branch", "phi_circular"}
            for reason in getattr(analysis, "unknown_event_reasons", [])
        )
        if not should_try and getattr(analysis, "effect_summary", None) is not None:
            should_try = bool(
                getattr(analysis.effect_summary, "effects", None)
                and len(getattr(analysis, "returns", []) or []) >= 2
            )
        if not should_try:
            return None

        summarizer = StructuralRecurrenceSummarizer(tracer, debug=self.debug)
        return summarizer.try_summarize_function(function, high_function, analysis)

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
            ConditionNormalizer.expression_signature(base_expr),
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

    def _make_deferred_call_recorder(self, target_function_name: str):
        def record_call(target, args: List[Expression]) -> UnknownValueRef:
            target_ref = self._coerce_runtime_target_ref(target) or CallTargetRef.unknown()
            target_label = target_ref.placeholder_name()
            sequence = self._deferred_call_counter
            placeholder_name = f"call_out_of_scope:{target_label}#{sequence}"
            self._deferred_call_counter += 1
            cloned_args = [self._clone_expression(arg) for arg in args]
            info = DeferredCallInfo(
                placeholder_name=placeholder_name,
                target_ref=target_ref,
                arguments=cloned_args,
                sequence=sequence,
            )
            self._current_deferred_calls[placeholder_name] = info
            if self.debug:
                arg_dump = ", ".join(arg.to_string() for arg in cloned_args)
                self._debug_print(
                    f"Recorded deferred call in '{target_function_name}': "
                    f"{placeholder_name} -> {target_ref.display_name()}([{arg_dump}])"
                )
            return info.unknown_ref

        return record_call

    def _apply_bounded_call_refinement(
        self,
        analysis: FunctionReturnAnalysis,
        active_functions: Set[str],
        current_function_name: str,
    ) -> None:
        if (
            not self._bounded_call_refinement_enabled
            or analysis is None
            or not analysis.deferred_calls
            or self._bounded_call_unroll_limit <= 0
        ):
            return

        def provide_analysis(target) -> Optional[FunctionReturnAnalysis]:
            target_ref = self._coerce_runtime_target_ref(target)
            if target_ref is None:
                return None
            if target_ref.function_name == current_function_name:
                return analysis
            in_progress = self._analysis_in_progress.get(target_ref.function_name or "")
            if in_progress is not None:
                return in_progress
            active_key = self._target_active_key(target_ref)
            if active_key is not None and active_key in active_functions:
                return None
            return self._get_or_analyze_call_target(target_ref, active_functions)

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

    def _recover_call_wrapper_returns(
        self,
        decompile_results,
        analysis: FunctionReturnAnalysis,
        current_function,
        tracer: PcodeTracer,
        condition_tracker: ConditionTracker,
        return_ops: List[Any],
        active_functions: Optional[Set[str]] = None,
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
        active_functions: Set[str],
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
        active_functions: Optional[Set[str]] = None,
    ) -> Optional[List[ReturnInfo]]:
        from ..transform.expander import ExpandedValue

        if not self._should_attempt_switch_recovery(analysis):
            return None

        block_by_index = getattr(condition_tracker, "block_by_index", None) or {}
        switch_blocks = [
            block_info
            for block_info in block_by_index.values()
            if self._find_branchind_op_on_block(block_info) is not None
        ]
        if not switch_blocks:
            return None

        for switch_block in sorted(switch_blocks, key=lambda info: info.index):
            branchind_op = self._find_branchind_op_on_block(switch_block)
            if branchind_op is None:
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
                branchind_op,
                tracer,
                condition_tracker,
            )
            if not candidate_entries or len(candidate_entries) < 2:
                continue

            expanded_values: List[ExpandedValue] = []
            candidate_failed = False
            for address_value, branch_conditions in candidate_entries:
                resolved = self._resolve_local_code_target_expansions(
                    address_value,
                    active_functions or set(),
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
                branchind_op,
                analysis.entry_point,
                identity_prefix="branchind",
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
                    "Recovered switch-like return cases from BRANCHIND/CFG structure "
                    f"(affected_sites={sorted(impacted_site_keys)}, recovered={len(recovered)})"
                )
            return combined

        return None

    def _find_branchind_op_on_block(self, block_info) -> Optional[Any]:
        if block_info is None:
            return None
        for pcode_op in reversed(list(getattr(block_info, "pcode_ops", []) or [])):
            try:
                if pcode_op.getMnemonic() == "BRANCHIND":
                    return pcode_op
            except Exception:
                continue
        return None

    def _enumerate_switch_branch_targets(
        self,
        switch_block,
        branchind_op,
        tracer: PcodeTracer,
        condition_tracker: ConditionTracker,
    ) -> List[Tuple[int, List[Condition]]]:
        if branchind_op is None or branchind_op.getNumInputs() < 1:
            return []

        base_paths = condition_tracker.get_all_valid_block_paths_to_block(switch_block)
        if not base_paths:
            base_paths = [([switch_block], [])]

        resolved_targets: List[Tuple[int, List[Condition]]] = []
        seen = set()
        for _blocks, base_conditions in base_paths:
            try:
                target_varnode = branchind_op.getInput(0)
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
                        f"Switch recovery skipped on block {switch_block.index}: BRANCHIND target was not finitely enumerable"
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
            return_type=analysis.return_type,
            return_type_obj=analysis.return_type_obj,
            unknown_event_count=analysis.unknown_event_count,
            unknown_event_reasons=list(analysis.unknown_event_reasons),
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
            return_type=analysis.return_type,
            return_type_obj=analysis.return_type_obj,
            unknown_event_count=analysis.unknown_event_count,
            unknown_event_reasons=list(analysis.unknown_event_reasons),
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
        caller = caller_storage or {}
        callee = callee_storage or {}
        if not caller.get("is_register") or not callee.get("is_register"):
            return False

        caller_base = (caller.get("base_register_name") or caller.get("register_name") or "").lower()
        callee_base = (callee.get("base_register_name") or callee.get("register_name") or "").lower()
        if not caller_base or caller_base != callee_base:
            return False

        caller_offset = int(caller.get("bit_offset_in_base", 0))
        callee_offset = int(callee.get("bit_offset_in_base", 0))
        if caller_offset != callee_offset:
            return False

        caller_bits = int(caller.get("size_bits") or (caller.get("size", 0) * 8))
        callee_bits = int(callee.get("size_bits") or (callee.get("size", 0) * 8))
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
                    offset=int(storage.get("offset", 0)),
                    size=int(storage.get("size", 0)),
                    size_bits=int(storage.get("size_bits", 0)),
                    register_name=storage.get("register_name"),
                    base_register_name=storage.get("base_register_name"),
                    base_register_offset=int(storage.get("base_register_offset", 0)),
                    base_register_size=int(storage.get("base_register_size", 0)),
                    base_register_size_bits=int(storage.get("base_register_size_bits", 0)),
                    bit_offset_in_base=int(storage.get("bit_offset_in_base", 0)),
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

    def _function_cache_key(self, function) -> Optional[str]:
        if function is None:
            return None
        try:
            return str(function.getEntryPoint())
        except Exception:
            return None

    def _target_active_key(self, target_ref: Optional[CallTargetRef]) -> Optional[str]:
        if target_ref is None:
            return None
        if target_ref.entry_offset is not None:
            return f"entry@0x{target_ref.entry_offset:x}"
        if target_ref.function_name:
            return f"name:{target_ref.function_name}"
        if target_ref.address_offset is not None:
            return f"code@0x{target_ref.address_offset:x}"
        return None

    def _resolve_target_function(self, target) -> Optional[Any]:
        target_ref = self._coerce_runtime_target_ref(target)
        if target_ref is None or self.program is None:
            return None
        if target_ref.function_obj is not None:
            return target_ref.function_obj
        if target_ref.entry_offset is not None:
            return self._find_function_by_entry_offset(target_ref.entry_offset)
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
        active_functions: Set[str],
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
            if target_ref.display_name() == "UNKNOWN_FUNC":
                continue
            if active_key is not None and active_key in active_functions:
                continue
            if target_ref.function_name and target_ref.function_name in active_functions:
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

    def _build_effect_summary(
        self,
        function,
        high_function,
        tracer: PcodeTracer,
        condition_tracker: ConditionTracker,
        parameters: List[Dict],
        active_functions: set,
    ):
        cache_key = str(function.getEntryPoint())
        self._effect_summary_parameter_cache[cache_key] = list(parameters)
        cached = self._effect_summary_cache.get(cache_key)
        if cached is not None:
            return cached

        def summarize_call(target, args):
            target_ref = self._coerce_runtime_target_ref(target)
            if target_ref is None:
                return None
            active_key = self._target_active_key(target_ref)
            if active_key is not None and active_key in active_functions:
                return None
            if target_ref.function_name and target_ref.function_name in active_functions:
                return None
            callee = self._resolve_target_function(target_ref)
            if callee is None:
                return None
            callee_key = self._function_cache_key(callee)
            if callee_key is None:
                return None
            cached_callee = self._effect_summary_cache.get(callee_key)
            if cached_callee is not None:
                return cached_callee

            decompiler = self._get_decompiler()
            results = decompiler.decompileFunction(callee, 60, None)
            if not results.decompileCompleted():
                return None
            callee_high = results.getHighFunction()
            if callee_high is None:
                return None

            callee_tracer = PcodeTracer(self.program, callee_high, debug=self.debug)
            callee_tracker = ConditionTracker(callee_tracer)
            from .phi_resolver import PhiHandler

            callee_phi_handler = PhiHandler(callee_tracer, callee_tracker)
            callee_tracer.phi_handler = callee_phi_handler
            callee_tracker.build()
            callee_parameters = self._collect_parameters(callee_high)
            self._effect_summary_parameter_cache[callee_key] = list(callee_parameters)
            image_base = None
            try:
                image_base = self.program.getImageBase().getOffset()
            except Exception:
                image_base = None
            callee_tracker.refine_branch_conditions(
                call_resolver=self._make_call_resolver(
                    active_functions | ({active_key} if active_key is not None else set()),
                    callee,
                ),
                parameters=callee_parameters,
                resolve_callee_parameters=self._get_freshest_callee_parameters,
                read_memory_value=self._read_memory_value,
                image_base=image_base,
            )
            summary = self._build_effect_summary(
                callee,
                callee_high,
                callee_tracer,
                callee_tracker,
                callee_parameters,
                active_functions | ({active_key} if active_key is not None else set()),
            )
            return summary

        def resolve_callee_parameters(target):
            return self._get_freshest_callee_parameters(target)

        current_target = CallTargetRef.from_function(function)
        current_active_key = self._target_active_key(current_target)
        summary = summarize_store_effects(
            condition_tracker.block_by_index.values(),
            tracer,
            condition_tracker,
            parameters,
            direct_call_summary=summarize_call,
            direct_call_expander=self._make_call_resolver(
                active_functions | ({current_active_key} if current_active_key is not None else set()),
                function,
            ),
            resolve_callee_parameters=resolve_callee_parameters,
            debug=self.debug,
        )
        self._effect_summary_cache[cache_key] = summary
        return summary

    def _make_call_resolver(self, active_functions: Set[str], current_function=None):
        def resolve_call(target, args):
            return self._resolve_call_expansions(target, args, active_functions, current_function)

        return resolve_call

    def _resolve_call_expansions(
        self,
        target,
        args: List[Expression],
        active_functions: Set[str],
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
            )

        active_key = self._target_active_key(target_ref)
        if (active_key is not None and active_key in active_functions) or (
            target_ref.function_name and target_ref.function_name in active_functions
        ):
            self._debug_print(f"Skipping recursive call expansion for '{target_label}'")
            return None

        analysis = self._get_or_analyze_call_target(target_ref, active_functions)
        if analysis is None:
            self._debug_print(f"Call expansion skipped for '{target_label}': analysis unavailable")
            return None
        if not self._is_call_return_summary_allowed(analysis, args):
            self._debug_print(
                f"Call expansion skipped for '{target_label}': "
                "summary not safe enough for inlining"
            )
            return None

        if len(args) < len(analysis.parameters):
            self._debug_print(
                f"Call expansion skipped for '{target_label}': "
                f"expected {len(analysis.parameters)} args, got {len(args)}"
            )
            return None

        replacements = _build_parameter_replacements(analysis.parameters, args)
        allowed_names: Set[str] = set()
        for arg in args:
            allowed_names.update(arg.get_all_variables())

        expanded = []
        for ret in analysis.returns:
            value = substitute_expression(ret.value, replacements, analysis.parameters)
            conditions = [
                substitute_condition(cond, replacements, analysis.parameters)
                for cond in ret.conditions
            ]

            if not self._call_summary_is_safe(value, conditions, allowed_names):
                self._debug_print(
                    f"Call expansion rejected for '{target_label}': "
                    "callee summary references unresolved symbols"
                )
                return None

            expanded.append(
                ExpandedValue(
                    value=value,
                    conditions=ConditionSimplifier.simplify_conditions(conditions),
                )
            )

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
        active_functions: Set[str],
        current_function=None,
    ):
        from ..transform.expander import ExpandedValue

        if address_value in self._local_target_cache:
            return self._local_target_cache[address_value]

        try:
            default_space = self.program.getAddressFactory().getDefaultAddressSpace()
            addr = default_space.getAddress(address_value)
        except Exception:
            self._debug_print(f"Local target resolution failed: invalid address 0x{address_value:x}")
            self._local_target_cache[address_value] = None
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
            self._local_target_cache[address_value] = None
            return None

        decompiler = self._get_decompiler()
        results = decompiler.decompileFunction(containing, 60, None)
        if not results.decompileCompleted():
            self._debug_print(
                f"Local target resolution failed: decompilation incomplete for 0x{address_value:x}"
            )
            self._local_target_cache[address_value] = None
            return None
        high_function = results.getHighFunction()
        if high_function is None:
            self._debug_print(f"Local target resolution failed: HighFunction unavailable for 0x{address_value:x}")
            self._local_target_cache[address_value] = None
            return None

        tracer = PcodeTracer(self.program, high_function, debug=self.debug)
        expanded = self._expand_linear_code_target(addr, tracer, containing)
        self._local_target_cache[address_value] = expanded
        return expanded

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
        return (
            ConditionNormalizer.expression_signature(addr_expr),
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
        active_functions: Set[str],
        minimum_param_count: int = 0,
    ) -> Optional[FunctionReturnAnalysis]:
        target_ref = self._coerce_runtime_target_ref(target)
        callee = self._resolve_target_function(target_ref)
        if callee is None:
            return None

        cache_key = self._function_cache_key(callee)
        if cache_key is None:
            return None
        cached = self._call_analysis_cache.get(cache_key)
        if cached is not None and len(getattr(cached, "parameters", []) or []) >= minimum_param_count:
            return cached

        active_key = self._target_active_key(target_ref)
        analysis = self.analyze_function(
            callee,
            timeout=60,
            active_functions=active_functions | ({active_key} if active_key is not None else set()),
        )
        if cached is None:
            self._call_analysis_cache[cache_key] = analysis
            return analysis
        if analysis is None:
            return cached
        if len(getattr(analysis, "parameters", []) or []) >= len(getattr(cached, "parameters", []) or []):
            self._call_analysis_cache[cache_key] = analysis
            return analysis
        return cached

    def _is_call_return_summary_allowed(
        self,
        analysis: FunctionReturnAnalysis,
        args: List[Expression],
    ) -> bool:
        if analysis is None or not analysis.returns:
            return False
        # 一時的な unknown event が残っていても、最終的な return summary が
        # 完全に解決済みなら call 展開には利用できる。ここでは最終 summary の
        # 安全性に直接効くシグナルだけを除外条件に使う。
        if analysis.has_unknown_return() or analysis.has_overlapping_unconditional_returns():
            return False

        param_names = {
            name
            for param in analysis.parameters
            for name in [param.get("name")]
            if isinstance(name, str) and name
        }
        allowed_names: Set[str] = set()
        for arg in args:
            allowed_names.update(arg.get_all_variables())

        for ret in analysis.returns:
            if self._expression_contains_unknown_or_call(ret.value):
                return False
            if not self._expression_uses_only_allowed_names(ret.value, param_names, allowed_names):
                return False
            for cond in ret.conditions:
                if self._expression_contains_unknown_or_call(cond.expression):
                    return False
                if not self._expression_uses_only_allowed_names(cond.expression, param_names, allowed_names):
                    return False

        return True

    def _call_summary_is_safe(
        self,
        value: Expression,
        conditions: List[Condition],
        allowed_names: Set[str],
    ) -> bool:
        if self._expression_contains_unknown_or_call(value):
            return False
        if not self._expression_uses_only_allowed_names(value, set(), allowed_names):
            return False

        for cond in conditions:
            if self._expression_contains_unknown_or_call(cond.expression):
                return False
            if not self._expression_uses_only_allowed_names(cond.expression, set(), allowed_names):
                return False

        return True

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

    def _expression_contains_phi(self, expr: Optional[Expression]) -> bool:
        if expr is None:
            return False
        if expr.expr_type == ExpressionType.PHI:
            return True
        for operand in getattr(expr, "operands", []) or []:
            if self._expression_contains_phi(operand):
                return True
        return False

    def _expression_uses_only_allowed_names(
        self,
        expr: Optional[Expression],
        local_param_names: Set[str],
        allowed_names: Set[str],
    ) -> bool:
        if expr is None:
            return True
        referenced = expr.get_all_variables()
        return referenced.issubset(local_param_names | allowed_names)
    
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
        active_functions: Set[str],
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
        if path_entries:
            path_entries = self._filter_noreturn_return_path_entries(
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
            # void return
            simplified_conds = ConditionSimplifier.simplify_conditions(path_conditions)
            return [self._make_return_info(
                address=address,
                value=Expression.unknown("void"),
                conditions=simplified_conds,
                branch_index=return_index,
                site_metadata=site_metadata,
            )]

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
            return path_entries

        filtered = []
        for block_path, conditions in path_entries:
            if self._block_path_contains_noreturn_call(block_path, tracer, return_op):
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

        return filtered

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
                if self._is_noreturn_call_op(pcode_op, tracer):
                    return True
        return False

    def _is_noreturn_call_op(self, pcode_op, tracer: PcodeTracer) -> bool:
        if pcode_op is None or pcode_op.getMnemonic() not in {"CALL", "CALLIND"}:
            return False

        for target_ref in self._resolve_object_centric_call_targets(pcode_op, tracer):
            target_function = self._resolve_function_from_call_target_ref(target_ref)
            if target_function is not None and self._function_has_no_return(target_function):
                return True
        return False

    def _resolve_object_centric_call_targets(
        self,
        pcode_op,
        tracer: Optional[PcodeTracer],
    ) -> List[CallTargetRef]:
        if pcode_op is None or tracer is None:
            return []

        resolved: List[CallTargetRef] = []

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

    def _resolve_direct_call_target_function(self, pcode_op, tracer: Optional[PcodeTracer] = None):
        if self.program is None or pcode_op is None or pcode_op.getNumInputs() < 1:
            return None
        try:
            target_varnode = pcode_op.getInput(0)
            if target_varnode is None:
                return None
        except Exception:
            return None
        function = self._resolve_function_from_address(target_varnode.getAddress())
        if function is not None:
            return function
        traced_target = self._trace_call_target_expression(target_varnode, tracer)
        if traced_target is None or traced_target.expr_type != ExpressionType.CONSTANT:
            return None
        target_offset = self._constant_int_value(traced_target)
        if target_offset is None or target_offset < 0:
            return None
        return self._resolve_function_from_program_offset(target_offset)

    def _resolve_function_from_address(self, address):
        if self.program is None or address is None:
            return None
        try:
            function_manager = self.program.getFunctionManager()
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

    def _trace_call_target_expression(
        self,
        target_varnode,
        tracer: Optional[PcodeTracer],
    ) -> Optional[Expression]:
        if tracer is None or target_varnode is None:
            return None
        try:
            traced_target = tracer.trace_varnode(target_varnode, use_cache=False)
        except Exception:
            return None
        if isinstance(traced_target, Expression):
            return traced_target
        return None

    def _find_function_by_name(self, resolved_name: str):
        if self.program is None or not resolved_name:
            return None
        try:
            function_manager = self.program.getFunctionManager()
            if function_manager is None:
                return None
            for func in function_manager.getFunctions(True):
                if func.getName() == resolved_name:
                    return func
        except Exception:
            return None
        return None

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
        active_functions: Optional[Set[str]] = None,
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
        active_functions: Optional[Set[str]] = None,
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
        active_functions: Optional[Set[str]] = None,
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
        active_functions: Optional[Set[str]] = None,
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
        best_input = None
        best_score: Optional[Tuple[int, int, int]] = None

        try:
            for index in range(int(get_in_size())):
                incoming = get_in(index)
                score = self._score_multiequal_incoming_for_return_path(
                    incoming,
                    predecessor,
                    condition_tracker,
                    current_condition_keys,
                )
                candidate_input = multiequal_op.getInput(index)
                if candidate_input is None:
                    continue
                if best_score is None or score > best_score:
                    best_score = score
                    best_input = candidate_input
        except Exception:
            return None

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
            return (predecessor_match, 0, 0)

        block_info = condition_tracker.get_block_by_hash(incoming_block)
        if block_info is None:
            return (predecessor_match, 0, 0)

        incoming_conditions = condition_tracker.get_path_conditions_to_block(block_info)
        incoming_keys = self._build_condition_signature_set(incoming_conditions)
        if not incoming_keys:
            return (predecessor_match, 0, 0)

        matched = len(incoming_keys & current_condition_keys)
        specificity = len(incoming_keys)
        return (matched, predecessor_match, specificity)

    def _build_condition_signature_set(self, conditions: List[Condition]) -> Set[object]:
        signatures: Set[object] = set()
        for condition in conditions:
            try:
                signatures.add(ConditionNormalizer.normalize_for_contradiction(condition))
            except Exception:
                try:
                    signatures.add(ConditionNormalizer.expression_signature(condition.expression))
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
        active_functions: Optional[Set[str]] = None,
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
            record_deferred_call=self._make_deferred_call_recorder(
                current_function.getName() if current_function is not None else "<unknown>"
            ),
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
        active_functions: Optional[Set[str]] = None,
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
                record_deferred_call=self._make_deferred_call_recorder(
                    current_function.getName() if current_function is not None else "<unknown>"
                ),
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
                        f"Expanding PHI return with path[{path_idx}]: {cond_strs}"
                    )
                expanded_values.extend(
                    expander.expand_from_varnode(return_varnode, conds)
                )
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
                record_deferred_call=self._make_deferred_call_recorder(
                    current_function.getName() if current_function is not None else "<unknown>"
                ),
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
            simplified_conds = ConditionSimplifier.simplify_conditions(path_conditions)
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

            simplified_conds = ConditionSimplifier.simplify_conditions(ev.conditions)
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
                normalized_value = self._normalize_expanded_return_value(
                    split_value,
                    split_conditions,
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
        rewritten_observed = None
        if self._expression_contains_observed_loads(value):
            rewritten_observed = rewrite_observed_loads_from_effects(
                value,
                conditions,
                effect_summary.effects,
                self._current_parameters,
            )
            if self._accept_effect_sensitive_rewrite(
                value,
                rewritten_observed,
                rewrite_kind="observed-load",
            ):
                return rewritten_observed

        rewritten_generic = rewrite_loads_from_effects(
            value,
            conditions,
            effect_summary.effects,
            self._current_parameters,
        )
        if self._accept_effect_sensitive_rewrite(
            value,
            rewritten_generic,
            rewrite_kind="generic effect-sensitive",
        ):
            return rewritten_generic

        return value

    def _accept_effect_sensitive_rewrite(
        self,
        original: Optional[Expression],
        rewritten: Optional[Expression],
        *,
        rewrite_kind: str,
    ) -> bool:
        if rewritten is None or original is None:
            return False
        if _expressions_equivalent(rewritten, original):
            return False

        original_rank = self._effect_sensitive_rewrite_rank(original)
        rewritten_rank = self._effect_sensitive_rewrite_rank(rewritten)
        accepted = rewritten_rank > original_rank

        if self.debug and not accepted:
            self._debug_print(
                f"Rejected {rewrite_kind} rewrite without object-centric precision gain: "
                f"{self._debug_expr_identity_summary(original)} -> "
                f"{self._debug_expr_identity_summary(rewritten)} "
                f"rank {original_rank} -> {rewritten_rank}"
            )

        return accepted

    def _effect_sensitive_rewrite_rank(
        self,
        expr: Optional[Expression],
    ) -> Tuple[int, int, int, int, int]:
        if expr is None:
            return (0, 0, 0, 0, 0)
        return (
            1 if expression_contains_synthetic_location_reads(expr) else 0,
            1 if expression_contains_post_state_reads(expr) else 0,
            1 if self._expression_contains_phi(expr) else 0,
            1 if self._expression_contains_observed_loads(expr) else 0,
            self._count_memory_reads(expr),
        )

    def _expand_object_centric_expression_cases(
        self,
        expr: Optional[Expression],
        base_conditions: List[Condition],
    ) -> List[Tuple[Expression, List[Condition]]]:
        if expr is None:
            return []

        simplified_base = ConditionSimplifier.simplify_conditions(base_conditions)
        if ConditionSimplifier.is_contradiction(simplified_base):
            return []

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
                nested_conditions = ConditionSimplifier.simplify_conditions(combined_conditions)
                if ConditionSimplifier.is_contradiction(nested_conditions):
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
                if not ConditionSimplifier.is_contradiction(case_conditions)
            ]
            return self._deduplicate_expression_cases(expanded)

        if expr.expr_type == ExpressionType.UNARY_OP and expr.operands:
            operand_cases = self._expand_object_centric_expression_cases(
                expr.operands[0],
                simplified_base,
            )
            if not operand_cases:
                return [(expr, simplified_base)]
            expanded = [
                (expr.clone_with(operands=[operand]), case_conditions)
                for operand, case_conditions in operand_cases
                if not ConditionSimplifier.is_contradiction(case_conditions)
            ]
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
                    combined_conditions = ConditionSimplifier.simplify_conditions(
                        list(left_conditions) + list(right_conditions)
                    )
                    if ConditionSimplifier.is_contradiction(combined_conditions):
                        continue
                    expanded.append(
                        (
                            expr.clone_with(operands=[left_value, right_value]),
                            combined_conditions,
                        )
                    )
            return self._deduplicate_expression_cases(expanded)

        return [(expr, simplified_base)]

    def _deduplicate_expression_cases(
        self,
        cases: List[Tuple[Expression, List[Condition]]],
    ) -> List[Tuple[Expression, List[Condition]]]:
        deduplicated: List[Tuple[Expression, List[Condition]]] = []
        for value, conditions in cases:
            simplified_conditions = ConditionSimplifier.simplify_conditions(conditions)
            if ConditionSimplifier.is_contradiction(simplified_conditions):
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

        if len(left_residual) == 1 and len(right_residual) == 1:
            if ConditionSimplifier.are_contradictory_conditions(left_residual[0], right_residual[0]):
                if not self._can_safely_collapse_complementary_return_pair(
                    left,
                    right,
                    shared_conditions,
                    all_infos or [],
                    left_index,
                    right_index,
                ):
                    return None
                return self._make_merged_return_info(
                    left,
                    right,
                    shared_conditions,
                    "collapsed complementary same-valued return cases",
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
        if not all_infos:
            return True

        merged_scope = ConditionSimplifier.simplify_conditions(list(merged_conditions))
        for index, other in enumerate(all_infos):
            if index == left_index or index == right_index:
                continue
            if self._return_site_key(other) != self._return_site_key(left):
                continue
            if _expressions_equivalent(other.value, left.value):
                continue

            overlap_conditions = ConditionSimplifier.simplify_conditions(
                list(merged_scope) + list(other.conditions)
            )
            if ConditionSimplifier.is_contradiction(overlap_conditions):
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
                if ConditionSimplifier.are_equivalent_conditions(left_cond, right_cond):
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
            ConditionSimplifier.simplify_conditions(shared),
            ConditionSimplifier.simplify_conditions(left_residual),
            ConditionSimplifier.simplify_conditions(right_residual),
        )

    def _make_merged_return_info(
        self,
        primary: ReturnInfo,
        secondary: ReturnInfo,
        merged_conditions: List[Condition],
        reason: str,
    ) -> ReturnInfo:
        normalized_conditions = ConditionSimplifier.simplify_conditions(list(merged_conditions))
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
        canonicalized = normalize_post_state_expression(
            value,
            conditions,
            effect_summary.effects,
            self._current_parameters,
            prefer_canonical_post_state=True,
            symbolic_post_state=True,
        )
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
            if value.expr_type == ExpressionType.MEMORY:
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
        if not expression_contains_synthetic_location_reads(canonicalized):
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
        if self._expression_contains_observed_loads(original):
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
        return True

    def _expression_contains_observed_loads(self, expr: Optional[Expression]) -> bool:
        if expr is None:
            return False
        runtime_ref = getattr(expr, "runtime_ref", None)
        observed_order_key = getattr(runtime_ref, "order_key", None)
        if expr.expr_type == ExpressionType.MEMORY and (
            getattr(expr, "read_order_key", None) is not None
            or observed_order_key is not None
        ):
            return True
        if expr.expr_type == ExpressionType.PHI and expr.value:
            for cond, value in expr.value:
                cond_expr = getattr(cond, "expression", None) if cond is not None else None
                if cond_expr is not None and self._expression_contains_observed_loads(cond_expr):
                    return True
                if self._expression_contains_observed_loads(value):
                    return True
            return False
        return any(
            self._expression_contains_observed_loads(operand)
            for operand in getattr(expr, "operands", []) or []
        )

    def _expression_contains_unresolved_value(self, expr: Optional[Expression]) -> bool:
        if expr is None:
            return True

        expr_type = getattr(expr, "expr_type", None)
        if expr_type is None:
            return True

        if expr_type in {ExpressionType.UNKNOWN, ExpressionType.CALL}:
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
        function_manager = self.program.getFunctionManager()
        for func in function_manager.getFunctions(True):
            if func.getName() == function_name:
                return func
        return None

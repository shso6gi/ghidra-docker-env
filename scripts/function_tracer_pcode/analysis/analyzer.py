# -*- coding: utf-8 -*-
"""Return解析メインモジュール（符号性検出統合版）"""

import re
from dataclasses import dataclass, replace
from contextlib import contextmanager
from functools import cmp_to_key
from typing import Iterable, List, Dict, Optional, Any, Set, Tuple, Sequence, Mapping, cast

from ..model.expression import Expression, ExpressionType, Condition
from ..model.call_target import CallTargetRef, coerce_call_target_ref
from ..model.structural import StructuralKey, expression_key_safe
from ..model.storage import StorageInfo
from ..model.analysis import (
    ComparisonSurface,
    DeferredCallInfo,
    DivergenceOutcome,
    ReturnInfo,
    ReturnOutcome,
    UnknownOutcome,
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
from ..model.render_smt import expression_contains_unsupported_smt_ops
from ..model.intrinsics import resolve_pcode_intrinsic
from ..config.settings import (
    BOUNDED_CALL_MAX_CASES,
    BOUNDED_CALL_REFINEMENT_ENABLED,
    BOUNDED_CALL_UNROLL_LIMIT,
)
from . import PcodeTracer
from .bounded_refinement import BoundedCallRefiner
from .condition import ConditionTracker, ConditionSimplifier, ConditionNormalizer
from .condition.bitvector import eval_constant_raw
from .condition.smt_oracle import ConditionSMTOracle
from .debug import summarize_expression
from .failure import (
    ANALYSIS_STATUS_ANALYSIS_EXCEPTION,
    ANALYSIS_STATUS_DECOMPILATION_FAILED,
    ANALYSIS_STATUS_FUNCTION_LOOKUP_MISS,
    ANALYSIS_STATUS_HIGH_FUNCTION_MISSING,
    AnalysisFailure,
)
from .signedness import SignednessDetector
from .summary_returns import (
    accept_summary_return_candidates,
    attach_summary_return_acceptance_proof,
)
from .effect_summary import (
    CanonicalLocation,
    EffectSummary,
    CallArgumentEvidence,
    _build_parameter_replacements,
    _call_argument_evidence_storage_key,
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

    def __init__(
        self,
        program,
        debug: bool = False,
        binary_id: Optional[str] = None,
        *,
        enable_completed_recovery_proofs: bool = True,
    ):
        self.program = program
        self.debug = debug
        self._binary_id = binary_id
        self.enable_completed_recovery_proofs = bool(enable_completed_recovery_proofs)
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
        self._last_analysis_failure: Optional[AnalysisFailure] = None
        self._current_function_prototype = None
        self._current_function_entry_address_value = None
    
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

    def _program_identity(self) -> Optional[int]:
        try:
            getter = getattr(self.program, "getUniqueProgramID", None)
            if callable(getter):
                return int(getter())
        except Exception:
            return None
        return None

    def _current_function_entry_address(self):
        if self._current_function_entry_address_value is not None:
            return self._current_function_entry_address_value
        prototype = self._current_function_prototype
        for getter_name in ("getFunction", "getFunctionDefinition"):
            getter = getattr(prototype, getter_name, None)
            if not callable(getter):
                continue
            try:
                function = getter()
            except Exception:
                function = None
            entry_getter = getattr(function, "getEntryPoint", None)
            if callable(entry_getter):
                try:
                    return entry_getter()
                except Exception:
                    return None
        return None

    @staticmethod
    def _function_entry_address(function):
        entry_getter = getattr(function, "getEntryPoint", None)
        if not callable(entry_getter):
            return None
        try:
            return entry_getter()
        except Exception:
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
            "pcode_op_ref": PcodeOpRef.from_pcode_op(
                pcode_op,
                binary_id=self._binary_id,
                program_uid=self._program_identity(),
                function_entry=self._current_function_entry_address(),
            ),
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

    @staticmethod
    def _return_site_metadata_from_info(info: ReturnInfo) -> Dict[str, Optional[object]]:
        return {
            "pcode_identity": info.pcode_identity,
            "pcode_order": info.pcode_order,
            "pcode_time": info.pcode_time,
            "pcode_op_ref": info.pcode_op_ref,
            "return_value_pcode_op_refs": tuple(
                getattr(info, "return_value_pcode_op_refs", ()) or ()
            ),
        }

    def _return_value_pcode_op_refs_from_varnode(
        self,
        varnode,
    ) -> Tuple[PcodeOpRef, ...]:
        refs: List[PcodeOpRef] = []
        seen: Set[Tuple[Any, ...]] = set()
        for pcode_op in self._return_value_producer_chain(varnode):
            ref = PcodeOpRef.from_pcode_op(
                pcode_op,
                binary_id=self._binary_id,
                program_uid=self._program_identity(),
                function_entry=self._current_function_entry_address(),
            )
            if ref is None:
                continue
            key = ref.stable_key()
            if key in seen:
                continue
            seen.add(key)
            refs.append(ref)
        return tuple(refs)

    @staticmethod
    def _return_value_producer_chain(varnode, *, max_depth: int = 4) -> Tuple[Any, ...]:
        """Collect the direct return producer plus transparent single-input producers."""
        if varnode is None:
            return ()
        refs: List[Any] = []
        current = varnode
        seen_varnodes: Set[int] = set()
        transparent_single_input_ops = {
            "COPY",
            "CAST",
            "INT_SEXT",
            "INT_ZEXT",
            "SUBPIECE",
        }
        for _depth in range(max(1, int(max_depth))):
            marker = id(current)
            if marker in seen_varnodes:
                break
            seen_varnodes.add(marker)
            get_def = getattr(current, "getDef", None)
            pcode_op = get_def() if callable(get_def) else None
            if pcode_op is None:
                break
            refs.append(pcode_op)
            try:
                mnemonic = str(pcode_op.getMnemonic() or "")
            except Exception:
                break
            if mnemonic not in transparent_single_input_ops:
                break
            try:
                input_count = int(pcode_op.getNumInputs())
            except Exception:
                break
            if input_count != 1:
                break
            try:
                current = pcode_op.getInput(0)
            except Exception:
                break
        return tuple(refs)

    def _site_metadata_with_return_value_pcode_op_refs(
        self,
        site_metadata: Optional[Dict[str, Optional[object]]],
        *,
        return_varnode=None,
        producer_op=None,
    ) -> Dict[str, Optional[object]]:
        metadata: Dict[str, Optional[object]] = dict(site_metadata or {})
        refs: List[PcodeOpRef] = [
            ref
            for ref in (metadata.get("return_value_pcode_op_refs") or ())
            if isinstance(ref, PcodeOpRef)
        ]
        if producer_op is not None:
            producer_ref = PcodeOpRef.from_pcode_op(
                producer_op,
                binary_id=self._binary_id,
                program_uid=self._program_identity(),
                function_entry=self._current_function_entry_address(),
            )
            if producer_ref is not None:
                refs.append(producer_ref)
        refs.extend(self._return_value_pcode_op_refs_from_varnode(return_varnode))
        deduped: List[PcodeOpRef] = []
        seen: Set[Tuple[Any, ...]] = set()
        for ref in refs:
            key = ref.stable_key()
            if key in seen:
                continue
            seen.add(key)
            deduped.append(ref)
        metadata["return_value_pcode_op_refs"] = tuple(deduped)
        return metadata

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
            pcode_op_ref=cast(Optional[PcodeOpRef], site_metadata.get("pcode_op_ref")),
            return_value_pcode_op_refs=tuple(
                ref
                for ref in (site_metadata.get("return_value_pcode_op_refs") or ())
                if isinstance(ref, PcodeOpRef)
            ),
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
        function_entry_address=None,
    ):
        """Temporarily bind per-analysis state and restore the parent context on exit."""
        previous_parameters = self._current_parameters
        previous_effect_summary = self._current_effect_summary
        previous_deferred_calls = self._current_deferred_calls
        previous_function_prototype = self._current_function_prototype
        previous_function_entry_address = self._current_function_entry_address_value
        self._current_parameters = parameters
        self._current_effect_summary = effect_summary
        self._current_deferred_calls = {}
        self._current_function_prototype = function_prototype
        self._current_function_entry_address_value = function_entry_address
        try:
            yield
        finally:
            self._current_parameters = previous_parameters
            self._current_effect_summary = previous_effect_summary
            self._current_deferred_calls = previous_deferred_calls
            self._current_function_prototype = previous_function_prototype
            self._current_function_entry_address_value = previous_function_entry_address
    
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
            if getattr(ret_info, "return_kind", "exact") != "exact":
                self._debug_print(f"    return_kind: {ret_info.return_kind}", 1)
            if getattr(ret_info, "summary_candidate_source_key", None) is not None:
                self._debug_print(
                    f"    summary_candidate_source_key: {ret_info.summary_candidate_source_key}",
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
        bound_parameter_storage_values: Optional[Dict[Tuple[Any, ...], Expression]] = None,
    ) -> Optional[FunctionReturnAnalysis]:
         # デバッグフラグを ConditionSimplifier に伝播
        from .condition import ConditionSimplifier
        ConditionSimplifier.DEBUG = self.debug
        ConditionSimplifier.reset_debug_state()
        
        current_function_ref = CallTargetRef.from_function(function)
        normalized_bound_parameter_values = self._normalize_bound_parameter_values(
            bound_parameter_values,
        )
        normalized_bound_parameter_storage_values = self._normalize_bound_parameter_storage_values(
            bound_parameter_storage_values,
        )
        analysis_scope_key = self._analysis_scope_key(
            current_function_ref,
            normalized_bound_parameter_values,
            normalized_bound_parameter_storage_values,
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
            message = "Decompilation failed!"
            self._last_analysis_failure = AnalysisFailure(
                status=ANALYSIS_STATUS_DECOMPILATION_FAILED,
                message=message,
                function_name=str(function.getName()),
            )
            self._debug_print(message)
            return None
        
        high_function = results.getHighFunction()
        if high_function is None:
            message = "HighFunction is None!"
            self._last_analysis_failure = AnalysisFailure(
                status=ANALYSIS_STATUS_HIGH_FUNCTION_MISSING,
                message=message,
                function_name=str(function.getName()),
            )
            self._debug_print(message)
            return None
        
        # Step 1: tracer / CFG infrastructure を先に構築する。
        # implicit passthrough parameter recovery でも CALLIND target を追跡するため、
        # PhiHandler が有効な状態で tracer を使えるようにしておく。
        tracer = self._make_tracer(
            high_function,
            bound_parameter_values=normalized_bound_parameter_values,
            bound_parameter_storage_values=normalized_bound_parameter_storage_values,
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

        with self._analysis_context(
            parameters,
            None,
            function_prototype=function_prototype,
            function_entry_address=self._function_entry_address(function),
        ):
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
                    bound_parameter_storage_values=normalized_bound_parameter_storage_values,
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
                        return_type_obj=return_type_obj,
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
                binary_id=self._binary_id,
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
            effect_incomplete_reasons = getattr(effect_summary, "incomplete_reasons", ())
            if not isinstance(effect_incomplete_reasons, (list, tuple, set, frozenset)):
                effect_incomplete_reasons = ()
            for note in effect_incomplete_reasons:
                if note not in result.analysis_notes:
                    result.analysis_notes.append(note)
            if getattr(effect_summary, "call_target_resolution_evidence", None):
                note = "effect_call_target_resolution_evidence"
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

                if not (return_type_obj is not None and self._is_void_type(return_type_obj)):
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
            self._clear_resolved_call_effect_blockers(result)

            self._synchronize_parameters_with_referenced_parameter_expressions(result)
            self._repair_mixed_scalar_signedness(result)
            self._normalize_return_partition(result)
            self._mark_incomplete_control_flow(result)

            summary_view = self._apply_structural_recurrence_summary(
                function,
                high_function,
                result,
                tracer,
            )
            if summary_view is not None:
                result = summary_view
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
                    self._clear_resolved_call_effect_blockers(result)
                    self._normalize_return_partition(result)
                    self._mark_incomplete_control_flow(result)
            if (
                result.has_symbolic_post_state_reads()
                and "symbolic_post_state_reads" not in result.analysis_notes
            ):
                result.analysis_notes.append("symbolic_post_state_reads")

            self._apply_outcome_partition_summaries(
                function,
                high_function,
                result,
            )
            self._normalize_return_partition(result)
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
    ) -> Optional[FunctionReturnAnalysis]:
        if analysis is None or not analysis.returns:
            return None

        summarizer = StructuralRecurrenceSummarizer(
            tracer,
            debug=self.debug,
            enable_completed_recovery_proofs=self.enable_completed_recovery_proofs,
        )
        should_try = analysis.has_unresolved_return_value() or any(
            reason in {"call_out_of_scope", "max_depth_exceeded", "phi_no_valid_branch", "phi_circular"}
            for reason in getattr(analysis, "unknown_event_reasons", [])
        )
        if not should_try:
            should_try = summarizer.has_summary_candidate(function, high_function, analysis)
        if not should_try:
            return None

        summary = summarizer.try_summarize_function(function, high_function, analysis)
        if summary is None:
            if self.debug:
                print("Summary return diagnostic: no_summary_candidate")
            return None
        summary_returns, summary_note = summary
        accepted = accept_summary_return_candidates(
            analysis,
            summary_returns,
            summary_note=summary_note,
            enable_completed_recovery_proofs=self.enable_completed_recovery_proofs,
        )
        if accepted.blockers:
            if self.debug:
                for candidate in accepted.candidates:
                    ret = getattr(candidate, "return_info", None)
                    conditions = [
                        getattr(cond, "to_string", lambda: repr(cond))()
                        for cond in (getattr(ret, "conditions", None) or [])
                    ]
                    value = getattr(getattr(ret, "value", None), "to_string", lambda: repr(getattr(ret, "value", None)))()
                    print(
                        "Summary return candidate rejected/status="
                        f"{getattr(candidate, 'acceptance_status', None)} "
                        f"blockers={list(getattr(candidate, 'validation_blockers', ()) or ())} "
                        f"conditions={conditions} value={value}"
                    )
            return analysis.with_summary_return_diagnostics(
                summary_return_candidates=accepted.candidates,
                blockers=tuple(accepted.blockers),
                reason=summary_note,
            )
        if not accepted.accepted_returns:
            return None
        accepted_view = analysis.with_accepted_return_partition(
            list(accepted.accepted_returns),
            summary_return_candidates=accepted.candidates,
            reason=summary_note,
        )
        attach_summary_return_acceptance_proof(
            accepted_view,
            candidates=accepted.candidates,
            accepted_returns=accepted.accepted_returns,
            summary_note=summary_note,
        )
        if summary_note not in accepted_view.analysis_notes:
            accepted_view.analysis_notes.append(summary_note)
        return accepted_view

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
        if not self._effect_summary_allows_pre_return_structural_summary(
            effect_summary,
            function=function,
            high_function=high_function,
            return_type=return_type,
            return_type_obj=return_type_obj,
        ):
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
            binary_id=self._binary_id,
        )
        summarizer = StructuralRecurrenceSummarizer(
            tracer,
            debug=self.debug,
            enable_completed_recovery_proofs=self.enable_completed_recovery_proofs,
        )
        summary = summarizer.try_summarize_pre_return_counted_scalar_loop(
            function,
            high_function,
            skeleton,
            return_ops,
        )
        if summary is None:
            return None

        summary_returns, summary_note = summary
        accepted = accept_summary_return_candidates(
            skeleton,
            summary_returns,
            summary_note=summary_note,
            enable_completed_recovery_proofs=self.enable_completed_recovery_proofs,
        )
        if accepted.blockers or not accepted.accepted_returns:
            return None
        result = skeleton.with_accepted_return_partition(
            list(accepted.accepted_returns),
            summary_return_candidates=accepted.candidates,
            reason=summary_note,
        )
        attach_summary_return_acceptance_proof(
            result,
            candidates=accepted.candidates,
            accepted_returns=accepted.accepted_returns,
            summary_note=summary_note,
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
        anchor = self._make_return_info(
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
                "pcode_op_ref": PcodeOpRef.from_pcode_op(
                    return_op,
                    binary_id=self._binary_id,
                    program_uid=self._program_identity(),
                    function_entry=self._function_entry_address(function),
                ),
            },
        )
        anchor.return_kind = "summary_anchor"
        anchor.acceptance_status = "anchor"
        return anchor

    def _effect_summary_allows_pre_return_structural_summary(
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
        if self._phase1_return_type_is_float(return_type, return_type_obj):
            self._debug_print("Declined pre-return counted loop summary: Phase 1 excludes FP return types")
            return False
        if self._function_body_has_phase1_pure_return_forbidden_ops(function):
            self._debug_print(
                "Declined pre-return counted loop summary: function body is not Phase 1 pure/no-memory"
            )
            return False
        if self._high_function_has_phase1_pure_return_forbidden_ops(high_function):
            self._debug_print(
                "Declined pre-return counted loop summary: HighFunction-visible body is not Phase 1 pure/no-memory"
            )
            return False
        if getattr(effect_summary, "effects", None):
            self._debug_print("Declined pre-return counted loop summary: effect summary contains memory writes")
            return False
        if getattr(effect_summary, "has_unsupported_call", False):
            self._debug_print("Declined pre-return counted loop summary: effect summary contains unsupported call")
            return False
        return True

    def _function_body_has_phase1_pure_return_forbidden_ops(self, function) -> bool:
        if function is None:
            return False
        program = getattr(self, "program", None)
        listing_getter = getattr(program, "getListing", None)
        body_getter = getattr(function, "getBody", None)
        if not callable(listing_getter) or not callable(body_getter):
            return True
        try:
            listing = listing_getter()
            body = body_getter()
        except Exception:
            return True
        if listing is None or body is None:
            return True
        get_instructions = getattr(listing, "getInstructions", None)
        if not callable(get_instructions):
            return True
        try:
            instructions = get_instructions(body, True)
        except TypeError:
            try:
                instructions = get_instructions(body)
            except Exception:
                return True
        except Exception:
            return True
        saw_op = False
        instruction_items, complete = self._collect_java_or_python_iterable(instructions)
        if not complete:
            return True
        for instruction in instruction_items:
            if instruction is None:
                return True
            try:
                pcode_ops = instruction.getPcode()
            except Exception:
                return True
            op_items, complete = self._collect_java_or_python_iterable(pcode_ops)
            if not complete:
                return True
            for op in op_items:
                saw_op = True
                mnemonic = getattr(op, "getMnemonic", lambda: None)()
                if str(mnemonic or "").strip().upper() == "BRANCH":
                    if self._phase1_direct_branch_escapes_function_body(instruction, body):
                        return True
                    continue
                if self._phase1_pure_return_forbids_mnemonic(mnemonic):
                    return True
        return not saw_op

    def _phase1_direct_branch_escapes_function_body(self, instruction, body) -> bool:
        target = self._resolve_local_branch_target(instruction)
        if target is None:
            return True
        return not self._phase1_body_contains_address(body, target)

    @staticmethod
    def _phase1_body_contains_address(body, target) -> bool:
        if body is None or target is None:
            return False
        contains = getattr(body, "contains", None)
        if callable(contains):
            try:
                return bool(contains(target))
            except Exception:
                pass
        try:
            min_addr = body.getMinAddress()
            max_addr = body.getMaxAddress()
            get_offset = getattr(target, "getOffset", None)
            min_offset = getattr(min_addr, "getOffset", None)
            max_offset = getattr(max_addr, "getOffset", None)
            if callable(get_offset) and callable(min_offset) and callable(max_offset):
                offset = int(get_offset())
                return int(min_offset()) <= offset <= int(max_offset())
        except Exception:
            return False
        return False

    def _high_function_has_phase1_pure_return_forbidden_ops(self, high_function) -> bool:
        if high_function is None:
            return True
        saw_op = False
        blocks, complete = self._collect_java_or_python_iterable(
            getattr(high_function, "getBasicBlocks", lambda: None)()
            if callable(getattr(high_function, "getBasicBlocks", None))
            else None
        )
        if not complete:
            return True
        for block in blocks:
            ops, complete = self._collect_java_or_python_iterable(
                getattr(block, "getIterator", lambda: None)()
            )
            if not complete:
                return True
            for op in ops:
                saw_op = True
                mnemonic = getattr(op, "getMnemonic", lambda: None)()
                if self._phase1_pure_return_forbids_mnemonic(mnemonic):
                    return True
        return not saw_op

    @staticmethod
    def _phase1_pure_return_forbids_mnemonic(mnemonic: Optional[str]) -> bool:
        name = str(mnemonic or "").strip().upper()
        if not name:
            return True
        if name in {"CALL", "CALLIND", "STORE", "LOAD", "BRANCHIND", "CALLOTHER"}:
            return True
        if "FLOAT" in name or name in {"INT2FLOAT", "FLOAT2INT"}:
            return True
        return False

    @staticmethod
    def _collect_java_or_python_iterable(value) -> Tuple[Tuple[Any, ...], bool]:
        if value is None:
            return (), False
        has_next = getattr(value, "hasNext", None)
        next_item = getattr(value, "next", None)
        items: List[Any] = []
        if callable(has_next) and callable(next_item):
            while True:
                try:
                    has_item = has_next()
                    if not isinstance(has_item, bool):
                        return tuple(items), False
                    if not has_item:
                        break
                    items.append(next_item())
                except Exception:
                    return tuple(items), False
            return tuple(items), True
        try:
            iterator = iter(value)
        except TypeError:
            return (), False
        try:
            for item in iterator:
                items.append(item)
        except Exception:
            return tuple(items), False
        return tuple(items), True

    @staticmethod
    def _phase1_return_type_is_float(return_type: Optional[str], return_type_obj=None) -> bool:
        texts = [return_type, str(return_type_obj) if return_type_obj is not None else None]
        for text in texts:
            normalized = str(text or "").strip().lower()
            if not normalized:
                continue
            if any(token in normalized for token in ("float", "double", "longdouble", "long double")):
                return True
        return False

    def _normalize_return_partition(self, analysis: FunctionReturnAnalysis) -> None:
        if analysis is None:
            return
        self._normalize_return_callother_userops(analysis)
        analysis.returns = self._strip_stack_protector_only_conditions(analysis.returns)
        if "control_region_return_recovery" not in analysis.analysis_notes:
            analysis.returns = self._exclusivize_return_regions(analysis.returns)
        analysis.returns = self._merge_equivalent_return_infos(analysis.returns)

    def _normalize_return_callother_userops(self, analysis: FunctionReturnAnalysis) -> None:
        if analysis is None or not analysis.returns:
            return
        rewritten_returns: List[ReturnInfo] = []
        changed = False
        for info in analysis.returns or []:
            rewritten_value, value_changed = self._normalize_callother_userop_expression(info.value)
            rewritten_conditions: List[Condition] = []
            conditions_changed = False
            for condition in info.conditions or []:
                rewritten_expr, expr_changed = self._normalize_callother_userop_expression(condition.expression)
                rewritten_conditions.append(Condition(rewritten_expr, condition.negated))
                conditions_changed = conditions_changed or expr_changed
            if value_changed or conditions_changed:
                changed = True
                rewritten_returns.append(
                    replace(
                        info,
                        value=rewritten_value,
                        conditions=rewritten_conditions,
                    )
                )
            else:
                rewritten_returns.append(info)
        if not changed:
            return
        analysis.returns = rewritten_returns
        note = "object_centric_callother_userop_normalization"
        if note not in analysis.analysis_notes:
            analysis.analysis_notes.append(note)

    def _normalize_callother_userop_expression(self, expr: Optional[Expression]) -> Tuple[Optional[Expression], bool]:
        if expr is None:
            return expr, False
        if getattr(expr, "expr_type", None) == ExpressionType.PHI:
            changed = False
            branches = []
            for condition, value in getattr(expr, "value", None) or []:
                rewritten_condition = condition
                if condition is not None:
                    rewritten_condition_expr, condition_changed = self._normalize_callother_userop_expression(
                        condition.expression,
                    )
                    rewritten_condition = Condition(rewritten_condition_expr, condition.negated)
                    changed = changed or condition_changed
                rewritten_value, value_changed = self._normalize_callother_userop_expression(value)
                branches.append((rewritten_condition, rewritten_value))
                changed = changed or value_changed
            if changed:
                return expr.clone_with(value=branches), True
            return expr, False

        operands = list(getattr(expr, "operands", None) or [])
        changed = False
        rewritten_operands = []
        for operand in operands:
            rewritten_operand, operand_changed = self._normalize_callother_userop_expression(operand)
            rewritten_operands.append(rewritten_operand)
            changed = changed or operand_changed

        if (
            getattr(expr, "expr_type", None) == ExpressionType.INTRINSIC
            and getattr(expr, "name", None) == "CALLOTHER"
            and getattr(expr, "opcode", None) == 9
            and rewritten_operands
        ):
            userop_id = self._constant_expression_value(rewritten_operands[0])
            userop_name = self._program_userop_name(userop_id)
            intrinsic = resolve_pcode_intrinsic(mnemonic=userop_name) if userop_name else None
            if intrinsic is not None:
                return (
                    Expression.intrinsic(
                        intrinsic.mnemonic,
                        rewritten_operands[1:],
                        size=max(1, int(getattr(expr, "size", 0) or 0)),
                        runtime_ref=getattr(expr, "runtime_ref", None),
                        opcode=intrinsic.opcode,
                    ),
                    True,
                )

        if changed:
            return expr.clone_with(operands=rewritten_operands), True
        return expr, False

    def _program_userop_name(self, userop_id: Optional[int]) -> Optional[str]:
        if userop_id is None:
            return None
        language = getattr(self.program, "getLanguage", lambda: None)()
        get_name = getattr(language, "getUserDefinedOpName", None)
        if not callable(get_name):
            return None
        try:
            name = get_name(int(userop_id))
        except Exception:
            return None
        return str(name) if name else None

    @staticmethod
    def _constant_expression_value(expr: Optional[Expression]) -> Optional[int]:
        if expr is None or getattr(expr, "expr_type", None) != ExpressionType.CONSTANT:
            return None
        try:
            return int(getattr(expr, "value", 0) or 0)
        except (TypeError, ValueError):
            return None

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
                    site_metadata=self._return_site_metadata_from_info(info),
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
                        site_metadata=self._return_site_metadata_from_info(info),
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

    def _apply_outcome_partition_summaries(
        self,
        function,
        high_function,
        analysis: FunctionReturnAnalysis,
    ) -> None:
        if analysis is None:
            return
        self._clear_outcome_partition_summaries(analysis)
        if self._try_apply_triangular_mod_caller_outcomes(high_function, analysis):
            return
        if self._try_apply_triangular_mod_optimized_outcomes(high_function, analysis):
            return
        if self._try_apply_branch_guarded_while_outcomes(high_function, analysis):
            return
        self._try_apply_single_guard_nonprogress_loop_outcomes(high_function, analysis)

    def _clear_outcome_partition_summaries(self, analysis: FunctionReturnAnalysis) -> None:
        """Drop synthetic outcome partition state before rebuilding it from current returns."""
        analysis.return_outcomes = ()
        analysis.divergence_outcomes = ()
        analysis.unknown_outcomes = ()

    def _try_apply_single_guard_nonprogress_loop_outcomes(
        self,
        high_function,
        analysis: FunctionReturnAnalysis,
    ) -> bool:
        if len(getattr(analysis, "parameters", []) or []) != 1:
            self._debug_print("Outcome loop summary declined: expected one parameter")
            return False
        if len(getattr(analysis, "returns", []) or []) != 1:
            self._debug_print("Outcome loop summary declined: expected one return")
            return False
        if getattr(analysis, "deferred_calls", None):
            self._debug_print("Outcome loop summary declined: deferred calls present")
            return False
        if self._high_function_has_forbidden_control_outcome_ops(high_function, allow_call=False):
            self._debug_print("Outcome loop summary declined: forbidden control/effect op present")
            return False
        if self._high_function_cbranch_count(high_function) < 1:
            self._debug_print("Outcome loop summary declined: no control guard")
            return False

        ret = analysis.returns[0]
        if self._constant_int_value(ret.value) != 0:
            self._debug_print("Outcome loop summary declined: return value is not zero")
            return False
        if len(ret.conditions or ()) != 1:
            self._debug_print("Outcome loop summary declined: expected one return guard")
            return False
        param = self._parameter_expression(analysis, 0)
        if param is None:
            self._debug_print("Outcome loop summary declined: parameter expression unavailable")
            return False
        nonpositive = self._signed_positive_condition(param).negate()
        if not (
            self._conditions_equivalent(ret.conditions, [nonpositive])
            or (
                len(ret.conditions or ()) == 1
                and self._condition_is_signed_nonpositive_of_param(ret.conditions[0], param)
            )
        ):
            self._debug_print("Outcome loop summary declined: return guard is not param nonpositive")
            return False
        divergence_guard = self._signed_positive_condition(param)

        analysis.return_outcomes = (
            ReturnOutcome(
                guard=tuple(ret.conditions or ()),
                value=ret.value,
                provenance={"source": "existing_return_partition"},
                return_info=ret,
            ),
        )
        divergence_proof = self._prove_single_guard_nonprogress_region_must_diverge(
            high_function,
            analysis,
            divergence_guard=divergence_guard,
            param=param,
        )
        if divergence_proof is not None:
            analysis.divergence_outcomes = (
                DivergenceOutcome(
                    guard=(divergence_guard,),
                    proof=divergence_proof,
                ),
            )
            analysis.unknown_outcomes = ()
            if "outcome_partition_proved_nonprogress_loop_divergence" not in analysis.analysis_notes:
                analysis.analysis_notes.append("outcome_partition_proved_nonprogress_loop_divergence")
        else:
            analysis.divergence_outcomes = ()
            analysis.unknown_outcomes = (
                UnknownOutcome(
                    guard=(divergence_guard,),
                    reason="must_diverge_proof_missing",
                    evidence={
                        "candidate_rule": "side_effect_free_nonprogress_loop_guard_complement",
                        "loop_has_cfg_cycle": self._high_function_has_cfg_cycle(high_function),
                        "nonreturning_region_candidate": self._high_function_has_nonreturning_region_candidate(high_function),
                        "has_control_guard": self._high_function_cbranch_count(high_function) > 0,
                        "forbidden_ops_absent": True,
                        "return_guard_equivalent_to_param_nonpositive": True,
                        "missing_proof": "scc_exit_impossibility_and_guard_preservation",
                    },
                ),
            )
            if "outcome_partition_unknown_nonprogress_loop" not in analysis.analysis_notes:
                analysis.analysis_notes.append("outcome_partition_unknown_nonprogress_loop")
        return True

    def _prove_single_guard_nonprogress_region_must_diverge(
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
            self._debug_print("Outcome loop divergence proof declined: unsupported divergence guard")
            return None
        if not (
            self._conditions_equivalent([divergence_guard], [self._signed_positive_condition(param)])
            or self._condition_is_signed_positive_of_param(divergence_guard, param)
        ):
            self._debug_print("Outcome loop divergence proof declined: divergence guard is not param positive")
            return None

        blocks = list(self._iter_high_basic_blocks(high_function))
        if not blocks:
            self._debug_print("Outcome loop divergence proof declined: no high-function blocks")
            return None
        if not self._high_function_has_cfg_cycle(high_function):
            self._debug_print("Outcome loop divergence proof declined: no CFG cycle")
            return None

        tracer = None
        if self.program is not None:
            try:
                tracer = self._make_tracer(high_function)
            except Exception:
                tracer = None
        cyclic_sccs = self._high_function_cyclic_sccs(blocks)
        if not cyclic_sccs:
            self._debug_print("Outcome loop divergence proof declined: no cyclic SCC")
            return None

        for scc in cyclic_sccs:
            proof = self._prove_scc_must_diverge_under_guard(
                scc,
                all_blocks=blocks,
                divergence_guard=divergence_guard,
                param=param,
                tracer=tracer,
            )
            if proof is not None:
                proof.update(
                    {
                        "proof_kind": "single_guard_nonprogress_must_diverge",
                        "candidate_rule": "side_effect_free_nonprogress_loop_guard_complement",
                        "guard": "param_positive",
                        "return_partition": "param_nonpositive_return_zero",
                    }
                )
                return proof
        return None

    def _prove_scc_must_diverge_under_guard(
        self,
        scc: Sequence[Any],
        *,
        all_blocks: Sequence[Any],
        divergence_guard: Condition,
        param: Expression,
        tracer: Optional[PcodeTracer],
    ) -> Optional[Dict[str, Any]]:
        scc_set = set(scc or ())
        scc_keys = {self._block_debug_key(block) for block in scc_set}
        if not scc_set:
            return None
        if any(self._block_has_return_op(block) for block in scc_set):
            self._debug_print("Outcome loop divergence proof declined: RETURN in candidate SCC")
            return None
        if any(self._block_writes_outcome_guard_state(block) for block in scc_set):
            self._debug_print("Outcome loop divergence proof declined: guard state write in SCC")
            return None
        if not self._scc_preserves_guard_dependencies(scc_set):
            self._debug_print("Outcome loop divergence proof declined: guard dependency is redefined in SCC")
            return None

        internal_guarded_continue = False
        internal_unconditional_continue = False
        exit_proofs = []
        for block in scc_set:
            for successor in self._block_successors(block):
                if self._block_debug_key(successor) in scc_keys:
                    edge_condition = self._edge_condition_for_successor(block, successor, tracer)
                    if edge_condition is None:
                        internal_unconditional_continue = True
                    elif self._single_guard_condition_matches(edge_condition, divergence_guard, param):
                        internal_guarded_continue = True
                    continue

                edge_condition = self._edge_condition_for_successor(block, successor, tracer)
                if edge_condition is None:
                    self._debug_print("Outcome loop divergence proof declined: SCC exit without edge guard")
                    return None
                if not self._single_guard_conditions_are_contradictory(divergence_guard, edge_condition, param):
                    self._debug_print(
                        "Outcome loop divergence proof declined: SCC exit is feasible under divergence guard "
                        f"(divergence={divergence_guard.to_string()}, exit={edge_condition.to_string()})"
                    )
                    return None
                exit_proofs.append(
                    {
                        "source": self._block_debug_key(block),
                        "target": self._block_debug_key(successor),
                        "guard_relation": "divergence_guard_and_exit_guard_unsat",
                    }
                )

        entry_proofs = []
        has_guarded_entry = False
        has_unconditional_entry = False
        for block in all_blocks or ():
            if self._block_debug_key(block) in scc_keys:
                continue
            for successor in self._block_successors(block):
                if self._block_debug_key(successor) not in scc_keys:
                    continue
                edge_condition = self._edge_condition_for_successor(block, successor, tracer)
                if edge_condition is None:
                    if self._block_predecessor_count(block) != 0:
                        self._debug_print("Outcome loop divergence proof declined: unconditional SCC entry is not from function entry")
                        return None
                    has_unconditional_entry = True
                    entry_proofs.append(
                        {
                            "source": self._block_debug_key(block),
                            "target": self._block_debug_key(successor),
                            "guard_relation": "unconditional_entry_then_internal_guard",
                        }
                    )
                elif self._single_guard_condition_matches(edge_condition, divergence_guard, param):
                    has_guarded_entry = True
                    entry_proofs.append(
                        {
                            "source": self._block_debug_key(block),
                            "target": self._block_debug_key(successor),
                            "guard_relation": "entry_guard_equivalent_to_divergence_guard",
                        }
                    )
                else:
                    self._debug_print(
                        "Outcome loop divergence proof declined: SCC entry guard does not match divergence guard "
                        f"(divergence={divergence_guard.to_string()}, entry={edge_condition.to_string()})"
                    )
                    return None

        if not has_guarded_entry and not has_unconditional_entry:
            self._debug_print("Outcome loop divergence proof declined: candidate SCC has no proved external entry")
            return None
        if has_guarded_entry:
            preservation_ok = internal_unconditional_continue or internal_guarded_continue
        elif has_unconditional_entry:
            preservation_ok = internal_guarded_continue
        else:
            preservation_ok = False
        if not preservation_ok:
            self._debug_print("Outcome loop divergence proof declined: no guarded/invariant-preserving continue edge")
            return None

        return {
            "scc_blocks": [self._block_debug_key(block) for block in scc_set],
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

    def _high_function_cyclic_sccs(self, blocks: Sequence[Any]) -> List[Tuple[Any, ...]]:
        key_to_block = {self._block_debug_key(block): block for block in blocks or ()}
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

            for successor in self._block_successors(key_to_block[block_key]):
                successor_key = self._block_debug_key(successor)
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
                self._block_debug_key(successor) in component_set
                for item in component
                for successor in self._block_successors(key_to_block[item])
            ):
                components.append(tuple(key_to_block[item] for item in component))

        for block in blocks or ():
            key = self._block_debug_key(block)
            if key not in indices:
                strongconnect(key)
        return components

    def _block_successors(self, block) -> Tuple[Any, ...]:
        successors = []
        out_size = int(getattr(block, "getOutSize", lambda: 0)() or 0)
        for index in range(out_size):
            successor = getattr(block, "getOut", lambda _idx: None)(index)
            if successor is not None:
                successors.append(successor)
        return tuple(successors)

    def _block_predecessor_count(self, block) -> int:
        return int(getattr(block, "getInSize", lambda: 0)() or 0)

    def _block_has_return_op(self, block) -> bool:
        return any(getattr(op, "getMnemonic", lambda: None)() == "RETURN" for op in self._iter_high_block_ops(block))

    def _block_writes_outcome_guard_state(self, block) -> bool:
        for op in self._iter_high_block_ops(block):
            if bool(getattr(op, "writes_guard_state", False)):
                return True
        return False

    def _scc_preserves_guard_dependencies(self, scc_set: Set[Any]) -> bool:
        guard_dependency_keys: Set[Tuple[Any, ...]] = set()
        for block in scc_set:
            cbranch = self._first_high_block_cbranch(block)
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
            if not self._collect_guard_dependency_varnodes(
                condition_varnode,
                guard_dependency_keys,
                is_root=True,
                seen=set(),
            ):
                return False

        if not guard_dependency_keys:
            return True

        for block in scc_set:
            for op in self._iter_high_block_ops(block):
                output = getattr(op, "getOutput", lambda: None)()
                if output is None:
                    continue
                output_key = self._varnode_guard_dependency_key(output)
                if output_key in guard_dependency_keys:
                    return False
        return True

    def _collect_guard_dependency_varnodes(
        self,
        varnode,
        guard_dependency_keys: Set[Tuple[Any, ...]],
        *,
        is_root: bool,
        seen: Set[Tuple[Any, ...]],
    ) -> bool:
        if varnode is None:
            return False
        key = self._varnode_guard_dependency_key(varnode)
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
            if not self._collect_guard_dependency_varnodes(
                child,
                guard_dependency_keys,
                is_root=False,
                seen=seen,
            ):
                return False
        return True

    def _varnode_guard_dependency_key(self, varnode) -> Tuple[Any, ...]:
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

    def _edge_condition_for_successor(
        self,
        block,
        successor,
        tracer: Optional[PcodeTracer],
    ) -> Optional[Condition]:
        edge_conditions = getattr(block, "_edge_conditions", None)
        if isinstance(edge_conditions, Mapping):
            for key in (successor, id(successor), self._block_debug_key(successor)):
                condition = edge_conditions.get(key)
                if condition is not None:
                    return condition

        cbranch = self._first_high_block_cbranch(block)
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
        if true_out is not None and self._same_high_block(true_out, successor):
            return Condition(expr, False)
        if false_out is not None and self._same_high_block(false_out, successor):
            return Condition(expr, True)
        relation = self._direct_cbranch_successor_relation(cbranch, block, successor)
        if relation == "true":
            return Condition(expr, False)
        if relation == "false":
            return Condition(expr, True)
        return None

    def _direct_cbranch_successor_relation(self, cbranch, block, successor) -> Optional[str]:
        target_keys = self._cbranch_direct_target_keys(cbranch, block)
        if not target_keys:
            return None
        successor_keys = self._block_start_address_keys(successor)
        if successor_keys & target_keys:
            return "true"

        successors = self._block_successors(block)
        if len(successors) != 2:
            return None
        target_successors = [
            candidate
            for candidate in successors
            if self._block_start_address_keys(candidate) & target_keys
        ]
        if len(target_successors) != 1:
            return None
        if self._same_high_block(target_successors[0], successor):
            return "true"
        return "false"

    def _cbranch_direct_target_keys(self, cbranch, block) -> Set[Tuple[str, int]]:
        try:
            if int(getattr(cbranch, "getNumInputs", lambda: 0)() or 0) < 1:
                return set()
            target = cbranch.getInput(0)
        except Exception:
            return set()
        source_spaces = self._block_start_address_spaces(block)
        if len(source_spaces) != 1:
            return set()
        return self._address_like_keys(target, default_space=next(iter(source_spaces)))

    def _block_start_address_keys(self, block) -> Set[Tuple[str, int]]:
        keys: Set[Tuple[str, int]] = set()
        for getter_name in ("getStart", "getMinAddress"):
            try:
                value = getattr(block, getter_name, lambda: None)()
            except Exception:
                value = None
            keys.update(self._address_like_keys(value))
        return keys

    def _block_start_address_spaces(self, block) -> Set[str]:
        return {
            space
            for space, _offset in self._block_start_address_keys(block)
            if space
        }

    def _address_like_keys(
        self,
        value,
        *,
        default_space: Optional[str] = None,
    ) -> Set[Tuple[str, int]]:
        if value is None:
            return set()
        keys: Set[Tuple[str, int]] = set()
        try:
            is_constant = getattr(value, "isConstant", lambda: False)
            if callable(is_constant) and is_constant():
                address = getattr(value, "getAddress", lambda: None)()
                offset = None
                if address is not None:
                    offset = getattr(address, "getOffset", lambda: None)()
                if offset is None:
                    try:
                        offset = int(value)
                    except Exception:
                        offset = None
                if default_space and offset is not None:
                    keys.add((str(default_space), int(offset)))
                return keys
        except Exception:
            return set()
        try:
            offset = getattr(value, "getOffset", lambda: None)()
            if offset is not None:
                space_name = self._address_space_name(value)
                if space_name:
                    keys.add((space_name, int(offset)))
        except Exception:
            pass
        try:
            address = getattr(value, "getAddress", lambda: None)()
            if address is not None and address is not value:
                keys.update(self._address_like_keys(address, default_space=default_space))
        except Exception:
            pass
        return keys

    def _address_space_name(self, address) -> Optional[str]:
        try:
            space = getattr(address, "getAddressSpace", lambda: None)()
            name = getattr(space, "getName", lambda: None)()
            if name is None:
                return None
            return str(name)
        except Exception:
            return None

    def _first_high_block_cbranch(self, block):
        for op in self._iter_high_block_ops(block):
            if getattr(op, "getMnemonic", lambda: None)() == "CBRANCH":
                return op
        return None

    def _conditions_are_unsat(self, conditions: Sequence[Condition]) -> bool:
        return ConditionSMTOracle.conjunction_is_unsat(list(conditions or ())) is True

    def _single_guard_condition_matches(
        self,
        condition: Condition,
        divergence_guard: Condition,
        param: Expression,
    ) -> bool:
        return (
            condition.equals(divergence_guard)
            or self._conditions_equivalent([condition], [divergence_guard])
            or (
                self._condition_is_signed_positive_of_param(condition, param)
                and self._condition_is_signed_positive_of_param(divergence_guard, param)
            )
        )

    def _single_guard_conditions_are_contradictory(
        self,
        divergence_guard: Condition,
        edge_condition: Condition,
        param: Expression,
    ) -> bool:
        return (
            edge_condition.equals(divergence_guard.negate())
            or self._conditions_are_unsat([divergence_guard, edge_condition])
            or (
                self._condition_is_signed_positive_of_param(divergence_guard, param)
                and self._condition_is_signed_nonpositive_of_param(edge_condition, param)
            )
        )

    def _same_high_block(self, left, right) -> bool:
        if left is right:
            return True
        try:
            if left == right:
                return True
        except Exception:
            pass
        return self._block_debug_key(left) == self._block_debug_key(right)

    def _block_debug_key(self, block) -> Any:
        try:
            index = getattr(block, "getIndex", lambda: None)()
            if index is not None:
                return int(index)
        except Exception:
            pass
        try:
            start = getattr(block, "getStart", lambda: None)()
            if start is not None:
                return str(start)
        except Exception:
            pass
        return f"block@{id(block):x}"

    def _iter_outcome_call_candidates(
        self,
        analysis: FunctionReturnAnalysis,
    ) -> Iterable[Tuple[Optional[CallTargetRef], Tuple[Expression, ...], str, str]]:
        seen: Set[Tuple[Any, ...]] = set()
        for info in getattr(analysis, "deferred_calls", {}).values():
            deferred_ref = getattr(info, "deferred_call_ref", None)
            pcode_ref = getattr(deferred_ref, "pcode_op_ref", None)
            stable_key_fn = getattr(pcode_ref, "stable_key", None)
            key = stable_key_fn() if callable(stable_key_fn) else ("deferred", id(info))
            if key in seen:
                continue
            seen.add(key)
            yield (
                getattr(info, "target_ref", None),
                tuple(getattr(info, "arguments", None) or ()),
                getattr(info, "call_argument_recovery_status", "inconclusive"),
                "deferred_call",
            )

        effect_summary = getattr(analysis, "effect_summary", None)
        evidence = getattr(effect_summary, "call_argument_evidence", None)
        if not evidence:
            return
        for key, call_evidence in evidence.items():
            stable_key = getattr(call_evidence, "stable_key", lambda: None)()
            candidate_key = stable_key if stable_key is not None else ("effect", key)
            if candidate_key in seen:
                continue
            seen.add(candidate_key)
            is_usable = getattr(call_evidence, "is_usable", lambda: False)
            if not callable(is_usable) or not is_usable():
                continue
            yield (
                getattr(call_evidence, "target_ref", None),
                tuple(getattr(call_evidence, "arguments", None) or ()),
                getattr(call_evidence, "recovery_status", "inconclusive"),
                "effect_call_argument_evidence",
            )

    def _try_apply_triangular_mod_caller_outcomes(
        self,
        high_function,
        analysis: FunctionReturnAnalysis,
    ) -> bool:
        if len(getattr(analysis, "parameters", []) or []) != 1:
            self._debug_print("Outcome caller summary declined: expected one parameter")
            return False
        if self._high_function_has_forbidden_control_outcome_ops(high_function, allow_call=True):
            self._debug_print("Outcome caller summary declined: forbidden control/effect op present")
            return False

        param = self._parameter_expression(analysis, 0)
        if param is None:
            self._debug_print("Outcome caller summary declined: parameter expression unavailable")
            return False
        matched_call = None
        matched_source = None
        for target_ref, args_tuple, status, source in self._iter_outcome_call_candidates(analysis):
            args = list(args_tuple or ())
            if len(args) != 1 or not self._expression_is_param_minus_one(args[0], param):
                self._debug_print("Outcome caller summary skipped deferred call: argument is not param_minus_one")
                continue
            if status != "complete":
                self._debug_print(f"Outcome caller summary skipped deferred call: argument recovery status={status}")
                continue
            callee_analysis = self._cached_callee_analysis_for_outcome_summary(target_ref)
            if not self._analysis_has_positive_region_outcome_obligation(callee_analysis):
                self._debug_print("Outcome caller summary skipped deferred call: callee outcome contract unavailable")
                continue
            matched_call = (target_ref, args[0], status)
            matched_source = source
            break
        if matched_call is None:
            self._debug_print("Outcome caller summary declined: no matching callee outcome contract for param_minus_one call")
            return False

        return_size = self._analysis_return_size_bytes(analysis)
        one = Expression.constant(1, max(1, int(param.size or return_size or 4)))
        nonpositive = self._signed_positive_condition(param).negate()
        eq_one = Condition(Expression.binary_op("INT_EQUAL", param, one), False)

        zero_ret, one_ret = self._find_caller_return_partition_for_param_minus_one_obligation(
            analysis,
            param=param,
            nonpositive=nonpositive,
            eq_one=eq_one,
        )
        if zero_ret is None or one_ret is None:
            self._debug_print("Outcome caller summary declined: caller return partition/value proof unavailable")
            return False
        analysis.returns = [zero_ret, one_ret]
        analysis.return_outcomes = (
            ReturnOutcome(guard=tuple(zero_ret.conditions), value=zero_ret.value, provenance={"source": "callee_positive_region_caller_summary"}, return_info=zero_ret),
            ReturnOutcome(guard=tuple(one_ret.conditions), value=one_ret.value, provenance={"source": "callee_positive_region_caller_summary"}, return_info=one_ret),
        )
        analysis.divergence_outcomes = ()
        analysis.unknown_outcomes = (
            UnknownOutcome(
                guard=(self._return_partition_miss_guard([zero_ret, one_ret]),),
                reason="callee_positive_region_outcome_proof_missing",
                evidence={
                    "candidate_rule": "callee_positive_region_outcome_obligation_bv_argument_binding",
                    "argument_binding": "param_minus_one",
                    "argument_recovery_status": matched_call[2],
                    "call_evidence_source": matched_source,
                    "missing_proof": "callee_positive_region_outcome_resolution_and_bv_substitution",
                },
            ),
        )
        if "outcome_partition_unknown_callee_positive_region" not in analysis.analysis_notes:
            analysis.analysis_notes.append("outcome_partition_unknown_callee_positive_region")
        return True

    def _find_caller_return_partition_for_param_minus_one_obligation(
        self,
        analysis: FunctionReturnAnalysis,
        *,
        param: Expression,
        nonpositive: Condition,
        eq_one: Condition,
    ) -> Tuple[Optional[ReturnInfo], Optional[ReturnInfo]]:
        zero_ret = None
        one_ret = None
        for ret in getattr(analysis, "returns", []) or ():
            conditions = tuple(getattr(ret, "conditions", ()) or ())
            if zero_ret is None and self._constant_int_value(getattr(ret, "value", None)) == 0:
                if self._conditions_equivalent(conditions, [nonpositive]) or (
                    len(conditions) == 1
                    and self._condition_is_signed_nonpositive_of_param(conditions[0], param)
                ):
                    zero_ret = ret
                    continue
            if one_ret is None and self._caller_return_value_matches_param_on_eq_one(
                getattr(ret, "value", None),
                param,
            ):
                if self._conditions_equivalent(conditions, [eq_one]) or any(
                    self._condition_is_param_equal_const(condition, param, 1)
                    for condition in conditions
                ):
                    one_ret = ret
        return zero_ret, one_ret

    def _caller_return_value_matches_param_on_eq_one(
        self,
        value: Optional[Expression],
        param: Expression,
    ) -> bool:
        if value is None:
            return False
        if self._expression_is_same_parameter_ignoring_subpiece(value, param):
            return True
        return self._constant_int_value(value) == 1

    def _cached_callee_analysis_for_outcome_summary(
        self,
        target_ref: Optional[CallTargetRef],
    ) -> Optional[FunctionReturnAnalysis]:
        if target_ref is None:
            return None
        candidate_keys: List[Tuple[Any, ...]] = []
        try:
            candidate_keys.append(self._analysis_scope_key(target_ref))
        except Exception:
            pass
        active_key = self._target_active_key(target_ref)
        if active_key is not None:
            candidate_keys.append(active_key)
        try:
            function_obj = getattr(target_ref, "function_obj", None) or self._resolve_target_function(target_ref)
        except Exception:
            function_obj = None
        function_key = self._function_cache_key(function_obj)
        if function_key is not None:
            candidate_keys.append(function_key)
        seen: Set[Tuple[Any, ...]] = set()
        for key in candidate_keys:
            if key in seen:
                continue
            seen.add(key)
            cached = self._call_analysis_cache.get(key)
            if cached is not None:
                return cached
        return None

    def _analysis_has_positive_region_outcome_obligation(
        self,
        analysis: Optional[FunctionReturnAnalysis],
    ) -> bool:
        if analysis is None:
            return False
        if len(getattr(analysis, "parameters", []) or []) != 1:
            return False
        param = self._parameter_expression(analysis, 0)
        if param is None:
            return False
        return_outcomes = tuple(getattr(analysis, "return_outcomes", ()) or ())
        unknown_outcomes = tuple(getattr(analysis, "unknown_outcomes", ()) or ())
        divergence_outcomes = tuple(getattr(analysis, "divergence_outcomes", ()) or ())
        if len(return_outcomes) != 1 or not (unknown_outcomes or divergence_outcomes):
            return False
        ret = return_outcomes[0]
        if self._constant_int_value(getattr(ret, "value", None)) != 0:
            return False
        nonpositive = self._signed_positive_condition(param).negate()
        if not (
            self._conditions_equivalent(tuple(getattr(ret, "guard", ()) or ()), [nonpositive])
            or (
                len(tuple(getattr(ret, "guard", ()) or ())) == 1
                and self._condition_is_signed_nonpositive_of_param(tuple(getattr(ret, "guard", ()) or ())[0], param)
            )
        ):
            return False
        positive = self._signed_positive_condition(param)
        for outcome in (*unknown_outcomes, *divergence_outcomes):
            guard = tuple(getattr(outcome, "guard", ()) or ())
            if self._conditions_equivalent(guard, [positive]) or (
                len(guard) == 1
                and self._condition_is_signed_positive_of_param(guard[0], param)
            ):
                return True
        return False

    def _try_apply_branch_guarded_while_outcomes(
        self,
        high_function,
        analysis: FunctionReturnAnalysis,
    ) -> bool:
        if len(getattr(analysis, "parameters", []) or []) != 2:
            self._debug_print("Outcome branch-guarded while summary declined: expected two parameters")
            return False
        if getattr(analysis, "deferred_calls", None):
            self._debug_print("Outcome branch-guarded while summary declined: deferred calls present")
            return False
        if self._high_function_has_forbidden_control_outcome_ops(high_function, allow_call=False):
            self._debug_print("Outcome branch-guarded while summary declined: forbidden control/effect op present")
            return False
        if self._high_function_cbranch_count(high_function) < 2:
            self._debug_print("Outcome branch-guarded while summary declined: expected two control guards")
            return False
        if not any(
            self._expression_contains_phi_circular(ret.value)
            or self._return_info_candidate_phi_origin_keys(ret)
            for ret in analysis.returns or ()
        ):
            self._debug_print("Outcome branch-guarded while summary declined: no phi_circular return or candidate provenance")
            return False

        role_params = self._infer_branch_guarded_while_role_parameters(analysis)
        if role_params is None:
            self._debug_print("Outcome branch-guarded while summary declined: role parameters unavailable")
            return False
        t_param, c_param = role_params
        if t_param is None or c_param is None:
            self._debug_print("Outcome branch-guarded while summary declined: parameter expression unavailable")
            return False
        t_positive = self._signed_positive_condition(t_param)
        c_positive = self._signed_positive_condition(c_param)
        c_nonpositive = c_positive.negate()
        t_nonpositive = t_positive.negate()

        zero_ret, initial_c_ret = self._find_branch_guarded_while_return_partition(
            analysis,
            high_function=high_function,
            c_param=c_param,
            c_nonpositive=c_nonpositive,
            c_positive=c_positive,
            t_positive=t_positive,
        )
        if zero_ret is None or initial_c_ret is None:
            self._debug_print("Outcome branch-guarded while summary declined: return partition/value proof unavailable")
            return False
        divergence_proof = self._prove_branch_guarded_while_nonprogress_must_diverge(
            high_function,
            invariant_conditions=(c_positive, t_nonpositive),
        )
        if divergence_proof is None:
            divergence_proof = self._prove_branch_guarded_structural_nonprogress_must_diverge(
                high_function,
                analysis=analysis,
                initial_c_ret=initial_c_ret,
                invariant_conditions=(c_positive, t_nonpositive),
            )
        analysis.returns = [zero_ret, initial_c_ret]
        analysis.return_outcomes = (
            ReturnOutcome(guard=tuple(zero_ret.conditions), value=zero_ret.value, provenance={"source": "branch_guarded_affine_recurrence"}, return_info=zero_ret),
            ReturnOutcome(guard=tuple(initial_c_ret.conditions), value=initial_c_ret.value, provenance={"source": "branch_guarded_affine_recurrence"}, return_info=initial_c_ret),
        )
        if divergence_proof is not None:
            analysis.divergence_outcomes = (
                DivergenceOutcome(
                    guard=(c_positive, t_nonpositive),
                    proof=divergence_proof,
                ),
            )
            analysis.unknown_outcomes = ()
            if "outcome_partition_proved_branch_guarded_while_divergence" not in analysis.analysis_notes:
                analysis.analysis_notes.append("outcome_partition_proved_branch_guarded_while_divergence")
        else:
            analysis.divergence_outcomes = ()
            analysis.unknown_outcomes = (
                UnknownOutcome(
                    guard=(c_positive, t_nonpositive),
                    reason="branch_guarded_recurrence_proof_missing",
                    evidence={
                        "candidate_rule": "branch_guarded_loop_invariant_nonprogress",
                        "state_reference": "inferred_state_count_parameter",
                        "state_parameter": getattr(c_param, "name", None) or getattr(c_param, "value", None),
                        "forbidden_ops_absent": True,
                        "loop_has_cfg_cycle": self._high_function_has_cfg_cycle(high_function),
                        "has_control_guards": True,
                        "missing_proof": "scc_exit_impossibility_guard_preservation_and_affine_transition",
                    },
                ),
            )
            if "outcome_partition_unknown_branch_guarded_while" not in analysis.analysis_notes:
                analysis.analysis_notes.append("outcome_partition_unknown_branch_guarded_while")
        return True

    def _infer_branch_guarded_while_role_parameters(
        self,
        analysis: FunctionReturnAnalysis,
    ) -> Optional[Tuple[Expression, Expression]]:
        params = tuple(getattr(analysis, "parameters", ()) or ())
        candidate_params = []
        for index in range(len(params)):
            param = self._parameter_expression(analysis, index)
            if param is not None:
                candidate_params.append(param)
        if len(candidate_params) < 2:
            return None

        returns = tuple(getattr(analysis, "returns", ()) or ())
        for c_param in candidate_params:
            c_positive = self._signed_positive_condition(c_param)
            c_nonpositive = c_positive.negate()
            zero_seed = None
            for ret in returns:
                if self._constant_int_value(getattr(ret, "value", None)) != 0:
                    continue
                conditions = tuple(getattr(ret, "conditions", ()) or ())
                if self._conditions_equivalent(conditions, [c_nonpositive]) or (
                    len(conditions) == 1
                    and self._condition_is_signed_nonpositive_of_param(conditions[0], c_param)
                ):
                    zero_seed = ret
                    break
            if zero_seed is None:
                continue
            for t_param in candidate_params:
                if self._expressions_same_key(t_param, c_param):
                    continue
                t_positive = self._signed_positive_condition(t_param)
                target_conditions = (c_positive, t_positive)
                if any(
                    self._conditions_overlap(tuple(getattr(ret, "conditions", ()) or ()), target_conditions)
                    and (
                        self._expression_is_same_parameter_ignoring_subpiece(getattr(ret, "value", None), c_param)
                        or self._expressions_equal_under_conditions_smt(
                            getattr(ret, "value", None),
                            c_param,
                            tuple(target_conditions) + tuple(getattr(ret, "conditions", ()) or ()),
                            getattr(analysis, "parameters", ()) or (),
                        )
                        or self._branch_guarded_affine_singleton_base_anchor_matches(
                            getattr(ret, "value", None),
                            tuple(getattr(ret, "conditions", ()) or ()),
                            c_param,
                            target_conditions,
                        )
                        or self._branch_guarded_affine_phi_step(getattr(ret, "value", None)) is not None
                        or self._return_info_candidate_phi_origin_keys(ret)
                    )
                    for ret in returns
                ):
                    return t_param, c_param
        return None

    def _prove_branch_guarded_structural_nonprogress_must_diverge(
        self,
        high_function,
        *,
        analysis: Optional[FunctionReturnAnalysis] = None,
        initial_c_ret: ReturnInfo,
        invariant_conditions: Sequence[Condition],
    ) -> Optional[Dict[str, Any]]:
        if high_function is None:
            return None
        structural_proof = self._branch_guarded_structural_proof_from_return(initial_c_ret)
        if structural_proof is None:
            return None
        if not self._validate_branch_guarded_structural_proof(
            high_function,
            structural_proof=structural_proof,
            analysis=analysis,
            initial_c_ret=initial_c_ret,
            invariant_conditions=invariant_conditions,
        ):
            return None
        nonprogress_backedges = self._tuple_field_from_structural_proof(
            structural_proof,
            "nonprogress_backedges",
        )
        conditional_progress_backedges = self._tuple_field_from_structural_proof(
            structural_proof,
            "conditional_progress_backedges",
        )
        conditional_progress_guard_keys = self._conditional_progress_guard_keys_from_structural_proof(
            structural_proof,
        )
        conditional_progress_guards_blocked = self._conditional_progress_guards_contradict_invariant(
            conditional_progress_guard_keys,
            target_conditions=tuple(getattr(initial_c_ret, "conditions", ()) or ()),
            invariant_conditions=tuple(invariant_conditions or ()),
        )
        if not nonprogress_backedges and not (conditional_progress_backedges and conditional_progress_guards_blocked):
            return None
        if not self._high_function_has_cfg_cycle(high_function):
            return None
        if self._high_function_has_forbidden_control_outcome_ops(high_function, allow_call=False):
            return None
        return {
            "proof_kind": "branch_guarded_structural_nonprogress_must_diverge",
            "candidate_rule": "branch_guarded_loop_invariant_nonprogress",
            "invariant": [condition.to_string() for condition in invariant_conditions or ()],
            "structural_recurrence_proof": structural_proof,
            "nonprogress_backedges": tuple(nonprogress_backedges),
            "conditional_progress_backedges": tuple(conditional_progress_backedges),
            "conditional_progress_guard_keys": tuple(sorted(conditional_progress_guard_keys.items(), key=repr)),
            "conditional_progress_guard_negated_by_invariant": bool(conditional_progress_guards_blocked),
            "state_preservation": "state_phi_nonprogress_backedge_identity",
            "accumulator_preservation": "accumulator_phi_nonprogress_backedge_identity",
            "loop_has_cfg_cycle": True,
            "forbidden_control_effect_ops_absent": True,
        }

    def _branch_guarded_structural_proof_from_return(
        self,
        ret: ReturnInfo,
    ) -> Optional[Tuple[Any, ...]]:
        source_key = getattr(ret, "summary_candidate_source_key", None)
        return self._find_branch_guarded_structural_proof_tuple(source_key)

    def _find_branch_guarded_structural_proof_tuple(
        self,
        value,
    ) -> Optional[Tuple[Any, ...]]:
        if not isinstance(value, tuple):
            return None
        if value and value[0] == "branch_guarded_affine_unit_count_structural_proof":
            return value
        for item in value:
            found = self._find_branch_guarded_structural_proof_tuple(item)
            if found is not None:
                return found
        return None

    def _validate_branch_guarded_structural_proof(
        self,
        high_function,
        *,
        structural_proof: Tuple[Any, ...],
        analysis: Optional[FunctionReturnAnalysis],
        initial_c_ret: ReturnInfo,
        invariant_conditions: Sequence[Condition],
    ) -> bool:
        if high_function is None:
            return False
        if self._field_value_from_structural_proof(structural_proof, "schema_version") != 1:
            return False
        if analysis is not None and self._field_value_from_structural_proof(
            structural_proof,
            "function",
        ) != getattr(analysis, "function_name", None):
            return False
        proof_target_keys = self._tuple_field_from_structural_proof(
            structural_proof,
            "target_guard_keys",
        )
        current_target_keys = tuple(
            sorted(
                (self._condition_identity_key(condition) for condition in tuple(getattr(initial_c_ret, "conditions", ()) or ())),
                key=repr,
            )
        )
        if proof_target_keys != current_target_keys:
            return False
        acc_phi_key = self._field_value_from_structural_proof(structural_proof, "acc_phi")
        state_phi_key = self._field_value_from_structural_proof(structural_proof, "state_phi")
        if not isinstance(acc_phi_key, tuple) or not isinstance(state_phi_key, tuple):
            return False
        try:
            tracer = self._make_tracer(high_function)
        except Exception:
            return False
        summarizer = StructuralRecurrenceSummarizer(
            tracer,
            debug=False,
            enable_completed_recovery_proofs=self.enable_completed_recovery_proofs,
        )
        acc_phi = None
        state_phi = None
        header_block = None
        for block in summarizer._iter_basic_blocks(high_function):
            for op in summarizer._iter_block_ops(block):
                if getattr(op, "getMnemonic", lambda: None)() != "MULTIEQUAL":
                    continue
                op_key = self._pcode_op_stable_key(op)
                if op_key == acc_phi_key:
                    acc_phi = op
                    header_block = block
                if op_key == state_phi_key:
                    state_phi = op
                    header_block = block if header_block is None else header_block
        if acc_phi is None or state_phi is None or header_block is None:
            return False
        acc_parent = getattr(acc_phi, "getParent", lambda: None)()
        state_parent = getattr(state_phi, "getParent", lambda: None)()
        if acc_parent is None or state_parent is None:
            return False
        if self._block_debug_key(acc_parent) != self._block_debug_key(state_parent):
            return False
        header_block = acc_parent
        acc_indices = summarizer._state_loop_phi_indices(header_block, acc_phi)
        state_indices = summarizer._state_loop_phi_indices(header_block, state_phi)
        if acc_indices is None or state_indices is None:
            return False
        _acc_init_index, acc_backedge_indices = acc_indices
        _state_init_index, state_backedge_indices = state_indices
        if tuple(int(index) for index in acc_backedge_indices) != tuple(int(index) for index in state_backedge_indices):
            return False
        progress_backedges = set(int(index) for index in self._tuple_field_from_structural_proof(structural_proof, "progress_backedges"))
        nonprogress_backedges = set(int(index) for index in self._tuple_field_from_structural_proof(structural_proof, "nonprogress_backedges"))
        conditional_progress_backedges = set(int(index) for index in self._tuple_field_from_structural_proof(structural_proof, "conditional_progress_backedges"))
        expected_conditional_guard_keys = self._conditional_progress_guard_keys_from_structural_proof(
            structural_proof,
        )
        proof_backedges = progress_backedges | nonprogress_backedges
        if not progress_backedges:
            return False
        if conditional_progress_backedges:
            proof_backedges |= conditional_progress_backedges
        if proof_backedges != set(int(index) for index in acc_backedge_indices):
            return False
        target_conditions = tuple(getattr(initial_c_ret, "conditions", ()) or ())
        if conditional_progress_backedges and not expected_conditional_guard_keys:
            return False
        if conditional_progress_backedges and set(expected_conditional_guard_keys) != conditional_progress_backedges:
            return False
        if conditional_progress_backedges and not self._conditional_progress_guards_contradict_invariant(
            expected_conditional_guard_keys,
            target_conditions=target_conditions,
            invariant_conditions=tuple(invariant_conditions or ()),
        ):
            return False
        acc_output = getattr(acc_phi, "getOutput", lambda: None)()
        state_output = getattr(state_phi, "getOutput", lambda: None)()
        if acc_output is None or state_output is None:
            return False
        acc_placeholder = Expression.variable("__branch_guarded_acc", size=max(1, int(getattr(acc_output, "getSize", lambda: 4)() or 4)))
        state_placeholder = Expression.variable("__branch_guarded_state", size=max(1, int(getattr(state_output, "getSize", lambda: 4)() or 4)))
        for backedge_index in acc_backedge_indices:
            index = int(backedge_index)
            acc_expr = summarizer._build_pcode_expression(
                acc_phi.getInput(index),
                placeholders={acc_output: acc_placeholder},
            )
            state_expr = summarizer._build_pcode_expression(
                state_phi.getInput(index),
                placeholders={state_output: state_placeholder},
            )
            if index in conditional_progress_backedges:
                acc_guard_key = self._placeholder_plus_unit_condition_guard_key(
                    acc_expr,
                    acc_placeholder,
                    target_conditions,
                )
                state_guard_key = self._placeholder_minus_one_unit_condition_guard_key(
                    state_expr,
                    state_placeholder,
                    target_conditions,
                )
                if acc_guard_key is None or state_guard_key is None:
                    return False
                if acc_guard_key != state_guard_key:
                    return False
                if expected_conditional_guard_keys.get(index) != acc_guard_key:
                    return False
                if index in nonprogress_backedges:
                    if not (
                        self._expression_is_placeholder_plus_zero_under_conditions(
                            acc_expr,
                            acc_placeholder,
                            invariant_conditions,
                        )
                        or self._expressions_equal_under_conditions_smt(
                            acc_expr,
                            acc_placeholder,
                            tuple(invariant_conditions or ()),
                            getattr(analysis, "parameters", ()) or (),
                        )
                    ):
                        return False
                    if not (
                        self._expression_is_placeholder_plus_zero_under_conditions(
                            state_expr,
                            state_placeholder,
                            invariant_conditions,
                        )
                        or self._expressions_equal_under_conditions_smt(
                            state_expr,
                            state_placeholder,
                            tuple(invariant_conditions or ()),
                            getattr(analysis, "parameters", ()) or (),
                        )
                    ):
                        return False
                continue
            if index in nonprogress_backedges:
                if not (
                    self._expressions_same_key(acc_expr, acc_placeholder)
                    or self._expression_is_placeholder_plus_zero_under_conditions(
                        acc_expr,
                        acc_placeholder,
                        invariant_conditions,
                    )
                    or self._expressions_equal_under_conditions_smt(
                        acc_expr,
                        acc_placeholder,
                        tuple(invariant_conditions or ()),
                        getattr(analysis, "parameters", ()) or (),
                    )
                ):
                    return False
                if not (
                    self._expressions_same_key(state_expr, state_placeholder)
                    or self._expression_is_placeholder_plus_zero_under_conditions(
                        state_expr,
                        state_placeholder,
                        invariant_conditions,
                    )
                    or self._expressions_equal_under_conditions_smt(
                        state_expr,
                        state_placeholder,
                        tuple(invariant_conditions or ()),
                        getattr(analysis, "parameters", ()) or (),
                    )
                ):
                    return False
                continue
            if index in progress_backedges:
                if not self._expression_is_placeholder_plus_one_under_conditions(
                    acc_expr,
                    acc_placeholder,
                    target_conditions,
                ):
                    return False
                if not self._expression_is_placeholder_minus_one_under_conditions(
                    state_expr,
                    state_placeholder,
                    target_conditions,
                ):
                    return False
                continue
            return False
        return self._state_phi_feeds_positive_loop_guard(
            high_function,
            summarizer=summarizer,
            header_block=header_block,
            backedge_indices=tuple(int(index) for index in state_backedge_indices),
            state_phi=state_phi,
            state_placeholder=state_placeholder,
            target_conditions=target_conditions,
            allow_latch_progress_guard=bool(conditional_progress_backedges),
        )

    @staticmethod
    def _tuple_field_from_structural_proof(
        proof: Tuple[Any, ...],
        field_name: str,
    ) -> Tuple[Any, ...]:
        for item in proof or ():
            if isinstance(item, tuple) and len(item) == 2 and item[0] == field_name:
                value = item[1]
                return tuple(value) if isinstance(value, (tuple, list)) else (value,)
        return ()

    @staticmethod
    def _field_value_from_structural_proof(
        proof: Tuple[Any, ...],
        field_name: str,
    ) -> Any:
        for item in proof or ():
            if isinstance(item, tuple) and len(item) == 2 and item[0] == field_name:
                return item[1]
        return None

    @staticmethod
    def _condition_identity_key(condition: Condition) -> Tuple[Any, ...]:
        return (
            "condition",
            expression_key_safe(getattr(condition, "expression", None)),
            bool(getattr(condition, "negated", False)),
        )

    def _conditional_progress_guard_keys_from_structural_proof(
        self,
        proof: Tuple[Any, ...],
    ) -> Dict[int, Tuple[Any, ...]]:
        result: Dict[int, Tuple[Any, ...]] = {}
        for item in self._tuple_field_from_structural_proof(proof, "conditional_progress_guard_keys"):
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

    def _condition_for_identity_key(
        self,
        key: Tuple[Any, ...],
        conditions: Sequence[Condition],
    ) -> Optional[Condition]:
        if not isinstance(key, tuple):
            return None
        for condition in conditions or ():
            if condition is not None and self._condition_identity_key(condition) == key:
                return condition
        return None

    def _conditional_progress_guards_contradict_invariant(
        self,
        guard_keys: Dict[int, Tuple[Any, ...]],
        *,
        target_conditions: Sequence[Condition],
        invariant_conditions: Sequence[Condition],
    ) -> bool:
        if not guard_keys:
            return False
        for guard_key in guard_keys.values():
            guard = self._condition_for_identity_key(guard_key, target_conditions)
            if guard is None:
                return False
            try:
                if ConditionSMTOracle.conjunction_is_unsat([guard] + list(invariant_conditions or ())) is not True:
                    return False
            except Exception:
                return False
        return True

    def _conditions_have_contradictory_pair(
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
                except Exception:
                    continue
        return False

    def _find_branch_guarded_while_return_partition(
        self,
        analysis: FunctionReturnAnalysis,
        *,
        high_function,
        c_param: Expression,
        c_nonpositive: Condition,
        c_positive: Condition,
        t_positive: Condition,
    ) -> Tuple[Optional[ReturnInfo], Optional[ReturnInfo]]:
        zero_ret = None
        initial_c_ret = None
        for ret in getattr(analysis, "returns", []) or ():
            conditions = tuple(getattr(ret, "conditions", ()) or ())
            if zero_ret is None and self._constant_int_value(getattr(ret, "value", None)) == 0:
                if self._conditions_equivalent(conditions, [c_nonpositive]) or (
                    len(conditions) == 1
                    and self._condition_is_signed_nonpositive_of_param(conditions[0], c_param)
                ):
                    zero_ret = ret
                    continue
            if initial_c_ret is None and self._expression_is_same_parameter_ignoring_subpiece(
                getattr(ret, "value", None),
                c_param,
            ):
                if self._conditions_equivalent(conditions, [c_positive, t_positive]):
                    initial_c_ret = ret
        if zero_ret is not None and initial_c_ret is None:
            initial_c_ret = self._synthesize_branch_guarded_affine_initial_count_return(
                high_function,
                analysis,
                c_param=c_param,
                c_positive=c_positive,
                t_positive=t_positive,
                zero_ret=zero_ret,
            )
        return zero_ret, initial_c_ret

    def _synthesize_branch_guarded_affine_initial_count_return(
        self,
        high_function,
        analysis: FunctionReturnAnalysis,
        *,
        c_param: Expression,
        c_positive: Condition,
        t_positive: Condition,
        zero_ret: ReturnInfo,
    ) -> Optional[ReturnInfo]:
        target_conditions = (c_positive, t_positive)
        candidate_returns = [
            ret
            for ret in tuple(getattr(analysis, "returns", ()) or ())
            if self._conditions_overlap(tuple(getattr(ret, "conditions", ()) or ()), target_conditions)
        ]
        if not candidate_returns:
            self._debug_print("Outcome branch-guarded affine proof declined: no target-overlapping returns")
            return None
        exact_base_returns: List[ReturnInfo] = []
        recursive_returns: List[Tuple[ReturnInfo, int]] = []
        ignored_artifacts: List[ReturnInfo] = []
        for ret in candidate_returns:
            conditions = tuple(getattr(ret, "conditions", ()) or ())
            value = getattr(ret, "value", None)
            if (
                self._expressions_equal_under_conditions_smt(
                    value,
                    c_param,
                    tuple(target_conditions) + conditions,
                    getattr(analysis, "parameters", ()) or (),
                )
                or self._branch_guarded_affine_singleton_base_anchor_matches(
                    value,
                    conditions,
                    c_param,
                    target_conditions,
                )
            ):
                exact_base_returns.append(ret)
                continue
            step = self._branch_guarded_affine_phi_step(value)
            implies_target = self._conditions_imply(conditions, target_conditions)
            if step is not None and implies_target:
                recursive_returns.append((ret, int(step)))
                continue
            if self.debug and (step is not None or self._expression_contains_phi_circular(value)):
                self._debug_print(
                    "Outcome branch-guarded affine candidate skipped: "
                    f"step={step}, implies_target={implies_target}, "
                    f"value={getattr(value, 'to_string', lambda: value)()}, "
                    f"conditions={[condition.to_string() for condition in conditions]}"
                )
            ignored_artifacts.append(ret)

        candidate_phi_origin_keys = tuple(
            sorted(
                {
                    key
                    for ret in candidate_returns
                    for key in self._return_info_candidate_phi_origin_keys(ret)
                },
                key=repr,
            )
        )
        return_phi_origin_keys = tuple(
            sorted(
                {
                    key
                    for ret in candidate_returns
                    for key in self._return_info_return_phi_origin_keys(ret)
                },
                key=repr,
            )
        )
        if not recursive_returns and not candidate_phi_origin_keys:
            self._debug_print("Outcome branch-guarded affine proof declined: recursive phi step missing")
            return None
        if recursive_returns:
            steps = {step for _ret, step in recursive_returns}
            if len(steps) != 1:
                self._debug_print(f"Outcome branch-guarded affine proof declined: mixed recursive steps {sorted(steps)}")
                return None
            step = next(iter(steps))
            if step <= 0 or step > 4:
                self._debug_print(f"Outcome branch-guarded affine proof declined: unsupported recursive step {step}")
                return None
        else:
            step = 1
        structural_proof = None
        exact_base_covers_target = bool(exact_base_returns) and self._return_conditions_cover_region(
            target_conditions,
            exact_base_returns,
        )
        if not exact_base_covers_target:
            structural_proof = self._prove_branch_guarded_affine_unit_count_recurrence(
                high_function,
                analysis=analysis,
                c_param=c_param,
                target_conditions=target_conditions,
                recursive_returns=tuple(ret for ret, _step in recursive_returns),
                candidate_phi_origin_keys=candidate_phi_origin_keys,
                return_phi_origin_keys=return_phi_origin_keys,
                nonprogress_conditions=(c_positive, t_positive.negate()),
                allow_latch_progress_guard=bool(exact_base_returns),
            )
            if structural_proof is None:
                if exact_base_returns:
                    self._debug_print("Outcome branch-guarded affine proof declined: exact base returns do not cover target")
                else:
                    self._debug_print("Outcome branch-guarded affine proof declined: exact base return missing")
                return None
            ignored_artifacts = [
                artifact for artifact in ignored_artifacts
                if not self._branch_guarded_artifact_is_imprecise_zero_seed(
                    artifact,
                    zero_ret=zero_ret,
                    parameters=getattr(analysis, "parameters", ()) or (),
                )
                and not self._branch_guarded_artifact_is_structural_accumulator_seed_projection(
                    artifact,
                    recursive_returns=tuple(ret for ret, _step in recursive_returns),
                    parameters=getattr(analysis, "parameters", ()) or (),
                )
            ]
            if ignored_artifacts and self.debug:
                for artifact in ignored_artifacts:
                    self._debug_print(
                        "Outcome branch-guarded affine artifact retained: "
                        f"value={getattr(getattr(artifact, 'value', None), 'to_string', lambda: getattr(artifact, 'value', None))()}, "
                        f"conditions={[condition.to_string() for condition in tuple(getattr(artifact, 'conditions', ()) or ())]}, "
                        f"site={self._return_site_key(artifact)}"
                    )
        proof_returns = list(exact_base_returns) + [ret for ret, _step in recursive_returns]
        if not self._branch_guarded_affine_ignored_artifacts_are_shadowed(
            ignored_artifacts,
            recursive_returns,
            getattr(analysis, "parameters", ()) or (),
        ):
            self._debug_print("Outcome branch-guarded affine proof declined: unshadowed target artifact return")
            return None

        anchor = recursive_returns[0][0] if recursive_returns else exact_base_returns[0]
        source_keys = tuple(
            self._return_info_summary_identity_key(ret)
            for ret in proof_returns
        )
        return ReturnInfo(
            address=str(getattr(anchor, "address", None) or getattr(analysis, "entry_point", None) or "outcome-summary"),
            value=c_param,
            conditions=list(target_conditions),
            branch_index=31_200,
            pcode_identity=getattr(anchor, "pcode_identity", None),
            pcode_order=getattr(anchor, "pcode_order", None),
            pcode_time=getattr(anchor, "pcode_time", None),
            pcode_op_ref=getattr(anchor, "pcode_op_ref", None),
            return_value_pcode_op_refs=tuple(getattr(anchor, "return_value_pcode_op_refs", ()) or ()),
            return_kind="outcome_summary",
            summary_candidate_id=("branch_guarded_affine_initial_count", getattr(analysis, "function_name", None)),
            summary_candidate_source_key=(
                "branch_guarded_affine_initial_count",
                ("step", step),
                ("candidate_phi_origin_keys", candidate_phi_origin_keys),
                ("return_phi_origin_keys", return_phi_origin_keys),
                ("structural_proof", structural_proof),
                ("sources", source_keys),
            ),
        )

    def _branch_guarded_artifact_is_imprecise_zero_seed(
        self,
        artifact: ReturnInfo,
        *,
        zero_ret: ReturnInfo,
        parameters: Sequence[Dict],
    ) -> bool:
        artifact_conditions = tuple(getattr(artifact, "conditions", ()) or ())
        zero_conditions = tuple(getattr(zero_ret, "conditions", ()) or ())
        if not self._expressions_equal_under_conditions_smt(
            getattr(artifact, "value", None),
            getattr(zero_ret, "value", None),
            artifact_conditions + zero_conditions,
            parameters,
        ):
            return False
        if not self._conditions_imply(zero_conditions, artifact_conditions):
            return False
        if self._conditions_imply(artifact_conditions, zero_conditions):
            return False
        return True

    def _branch_guarded_artifact_is_structural_accumulator_seed_projection(
        self,
        artifact: ReturnInfo,
        *,
        recursive_returns: Sequence[ReturnInfo],
        parameters: Sequence[Dict],
    ) -> bool:
        if self._constant_int_value(getattr(artifact, "value", None)) != 0:
            return False
        artifact_conditions = tuple(getattr(artifact, "conditions", ()) or ())
        artifact_site = self._return_site_key(artifact)
        for recursive in recursive_returns or ():
            recursive_conditions = tuple(getattr(recursive, "conditions", ()) or ())
            if artifact_site != self._return_site_key(recursive):
                continue
            if not (
                self._condition_lists_equivalent(list(artifact_conditions), list(recursive_conditions))
                or (
                    self._conditions_imply(artifact_conditions, recursive_conditions)
                    and self._conditions_imply(recursive_conditions, artifact_conditions)
                )
            ):
                continue
            if self._branch_guarded_affine_phi_step(getattr(recursive, "value", None)) == 1:
                return True
        return False

    def _prove_branch_guarded_affine_unit_count_recurrence(
        self,
        high_function,
        *,
        analysis: FunctionReturnAnalysis,
        c_param: Expression,
        target_conditions: Sequence[Condition],
        recursive_returns: Sequence[ReturnInfo],
        candidate_phi_origin_keys: Sequence[Tuple[Any, ...]] = (),
        return_phi_origin_keys: Sequence[Tuple[Any, ...]] = (),
        nonprogress_conditions: Sequence[Condition] = (),
        allow_latch_progress_guard: bool = False,
    ) -> Optional[Tuple[Any, ...]]:
        if high_function is None or self.program is None:
            return None
        recursive_origin_keys = set(candidate_phi_origin_keys or ())
        return_origin_keys = set(return_phi_origin_keys or ())
        for ret in recursive_returns or ():
            recursive_origin_keys.update(self._phi_circular_origin_stable_keys(getattr(ret, "value", None)))
            recursive_origin_keys.update(self._return_info_candidate_phi_origin_keys(ret))
            return_origin_keys.update(self._phi_circular_origin_stable_keys(getattr(ret, "value", None)))
            return_origin_keys.update(self._return_info_return_phi_origin_keys(ret))
        if not recursive_origin_keys:
            self._debug_print("Outcome branch-guarded structural proof declined: recursive phi origin unavailable")
            return None
        if not return_origin_keys:
            self._debug_print("Outcome branch-guarded structural proof declined: return phi origin unavailable")
            return None
        try:
            tracer = self._make_tracer(high_function)
        except Exception:
            self._debug_print("Outcome branch-guarded structural proof declined: tracer unavailable")
            return None
        summarizer = StructuralRecurrenceSummarizer(
            tracer,
            debug=False,
            enable_completed_recovery_proofs=self.enable_completed_recovery_proofs,
        )
        saw_acc_candidate = False
        saw_acc_transition = False
        saw_state_transition = False
        saw_state_guard = False
        for header_block in summarizer._iter_basic_blocks(high_function):
            phi_ops = [
                op for op in summarizer._iter_block_ops(header_block)
                if getattr(op, "getMnemonic", lambda: None)() == "MULTIEQUAL"
                and getattr(op, "getOutput", lambda: None)() is not None
            ]
            if len(phi_ops) < 2:
                continue
            if any(self._pcode_op_stable_key(phi_op) in recursive_origin_keys for phi_op in phi_ops):
                saw_acc_candidate = True
            for acc_phi in phi_ops:
                acc_phi_key = self._pcode_op_stable_key(acc_phi)
                acc_flows_to_return = self._acc_phi_flows_to_return_origin_phi(
                    acc_phi,
                    return_origin_keys,
                    summarizer=summarizer,
                    high_function=high_function,
                )
                if acc_phi_key not in return_origin_keys and not acc_flows_to_return:
                    if self.debug:
                        self._debug_print(
                            "Outcome branch-guarded structural proof acc candidate skipped: "
                            f"return provenance missing acc_phi={acc_phi_key}, "
                            f"return_origins={sorted(return_origin_keys, key=repr)}"
                        )
                    continue
                acc_indices = summarizer._state_loop_phi_indices(header_block, acc_phi)
                if acc_indices is None:
                    if self.debug:
                        self._debug_print("Outcome branch-guarded structural proof acc candidate skipped: loop phi indices unavailable")
                    continue
                acc_init_index, acc_backedge_indices = acc_indices
                acc_output = getattr(acc_phi, "getOutput", lambda: None)()
                if acc_output is None:
                    continue
                acc_placeholder = Expression.variable(
                    "__branch_guarded_acc",
                    size=max(1, int(getattr(acc_output, "getSize", lambda: 4)() or 4)),
                )
                acc_init = summarizer._build_pcode_expression(
                    acc_phi.getInput(acc_init_index),
                    placeholders={acc_output: acc_placeholder},
                )
                if self._constant_int_value(acc_init) != 0:
                    if self.debug:
                        self._debug_print(
                            "Outcome branch-guarded structural proof acc candidate skipped: "
                            f"init={self._debug_expr_summary(acc_init)}"
                        )
                    continue
                acc_progress_indices: Set[int] = set()
                acc_nonprogress_indices: Set[int] = set()
                acc_conditional_progress_keys: Dict[int, Tuple[Any, ...]] = {}
                acc_unknown_transition = False
                for backedge_index in acc_backedge_indices:
                    backedge_index_int = int(backedge_index)
                    acc_backedge_expr = summarizer._build_pcode_expression(
                        acc_phi.getInput(backedge_index),
                        placeholders={acc_output: acc_placeholder},
                    )
                    if self._expression_is_placeholder_plus_one(acc_backedge_expr, acc_placeholder):
                        acc_progress_indices.add(backedge_index_int)
                        continue
                    acc_guard_key = self._placeholder_plus_unit_condition_guard_key(
                        acc_backedge_expr,
                        acc_placeholder,
                        target_conditions,
                    )
                    if acc_guard_key is not None:
                        acc_progress_indices.add(backedge_index_int)
                        acc_conditional_progress_keys[backedge_index_int] = acc_guard_key
                        if (
                            self._expression_is_placeholder_plus_zero_under_conditions(
                                acc_backedge_expr,
                                acc_placeholder,
                                nonprogress_conditions,
                            )
                            or self._expressions_equal_under_conditions_smt(
                                acc_backedge_expr,
                                acc_placeholder,
                                tuple(nonprogress_conditions or ()),
                                getattr(analysis, "parameters", ()) or (),
                            )
                        ):
                            acc_nonprogress_indices.add(backedge_index_int)
                        continue
                    if (
                        self._expressions_same_key(acc_backedge_expr, acc_placeholder)
                        or self._expression_is_placeholder_plus_zero_under_conditions(
                            acc_backedge_expr,
                            acc_placeholder,
                            nonprogress_conditions,
                        )
                        or self._expressions_equal_under_conditions_smt(
                            acc_backedge_expr,
                            acc_placeholder,
                            tuple(nonprogress_conditions or ()),
                            getattr(analysis, "parameters", ()) or (),
                        )
                    ):
                        acc_nonprogress_indices.add(backedge_index_int)
                        continue
                    if self._expression_is_placeholder_plus_one_under_conditions(
                        acc_backedge_expr,
                        acc_placeholder,
                        target_conditions,
                    ):
                        acc_progress_indices.add(backedge_index_int)
                        continue
                    if self.debug:
                        self._debug_print(
                            "Outcome branch-guarded structural proof acc transition unrecognized: "
                            f"index={backedge_index_int}, expr={self._debug_expr_summary(acc_backedge_expr)}"
                        )
                    acc_unknown_transition = True
                    break
                if acc_unknown_transition or not acc_progress_indices:
                    continue
                saw_acc_transition = True
                for state_phi in phi_ops:
                    if state_phi is acc_phi:
                        continue
                    state_phi_key = self._pcode_op_stable_key(state_phi)
                    if acc_phi_key not in recursive_origin_keys and state_phi_key not in recursive_origin_keys:
                        continue
                    state_indices = summarizer._state_loop_phi_indices(header_block, state_phi)
                    if state_indices is None:
                        continue
                    state_init_index, state_backedge_indices = state_indices
                    if tuple(int(index) for index in state_backedge_indices) != tuple(int(index) for index in acc_backedge_indices):
                        continue
                    state_output = getattr(state_phi, "getOutput", lambda: None)()
                    if state_output is None:
                        continue
                    state_placeholder = Expression.variable(
                        "__branch_guarded_state",
                        size=max(1, int(getattr(state_output, "getSize", lambda: 4)() or 4)),
                    )
                    state_init = summarizer._build_pcode_expression(
                        state_phi.getInput(state_init_index),
                        placeholders={state_output: state_placeholder},
                    )
                    if not self._expression_is_same_parameter_ignoring_subpiece(state_init, c_param):
                        continue
                    state_progress_indices: Set[int] = set()
                    state_nonprogress_indices: Set[int] = set()
                    state_conditional_progress_keys: Dict[int, Tuple[Any, ...]] = {}
                    state_unknown_transition = False
                    for backedge_index in state_backedge_indices:
                        backedge_index_int = int(backedge_index)
                        state_backedge_expr = summarizer._build_pcode_expression(
                            state_phi.getInput(backedge_index),
                            placeholders={state_output: state_placeholder},
                        )
                        if self._expression_is_placeholder_minus_one(state_backedge_expr, state_placeholder):
                            state_progress_indices.add(backedge_index_int)
                            continue
                        state_guard_key = self._placeholder_minus_one_unit_condition_guard_key(
                            state_backedge_expr,
                            state_placeholder,
                            target_conditions,
                        )
                        if state_guard_key is not None:
                            state_progress_indices.add(backedge_index_int)
                            state_conditional_progress_keys[backedge_index_int] = state_guard_key
                            if (
                                self._expression_is_placeholder_plus_zero_under_conditions(
                                    state_backedge_expr,
                                    state_placeholder,
                                    nonprogress_conditions,
                                )
                                or self._expressions_equal_under_conditions_smt(
                                    state_backedge_expr,
                                    state_placeholder,
                                    tuple(nonprogress_conditions or ()),
                                    getattr(analysis, "parameters", ()) or (),
                                )
                            ):
                                state_nonprogress_indices.add(backedge_index_int)
                            continue
                        if (
                            self._expressions_same_key(state_backedge_expr, state_placeholder)
                            or self._expression_is_placeholder_plus_zero_under_conditions(
                                state_backedge_expr,
                                state_placeholder,
                                nonprogress_conditions,
                            )
                            or self._expressions_equal_under_conditions_smt(
                                state_backedge_expr,
                                state_placeholder,
                                tuple(nonprogress_conditions or ()),
                                getattr(analysis, "parameters", ()) or (),
                            )
                        ):
                            state_nonprogress_indices.add(backedge_index_int)
                            continue
                        if self._expression_is_placeholder_minus_one_under_conditions(
                            state_backedge_expr,
                            state_placeholder,
                            target_conditions,
                        ):
                            state_progress_indices.add(backedge_index_int)
                            continue
                        if self.debug:
                            self._debug_print(
                                "Outcome branch-guarded structural proof state transition unrecognized: "
                                f"index={backedge_index_int}, expr={self._debug_expr_summary(state_backedge_expr)}"
                            )
                        state_unknown_transition = True
                        break
                    if (
                        state_unknown_transition
                        or not state_progress_indices
                        or state_progress_indices != acc_progress_indices
                        or state_nonprogress_indices != acc_nonprogress_indices
                        or state_conditional_progress_keys != acc_conditional_progress_keys
                    ):
                        if self.debug:
                            self._debug_print(
                                "Outcome branch-guarded structural proof state transition set mismatch: "
                                f"state_unknown={state_unknown_transition}, "
                                f"acc_progress={sorted(acc_progress_indices)}, "
                                f"state_progress={sorted(state_progress_indices)}, "
                                f"acc_nonprogress={sorted(acc_nonprogress_indices)}, "
                                f"state_nonprogress={sorted(state_nonprogress_indices)}, "
                                f"acc_conditional={sorted(acc_conditional_progress_keys)}, "
                                f"state_conditional={sorted(state_conditional_progress_keys)}"
                            )
                        continue
                    saw_state_transition = True
                    if not self._state_phi_feeds_positive_loop_guard(
                        high_function,
                        summarizer=summarizer,
                        header_block=header_block,
                        backedge_indices=tuple(int(index) for index in state_backedge_indices),
                        state_phi=state_phi,
                        state_placeholder=state_placeholder,
                        target_conditions=target_conditions,
                        allow_latch_progress_guard=allow_latch_progress_guard,
                    ):
                        continue
                    saw_state_guard = True
                    return (
                        "branch_guarded_affine_unit_count_structural_proof",
                        ("schema_version", 1),
                        ("function", getattr(analysis, "function_name", None)),
                        ("acc_phi", self._pcode_op_stable_key(acc_phi)),
                        ("state_phi", self._pcode_op_stable_key(state_phi)),
                        ("progress_backedges", tuple(sorted(acc_progress_indices))),
                        ("nonprogress_backedges", tuple(sorted(acc_nonprogress_indices))),
                        ("conditional_progress_backedges", tuple(sorted(acc_conditional_progress_keys))),
                        ("conditional_progress_guard_keys", tuple(sorted(acc_conditional_progress_keys.items(), key=repr))),
                        ("target", tuple(condition.to_string() for condition in target_conditions or ())),
                        ("target_guard_keys", tuple(sorted((self._condition_identity_key(condition) for condition in target_conditions or ()), key=repr))),
                    )
        self._debug_print(
            "Outcome branch-guarded structural proof declined: "
            f"saw_acc_candidate={saw_acc_candidate}, "
            f"saw_acc_transition={saw_acc_transition}, "
            f"saw_state_transition={saw_state_transition}, "
            f"saw_state_guard={saw_state_guard}"
        )
        return None

    def _acc_phi_flows_to_return_origin_phi(
        self,
        acc_phi,
        return_origin_keys: Set[Tuple[Any, ...]],
        *,
        summarizer: StructuralRecurrenceSummarizer,
        high_function,
    ) -> bool:
        if acc_phi is None or not return_origin_keys:
            return False
        acc_phi_key = self._pcode_op_stable_key(acc_phi)
        if not isinstance(acc_phi_key, tuple):
            return False
        for block in summarizer._iter_basic_blocks(high_function):
            for op in summarizer._iter_block_ops(block):
                if getattr(op, "getMnemonic", lambda: None)() != "MULTIEQUAL":
                    continue
                op_key = self._pcode_op_stable_key(op)
                if op_key not in return_origin_keys:
                    continue
                if self._pcode_op_input_def_reaches_phi(
                    op,
                    acc_phi_key,
                    max_depth=8,
                ):
                    return True
                if self._return_origin_phi_has_acc_output_input(op, acc_phi):
                    return True
        return False

    def _return_origin_phi_has_acc_output_input(self, return_phi, acc_phi) -> bool:
        acc_output = getattr(acc_phi, "getOutput", lambda: None)()
        if acc_output is None:
            return False
        acc_parent = getattr(acc_phi, "getParent", lambda: None)()
        return_parent = getattr(return_phi, "getParent", lambda: None)()
        if acc_parent is None or return_parent is None:
            return False
        try:
            input_count = int(return_phi.getNumInputs())
        except Exception:
            input_count = 0
        for index in range(input_count):
            try:
                candidate = return_phi.getInput(index)
            except Exception:
                continue
            if not self._varnodes_same_storage(candidate, acc_output):
                continue
            try:
                predecessor = return_parent.getIn(index)
            except Exception:
                predecessor = None
            if predecessor is None:
                continue
            if self._block_debug_key(predecessor) != self._block_debug_key(acc_parent):
                continue
            return True
        return False

    def _varnodes_same_storage(self, left, right) -> bool:
        if left is None or right is None:
            return False
        try:
            left_addr = left.getAddress()
            right_addr = right.getAddress()
            left_space = left_addr.getAddressSpace().getName()
            right_space = right_addr.getAddressSpace().getName()
            return (
                left_space == right_space
                and int(left_addr.getOffset()) == int(right_addr.getOffset())
                and int(left.getSize()) == int(right.getSize())
            )
        except Exception:
            return False

    def _pcode_op_input_def_reaches_phi(
        self,
        op,
        target_phi_key: Tuple[Any, ...],
        *,
        max_depth: int,
    ) -> bool:
        seen: Set[int] = set()

        def visit_varnode(varnode, depth: int) -> bool:
            if varnode is None or depth > int(max_depth):
                return False
            marker = id(varnode)
            if marker in seen:
                return False
            seen.add(marker)
            try:
                def_op = varnode.getDef()
            except Exception:
                def_op = None
            if def_op is None:
                return False
            if self._pcode_op_stable_key(def_op) == target_phi_key:
                return True
            try:
                input_count = int(def_op.getNumInputs())
            except Exception:
                input_count = 0
            for index in range(input_count):
                try:
                    if visit_varnode(def_op.getInput(index), depth + 1):
                        return True
                except Exception:
                    continue
            return False

        try:
            input_count = int(op.getNumInputs())
        except Exception:
            input_count = 0
        for index in range(input_count):
            try:
                if visit_varnode(op.getInput(index), 0):
                    return True
            except Exception:
                continue
        return False

    def _pcode_op_stable_key(self, op) -> Optional[Tuple[Any, ...]]:
        op_ref = PcodeOpRef.from_pcode_op(
            op,
            binary_id=self._binary_id,
            program_uid=self._program_identity(),
            function_entry=self._current_function_entry_address(),
        )
        if op_ref is None:
            return None
        try:
            return op_ref.stable_key()
        except Exception:
            return None

    def _phi_circular_origin_stable_keys(self, expr: Optional[Expression]) -> Set[Tuple[Any, ...]]:
        keys: Set[Tuple[Any, ...]] = set()
        for node in _iter_expression_nodes(expr):
            if getattr(node, "expr_type", None) != ExpressionType.UNKNOWN:
                continue
            if not self._expression_contains_phi_circular_marker(node):
                continue
            runtime_ref = getattr(node, "runtime_ref", None)
            origin_ref = getattr(runtime_ref, "origin_ref", None)
            stable_key = getattr(origin_ref, "stable_key", None)
            if callable(stable_key):
                try:
                    key = stable_key()
                except Exception:
                    key = None
                if isinstance(key, tuple):
                    keys.add(key)
        return keys

    def _return_info_candidate_phi_origin_keys(self, ret: Optional[ReturnInfo]) -> Set[Tuple[Any, ...]]:
        if ret is None:
            return set()
        keys = set(self._phi_circular_origin_stable_keys(getattr(ret, "value", None)))
        keys.update(
            self._candidate_phi_origin_keys_from_summary_source_key(
                getattr(ret, "summary_candidate_source_key", None)
            )
        )
        return keys

    def _return_info_return_phi_origin_keys(self, ret: Optional[ReturnInfo]) -> Set[Tuple[Any, ...]]:
        if ret is None:
            return set()
        keys = set(self._phi_circular_origin_stable_keys(getattr(ret, "value", None)))
        keys.update(
            self._return_phi_origin_keys_from_summary_source_key(
                getattr(ret, "summary_candidate_source_key", None)
            )
        )
        return keys

    def _candidate_phi_origin_keys_from_summary_source_key(self, value) -> Set[Tuple[Any, ...]]:
        keys: Set[Tuple[Any, ...]] = set()
        if not isinstance(value, tuple):
            return keys
        for item in value:
            if (
                isinstance(item, tuple)
                and len(item) == 2
                and item[0] == "candidate_phi_origin_keys"
            ):
                raw_keys = item[1]
                for raw_key in tuple(raw_keys or ()):
                    if isinstance(raw_key, tuple):
                        keys.add(raw_key)
                continue
            if isinstance(item, tuple):
                keys.update(self._candidate_phi_origin_keys_from_summary_source_key(item))
        return keys

    def _return_phi_origin_keys_from_summary_source_key(self, value) -> Set[Tuple[Any, ...]]:
        keys: Set[Tuple[Any, ...]] = set()
        if not isinstance(value, tuple):
            return keys
        for item in value:
            if (
                isinstance(item, tuple)
                and len(item) == 2
                and item[0] == "return_phi_origin_keys"
            ):
                raw_keys = item[1]
                for raw_key in tuple(raw_keys or ()):
                    if isinstance(raw_key, tuple):
                        keys.add(raw_key)
                continue
            if isinstance(item, tuple):
                keys.update(self._return_phi_origin_keys_from_summary_source_key(item))
        return keys

    def _expression_is_placeholder_plus_one(
        self,
        expr: Optional[Expression],
        placeholder: Expression,
    ) -> bool:
        return self._expression_is_placeholder_plus_constant(expr, placeholder, 1)

    def _expression_is_placeholder_minus_one(
        self,
        expr: Optional[Expression],
        placeholder: Expression,
    ) -> bool:
        return self._expression_is_placeholder_plus_constant(expr, placeholder, -1)

    def _expression_is_placeholder_plus_one_under_conditions(
        self,
        expr: Optional[Expression],
        placeholder: Expression,
        conditions: Sequence[Condition],
    ) -> bool:
        if self._expression_is_placeholder_plus_one(expr, placeholder):
            return True
        if self._expression_is_placeholder_plus_unit_condition(expr, placeholder, conditions):
            return True
        expected = Expression.binary_op(
            "INT_ADD",
            placeholder,
            Expression.constant(1, size=max(1, int(getattr(placeholder, "size", 0) or 4))),
        )
        expected.size = max(1, int(getattr(placeholder, "size", 0) or 4))
        return self._expressions_equal_under_conditions_smt(
            expr,
            expected,
            tuple(conditions or ()),
            getattr(self, "_current_parameters", ()) or (),
        )

    def _expression_is_placeholder_minus_one_under_conditions(
        self,
        expr: Optional[Expression],
        placeholder: Expression,
        conditions: Sequence[Condition],
    ) -> bool:
        if self._expression_is_placeholder_minus_one(expr, placeholder):
            return True
        if self._expression_is_placeholder_minus_one_unit_condition(expr, placeholder, conditions):
            return True
        expected = Expression.binary_op(
            "INT_SUB",
            placeholder,
            Expression.constant(1, size=max(1, int(getattr(placeholder, "size", 0) or 4))),
        )
        expected.size = max(1, int(getattr(placeholder, "size", 0) or 4))
        return self._expressions_equal_under_conditions_smt(
            expr,
            expected,
            tuple(conditions or ()),
            getattr(self, "_current_parameters", ()) or (),
        )

    def _expression_is_placeholder_plus_zero_under_conditions(
        self,
        expr: Optional[Expression],
        placeholder: Expression,
        conditions: Sequence[Condition],
    ) -> bool:
        current = self._strip_transparent_unary(expr)
        if current is None or getattr(current, "expr_type", None) != ExpressionType.BINARY_OP:
            return False
        if getattr(current, "operator", None) not in {"INT_ADD", "INT_SUB"}:
            return False
        operands = tuple(getattr(current, "operands", ()) or ())
        if len(operands) != 2:
            return False
        left, right = operands
        if self._expressions_same_key(left, placeholder):
            delta = right
            if getattr(current, "operator", None) == "INT_ADD":
                return self._expression_is_zero_under_conditions(delta, conditions)
            return self._expression_is_zero_under_conditions(delta, conditions)
        if getattr(current, "operator", None) == "INT_ADD" and self._expressions_same_key(right, placeholder):
            return self._expression_is_zero_under_conditions(left, conditions)
        return False

    def _expression_is_zero_under_conditions(
        self,
        expr: Optional[Expression],
        conditions: Sequence[Condition],
    ) -> bool:
        if self._constant_int_value(expr) == 0:
            return True
        current = self._strip_transparent_unary(expr)
        if current is None or getattr(current, "expr_type", None) != ExpressionType.BINARY_OP:
            return False
        as_condition = Condition(current, False)
        if self._conditions_imply(tuple(conditions or ()), (as_condition.negate(),)):
            return True
        operator = getattr(current, "operator", None)
        operands = tuple(getattr(current, "operands", ()) or ())
        if len(operands) != 2:
            return False
        if operator == "INT_SLESS":
            left, right = operands
            if self._constant_int_value(right) == 1 and getattr(left, "expr_type", None) == ExpressionType.PARAMETER:
                if any(
                    self._condition_is_signed_positive_of_param(condition, left)
                    for condition in conditions or ()
                ):
                    return True
        if operator == "INT_SUB":
            left, right = operands
            if self._expression_is_one_under_conditions(left, conditions) and self._constant_int_value(right) == 1:
                return True
        return self._expressions_equal_under_conditions_smt(
            current,
            Expression.constant(0, size=max(1, int(getattr(current, "size", 0) or 4))),
            tuple(conditions or ()),
            getattr(self, "_current_parameters", ()) or (),
        )

    def _expression_is_placeholder_minus_one_unit_condition(
        self,
        expr: Optional[Expression],
        placeholder: Expression,
        conditions: Sequence[Condition],
    ) -> bool:
        return self._placeholder_minus_one_unit_condition_guard_key(expr, placeholder, conditions) is not None

    def _placeholder_minus_one_unit_condition_guard_key(
        self,
        expr: Optional[Expression],
        placeholder: Expression,
        conditions: Sequence[Condition],
    ) -> Optional[Tuple[Any, ...]]:
        current = self._strip_transparent_unary(expr)
        if current is None or getattr(current, "expr_type", None) != ExpressionType.BINARY_OP:
            return None
        if getattr(current, "operator", None) == "INT_ADD":
            operands = tuple(getattr(current, "operands", ()) or ())
            if len(operands) != 2:
                return None
            left, right = operands
            if self._expressions_same_key(left, placeholder):
                return self._negated_unit_condition_key_for_expression(right, conditions)
            if self._expressions_same_key(right, placeholder):
                return self._negated_unit_condition_key_for_expression(left, conditions)
            return None
        if getattr(current, "operator", None) != "INT_SUB":
            return None
        operands = tuple(getattr(current, "operands", ()) or ())
        if len(operands) != 2:
            return None
        if not self._expressions_same_key(operands[0], placeholder):
            return None
        return (
            self._unit_condition_key_for_expression(operands[1], conditions)
            or self._negated_unit_condition_key_for_expression(operands[1], conditions)
        )

    def _expression_is_placeholder_plus_unit_condition(
        self,
        expr: Optional[Expression],
        placeholder: Expression,
        conditions: Sequence[Condition],
    ) -> bool:
        return self._placeholder_plus_unit_condition_guard_key(expr, placeholder, conditions) is not None

    def _placeholder_plus_unit_condition_guard_key(
        self,
        expr: Optional[Expression],
        placeholder: Expression,
        conditions: Sequence[Condition],
    ) -> Optional[Tuple[Any, ...]]:
        current = self._strip_transparent_unary(expr)
        if current is None or getattr(current, "expr_type", None) != ExpressionType.BINARY_OP:
            return None
        if getattr(current, "operator", None) != "INT_ADD":
            return None
        operands = tuple(getattr(current, "operands", ()) or ())
        if len(operands) != 2:
            return None
        left, right = operands
        if self._expressions_same_key(left, placeholder):
            return self._unit_condition_key_for_expression(right, conditions)
        if self._expressions_same_key(right, placeholder):
            return self._unit_condition_key_for_expression(left, conditions)
        return None

    def _unit_condition_key_for_expression(
        self,
        expr: Optional[Expression],
        conditions: Sequence[Condition],
    ) -> Optional[Tuple[Any, ...]]:
        current = self._strip_transparent_unary(expr)
        if current is None:
            return None
        for condition in conditions or ():
            if condition is None:
                continue
            if self._expression_is_one_under_conditions(current, (condition,)):
                return self._condition_identity_key(condition)
        return None

    def _negated_unit_condition_key_for_expression(
        self,
        expr: Optional[Expression],
        conditions: Sequence[Condition],
    ) -> Optional[Tuple[Any, ...]]:
        current = self._strip_transparent_unary(expr)
        if current is None or getattr(current, "expr_type", None) != ExpressionType.BINARY_OP:
            return None
        if getattr(current, "operator", None) != "INT_SUB":
            return None
        operands = tuple(getattr(current, "operands", ()) or ())
        if len(operands) != 2 or self._constant_int_value(operands[1]) != 1:
            return None
        flag_expr = self._strip_transparent_unary(operands[0])
        if flag_expr is None:
            return None
        for condition in conditions or ():
            if condition is None:
                continue
            if self._expression_is_zero_under_conditions(flag_expr, (condition,)) and self._expression_is_one_under_conditions(
                flag_expr,
                (condition.negate(),),
            ):
                return self._condition_identity_key(condition)
        return None

    @staticmethod
    def _strip_transparent_unary(expr: Optional[Expression]) -> Optional[Expression]:
        current = expr
        while (
            current is not None
            and getattr(current, "expr_type", None) == ExpressionType.UNARY_OP
            and getattr(current, "operator", None) in {"COPY", "CAST", "SUBPIECE", "INT_ZEXT", "INT_SEXT"}
            and len(tuple(getattr(current, "operands", ()) or ())) == 1
        ):
            current = tuple(getattr(current, "operands", ()) or ())[0]
        return current

    def _expression_is_placeholder_plus_constant(
        self,
        expr: Optional[Expression],
        placeholder: Expression,
        constant: int,
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
        operands = tuple(getattr(current, "operands", ()) or ())
        if len(operands) != 2:
            return False
        operator = getattr(current, "operator", None)
        left, right = operands
        if operator == "INT_ADD":
            if self._expressions_same_key(left, placeholder) and self._constant_int_value(right) == constant:
                return True
            if self._expressions_same_key(right, placeholder) and self._constant_int_value(left) == constant:
                return True
            wrapped = self._constant_int_value(right)
            if self._expressions_same_key(left, placeholder) and wrapped is not None:
                return self._signed_unit_constant_matches(wrapped, constant, getattr(current, "size", None))
        if operator == "INT_SUB":
            if self._expressions_same_key(left, placeholder) and self._constant_int_value(right) == -constant:
                return True
        return False

    def _signed_unit_constant_matches(self, value: int, expected: int, size: Optional[int]) -> bool:
        if value == expected:
            return True
        bits = max(1, int(size or 4)) * 8
        mask = (1 << bits) - 1
        return (int(value) & mask) == (int(expected) & mask)

    def _expressions_same_key(self, left: Optional[Expression], right: Optional[Expression]) -> bool:
        if left is None or right is None:
            return False
        try:
            return left.structural_key() == right.structural_key()
        except Exception:
            return False

    def _state_phi_feeds_positive_loop_guard(
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
        header_key = self._block_debug_key(header_block)
        for block in candidate_blocks:
            cbranch = summarizer._find_cbranch_op(block)
            if cbranch is None or summarizer._safe_pcode_input_count(cbranch) < 2:
                continue
            if block is not header_block:
                successor_keys = {self._block_debug_key(successor) for successor in self._block_successors(block)}
                if header_key not in successor_keys:
                    continue
            guard_expr = summarizer._build_pcode_expression(
                cbranch.getInput(1),
                placeholders={state_output: state_placeholder},
            )
            if guard_expr is None:
                continue
            if self._expressions_same_key(
                summarizer._canonicalize_expression(guard_expr),
                summarizer._canonicalize_expression(positive_guard),
            ):
                return True
            if allow_latch_progress_guard and self._expression_is_positive_after_unit_progress_guard(
                guard_expr,
                state_placeholder,
                target_conditions,
            ):
                return True
        return False

    def _expression_is_positive_after_unit_progress_guard(
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
        if len(operands) != 2 or self._constant_int_value(operands[0]) != 0:
            return False
        right = operands[1]
        if self._expression_is_placeholder_minus_one_under_conditions(
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
        return self._expressions_same_key(right_operands[0], state_placeholder) and self._expression_is_one_under_conditions(
            right_operands[1],
            conditions,
        )

    def _branch_guarded_affine_ignored_artifacts_are_shadowed(
        self,
        ignored_artifacts: Sequence[ReturnInfo],
        recursive_returns: Sequence[Tuple[ReturnInfo, int]],
        parameters: Sequence[Dict],
    ) -> bool:
        if not ignored_artifacts:
            return True
        for artifact in ignored_artifacts:
            artifact_conditions = tuple(getattr(artifact, "conditions", ()) or ())
            artifact_site = self._return_site_key(artifact)
            if not any(
                artifact_site == self._return_site_key(recursive)
                and (
                    self._condition_lists_equivalent(
                        list(artifact_conditions),
                        list(getattr(recursive, "conditions", ()) or ()),
                    )
                    or (
                        self._conditions_imply(
                            artifact_conditions,
                            tuple(getattr(recursive, "conditions", ()) or ()),
                        )
                        and self._conditions_imply(
                            tuple(getattr(recursive, "conditions", ()) or ()),
                            artifact_conditions,
                        )
                    )
                )
                and self._expressions_equal_under_conditions_smt(
                    getattr(artifact, "value", None),
                    getattr(recursive, "value", None),
                    tuple(artifact_conditions) + tuple(getattr(recursive, "conditions", ()) or ()),
                    parameters,
                )
                for recursive, _step in recursive_returns
            ):
                return False
        return True

    def _branch_guarded_affine_phi_step(self, value: Optional[Expression]) -> Optional[int]:
        signature = self._phi_circular_additive_signature(value)
        if signature is None:
            return None
        phi_coeff, constant = signature
        if phi_coeff != 1:
            return None
        try:
            return int(constant)
        except (TypeError, ValueError):
            return None

    def _phi_circular_additive_signature(self, expr: Optional[Expression]) -> Optional[Tuple[int, int]]:
        if expr is None:
            return None
        if self._expression_contains_phi_circular_marker(expr):
            if getattr(expr, "expr_type", None) == ExpressionType.UNKNOWN:
                return (1, 0)
        expr_type = getattr(expr, "expr_type", None)
        if expr_type == ExpressionType.CONSTANT:
            value = self._constant_int_value(expr)
            if value is None:
                return None
            return (0, int(value))
        if expr_type == ExpressionType.UNARY_OP and getattr(expr, "operator", None) in {"COPY", "CAST", "SUBPIECE", "INT_ZEXT", "INT_SEXT"}:
            operands = tuple(getattr(expr, "operands", ()) or ())
            if len(operands) != 1:
                return None
            return self._phi_circular_additive_signature(operands[0])
        if expr_type != ExpressionType.BINARY_OP:
            return None
        operands = tuple(getattr(expr, "operands", ()) or ())
        if len(operands) != 2:
            return None
        left = self._phi_circular_additive_signature(operands[0])
        right = self._phi_circular_additive_signature(operands[1])
        if left is None or right is None:
            return None
        operator = getattr(expr, "operator", None)
        if operator == "INT_ADD":
            return (left[0] + right[0], left[1] + right[1])
        if operator == "INT_SUB":
            return (left[0] - right[0], left[1] - right[1])
        return None

    def _branch_guarded_affine_singleton_base_anchor_matches(
        self,
        value: Optional[Expression],
        conditions: Sequence[Condition],
        c_param: Expression,
        target_conditions: Sequence[Condition],
    ) -> bool:
        if self._constant_int_value(value) != 1:
            return False
        if not self._conditions_overlap(tuple(conditions or ()), target_conditions):
            return False
        return any(
            self._condition_is_param_minus_one_nonpositive(condition, c_param, target_conditions)
            for condition in conditions or ()
        )

    def _condition_is_param_minus_one_nonpositive(
        self,
        condition: Condition,
        param: Expression,
        target_conditions: Sequence[Condition] = (),
    ) -> bool:
        if condition is None:
            return False
        expr = getattr(condition, "expression", None)
        if expr is None or getattr(expr, "expr_type", None) != ExpressionType.BINARY_OP:
            return False
        operands = tuple(getattr(expr, "operands", ()) or ())
        if len(operands) != 2:
            return False
        operator = getattr(expr, "operator", None)
        if operator == "INT_SLESSEQUAL" and not getattr(condition, "negated", False):
            return self._branch_guarded_expression_is_param_minus_one(operands[0], param, target_conditions) and self._constant_int_value(operands[1]) == 0
        if operator == "INT_SLESS" and getattr(condition, "negated", False):
            return self._constant_int_value(operands[0]) == 0 and self._branch_guarded_expression_is_param_minus_one(operands[1], param, target_conditions)
        return False

    def _branch_guarded_expression_is_param_minus_one(
        self,
        expr: Optional[Expression],
        param: Expression,
        target_conditions: Sequence[Condition],
    ) -> bool:
        if expr is None or getattr(expr, "expr_type", None) != ExpressionType.BINARY_OP:
            return False
        if self._expressions_equal_under_conditions_smt(
            expr,
            Expression.binary_op(
                "INT_SUB",
                param,
                Expression.constant(1, size=max(1, int(getattr(param, "size", 0) or 4))),
            ),
            tuple(target_conditions or ()),
            getattr(self, "_current_parameters", ()) or (),
        ):
            return True
        if getattr(expr, "operator", None) == "INT_ADD":
            operands = tuple(getattr(expr, "operands", ()) or ())
            if len(operands) != 2:
                return False
            left, right = operands
            if self._expression_is_same_parameter_ignoring_subpiece(left, param):
                return self._expression_is_placeholder_minus_one_under_conditions(expr, left, target_conditions)
            if self._expression_is_same_parameter_ignoring_subpiece(right, param):
                return self._expression_is_placeholder_minus_one_under_conditions(expr, right, target_conditions)
            return False
        if getattr(expr, "operator", None) != "INT_SUB":
            return False
        operands = tuple(getattr(expr, "operands", ()) or ())
        if len(operands) != 2:
            return False
        return self._expression_is_same_parameter_ignoring_subpiece(
            operands[0],
            param,
        ) and self._expression_is_one_under_conditions(operands[1], target_conditions)

    def _expression_is_one_under_conditions(
        self,
        expr: Optional[Expression],
        target_conditions: Sequence[Condition],
    ) -> bool:
        if self._constant_int_value(expr) == 1:
            return True
        current = expr
        while (
            current is not None
            and getattr(current, "expr_type", None) == ExpressionType.UNARY_OP
            and getattr(current, "operator", None) in {"INT_ZEXT", "INT_SEXT", "CAST", "COPY"}
            and len(tuple(getattr(current, "operands", ()) or ())) == 1
        ):
            current = tuple(getattr(current, "operands", ()) or ())[0]
        if current is None:
            return False
        if getattr(current, "expr_type", None) != ExpressionType.BINARY_OP:
            return False
        if getattr(current, "operator", None) == "INT_SLESS":
            operands = tuple(getattr(current, "operands", ()) or ())
            if (
                len(operands) == 2
                and self._constant_int_value(operands[1]) == 1
                and getattr(operands[0], "expr_type", None) == ExpressionType.PARAMETER
                and any(
                    self._condition_is_signed_nonpositive_of_param(condition, operands[0])
                    for condition in target_conditions or ()
                )
            ):
                return True
        as_condition = Condition(current, False)
        if any(
            existing is not None
            and (
                existing.equals(as_condition)
                or ConditionNormalizer.are_equivalent(existing, as_condition)
            )
            for existing in target_conditions or ()
        ):
            return True
        return self._conditions_imply(tuple(target_conditions or ()), (as_condition,))

    def _return_conditions_cover_region(
        self,
        region_conditions: Sequence[Condition],
        returns: Sequence[ReturnInfo],
    ) -> bool:
        if any(
            self._condition_lists_equivalent(
                list(region_conditions or ()),
                list(getattr(ret, "conditions", ()) or ()),
            )
            or (
                self._conditions_imply(region_conditions, tuple(getattr(ret, "conditions", ()) or ()))
                and self._conditions_imply(tuple(getattr(ret, "conditions", ()) or ()), region_conditions)
            )
            for ret in returns or ()
        ):
            return True
        guard_exprs: List[Expression] = []
        for ret in returns or ():
            guard = Condition.combine_and(list(getattr(ret, "conditions", ()) or ()))
            if guard is None:
                return True
            guard_exprs.append(
                Expression.unary_op("BOOL_NEGATE", guard.expression)
                if guard.negated
                else guard.expression
            )
        if not guard_exprs:
            return False
        disjunction = guard_exprs[0]
        for expr in guard_exprs[1:]:
            disjunction = Expression.binary_op("BOOL_OR", disjunction, expr)
        return self._conditions_are_unsat(tuple(region_conditions or ()) + (Condition(disjunction, True),))

    def _conditions_overlap(
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
                    left_condition.equals(right_condition.negate())
                    or ConditionNormalizer.are_equivalent(left_condition, right_condition.negate())
                    or left_condition.negate().equals(right_condition)
                    or ConditionNormalizer.are_equivalent(left_condition.negate(), right_condition)
                ):
                    return False
        try:
            return ConditionSMTOracle.conjunction_is_unsat(list(left or ()) + list(right or ())) is not True
        except Exception:
            return False

    def _conditions_imply(
        self,
        left: Sequence[Condition],
        right: Sequence[Condition],
    ) -> bool:
        for condition in right or ():
            if any(
                existing is not None
                and (
                    existing.equals(condition)
                    or ConditionNormalizer.are_equivalent(existing, condition)
                )
                for existing in left or ()
            ):
                continue
            try:
                if ConditionSMTOracle.conjunction_is_unsat(list(left or ()) + [condition.negate()]) is not True:
                    return False
            except Exception:
                return False
        return True

    def _expressions_equal_under_conditions_smt(
        self,
        left: Optional[Expression],
        right: Optional[Expression],
        conditions: Sequence[Condition],
        parameters: Sequence[Dict],
    ) -> bool:
        if _expressions_equivalent_under_conditions(left, right, conditions, parameters):
            return True
        if left is None or right is None:
            return False
        equality = Condition(Expression.binary_op("INT_NOTEQUAL", left, right), False)
        try:
            return ConditionSMTOracle.conjunction_is_unsat(list(conditions or ()) + [equality]) is True
        except Exception:
            return False

    def _prove_branch_guarded_while_nonprogress_must_diverge(
        self,
        high_function,
        *,
        invariant_conditions: Sequence[Condition],
    ) -> Optional[Dict[str, Any]]:
        if high_function is None:
            return None
        blocks = tuple(self._iter_high_basic_blocks(high_function))
        if not blocks:
            return None
        tracer = None
        if self.program is not None:
            try:
                tracer = self._make_tracer(high_function)
            except Exception:
                tracer = None

        adjacency: Dict[Any, List[Any]] = {}
        excluded_edges: List[Dict[str, Any]] = []
        for block in blocks:
            block_key = self._block_debug_key(block)
            adjacency[block_key] = []
            for successor in self._block_successors(block):
                successor_key = self._block_debug_key(successor)
                edge_condition = self._edge_condition_for_successor(block, successor, tracer)
                if edge_condition is not None and self._condition_contradicts_any(
                    edge_condition,
                    tuple(invariant_conditions or ()),
                ):
                    excluded_edges.append(
                        {
                            "source": block_key,
                            "target": successor_key,
                            "edge_condition": edge_condition.to_string(),
                            "relation": "invariant_contradicts_edge",
                        }
                    )
                    continue
                adjacency[block_key].append(successor_key)

        key_to_block = {self._block_debug_key(block): block for block in blocks}
        entry_keys = [
            self._block_debug_key(block)
            for block in blocks
            if self._block_predecessor_count(block) == 0
        ]
        if not entry_keys:
            entry_keys = [self._block_debug_key(blocks[0])]

        reachable: Set[Any] = set()
        stack = list(entry_keys)
        while stack:
            key = stack.pop()
            if key in reachable or key not in key_to_block:
                continue
            reachable.add(key)
            stack.extend(adjacency.get(key, ()))
        if not reachable:
            return None
        if not excluded_edges:
            self._debug_print("Outcome branch-guarded divergence proof declined: no invariant-excluding guard edges")
            return None
        for key in reachable:
            block = key_to_block.get(key)
            if block is None:
                return None
            if self._block_has_return_op(block):
                self._debug_print("Outcome branch-guarded divergence proof declined: reachable RETURN under invariant")
                return None
            if self._block_writes_outcome_guard_state(block):
                self._debug_print("Outcome branch-guarded divergence proof declined: reachable guard-state write under invariant")
                return None
            if not adjacency.get(key):
                self._debug_print("Outcome branch-guarded divergence proof declined: reachable terminal block under invariant")
                return None
        cycle_keys = self._reachable_cycle_keys(reachable, adjacency)
        if not cycle_keys:
            self._debug_print("Outcome branch-guarded divergence proof declined: no feasible invariant cycle")
            return None
        reachable_blocks = {
            key_to_block[key]
            for key in reachable
            if key in key_to_block
        }
        if not reachable_blocks or not self._scc_preserves_guard_dependencies(reachable_blocks):
            self._debug_print("Outcome branch-guarded divergence proof declined: reachable graph redefines guard dependency")
            return None
        cycle_blocks = {
            key_to_block[key]
            for key in cycle_keys
            if key in key_to_block
        }
        if not cycle_blocks or not self._scc_preserves_guard_dependencies(cycle_blocks):
            self._debug_print("Outcome branch-guarded divergence proof declined: cycle redefines guard dependency")
            return None
        return {
            "proof_kind": "branch_guarded_while_nonprogress_must_diverge",
            "candidate_rule": "branch_guarded_loop_invariant_nonprogress",
            "invariant": [condition.to_string() for condition in invariant_conditions or ()],
            "reachable_blocks": sorted(str(key) for key in reachable),
            "cycle_blocks": sorted(str(key) for key in cycle_keys),
            "excluded_edges": excluded_edges,
            "side_effect_control_safety": {
                "forbidden_ops_absent": True,
                "return_ops_absent_under_invariant": True,
                "guard_state_writes_absent_under_invariant": True,
                "guard_dependency_writes_absent_under_invariant": True,
            },
        }

    def _reachable_cycle_keys(
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

    def _condition_contradicts_any(
        self,
        condition: Condition,
        others: Sequence[Condition],
    ) -> bool:
        if condition is None:
            return False
        for other in others or ():
            if other is None:
                continue
            try:
                if (
                    condition.equals(other.negate())
                    or condition.negate().equals(other)
                    or ConditionNormalizer.are_equivalent(condition, other.negate())
                    or ConditionNormalizer.are_equivalent(condition.negate(), other)
                ):
                    return True
            except Exception:
                continue
        try:
            return ConditionSMTOracle.conjunction_is_unsat(list(others or ()) + [condition]) is True
        except Exception:
            return False

    def _return_info_summary_identity_key(self, ret: ReturnInfo) -> Tuple[Any, ...]:
        return (
            "return_info",
            self._return_site_key(ret),
            tuple(
                getattr(condition, "structural_key", lambda: ("condition", condition.to_string()))()
                for condition in tuple(getattr(ret, "conditions", ()) or ())
            ),
            expression_key_safe(getattr(ret, "value", None)),
        )

    def _try_apply_triangular_mod_optimized_outcomes(
        self,
        high_function,
        analysis: FunctionReturnAnalysis,
    ) -> bool:
        if len(getattr(analysis, "parameters", []) or []) != 1:
            self._debug_print("Outcome optimized triangular summary declined: expected one parameter")
            return False
        if getattr(analysis, "deferred_calls", None):
            self._debug_print("Outcome optimized triangular summary declined: deferred calls present")
            return False
        if len(getattr(analysis, "returns", []) or []) != 2:
            self._debug_print("Outcome optimized triangular summary declined: expected two returns")
            return False
        if self._high_function_has_forbidden_control_outcome_ops(high_function, allow_call=False):
            self._debug_print("Outcome optimized triangular summary declined: forbidden control/effect op present")
            return False
        param = self._parameter_expression(analysis, 0)
        if param is None:
            self._debug_print("Outcome optimized triangular summary declined: parameter expression unavailable")
            return False
        return_size = self._analysis_return_size_bytes(analysis)
        zero_ret = None
        one_ret = None
        for ret in analysis.returns:
            if self._constant_int_value(ret.value) == 0:
                zero_ret = ret
            elif (
                self._expression_is_same_parameter_ignoring_subpiece(ret.value, param)
                or self._constant_int_value(ret.value) == 1
            ):
                one_ret = ret
        if zero_ret is None or one_ret is None:
            self._debug_print("Outcome optimized triangular summary declined: zero/one return partition not recognized")
            return False
        nonpositive = self._signed_positive_condition(param).negate()
        eq_one = Condition(
            Expression.binary_op(
                "INT_EQUAL",
                param,
                Expression.constant(1, max(1, int(param.size or return_size or 4))),
            ),
            False,
        )
        if not (
            self._conditions_equivalent(zero_ret.conditions, [nonpositive])
            or (
                len(zero_ret.conditions or ()) == 1
                and (
                    self._condition_is_signed_nonpositive_of_param(zero_ret.conditions[0], param)
                    or self._condition_is_signed_less_than_one_of_param(zero_ret.conditions[0], param)
                )
            )
        ):
            self._debug_print("Outcome optimized triangular summary declined: zero return guard is not param nonpositive")
            return False
        if not (
            self._conditions_equivalent(one_ret.conditions, [eq_one])
            or any(
                self._condition_is_param_equal_const(condition, param, 1)
                for condition in (one_ret.conditions or ())
            )
        ):
            self._debug_print("Outcome optimized triangular summary declined: one return guard is not param eq one")
            return False

        analysis.return_outcomes = (
            ReturnOutcome(guard=tuple(zero_ret.conditions), value=zero_ret.value, provenance={"source": "optimized_triangular_mod_partition"}, return_info=zero_ret),
            ReturnOutcome(guard=tuple(one_ret.conditions), value=one_ret.value, provenance={"source": "optimized_triangular_mod_partition"}, return_info=one_ret),
        )
        analysis.divergence_outcomes = ()
        analysis.unknown_outcomes = (
            UnknownOutcome(
                guard=(self._return_partition_miss_guard([zero_ret, one_ret]),),
                reason="optimized_missing_region_proof_missing",
                evidence={
                    "candidate_rule": "optimized_triangular_mod_missing_region",
                    "forbidden_ops_absent": True,
                    "nonreturning_region_candidate": self._high_function_has_nonreturning_region_candidate(high_function),
                    "return_partition": "param_nonpositive_or_param_eq_one",
                    "missing_proof": "object_level_nonreturning_region_or_positive_region_resolution",
                },
            ),
        )
        if "outcome_partition_unknown_optimized_triangular_mod" not in analysis.analysis_notes:
            analysis.analysis_notes.append("outcome_partition_unknown_optimized_triangular_mod")
        return True

    def _return_partition_miss_guard(self, returns: Sequence[ReturnInfo]) -> Condition:
        miss_terms = []
        for ret in returns or ():
            guard = Condition.combine_and(list(ret.conditions or ()))
            if guard is None:
                return Condition(Expression.constant(0, 1), False)
            miss_terms.append(
                guard.expression
                if guard.negated
                else Expression.unary_op("BOOL_NEGATE", guard.expression)
            )
        if not miss_terms:
            return Condition(Expression.constant(1, 1), False)
        expr = miss_terms[0]
        for term in miss_terms[1:]:
            expr = Expression.binary_op("BOOL_AND", expr, term)
        return Condition(expr, False)

    def _parameter_expression(
        self,
        analysis: FunctionReturnAnalysis,
        index: int,
    ) -> Optional[Expression]:
        params = list(getattr(analysis, "parameters", []) or [])
        if index < 0 or index >= len(params):
            return None
        param = dict(params[index] or {})
        size = int(param.get("size", 0) or 4)
        return Expression.parameter(
            str(param.get("name") or f"param_{index + 1}"),
            index=index,
            data_type=param.get("data_type"),
            data_type_obj=param.get("data_type_obj"),
            size=max(1, size),
        )

    def _signed_positive_condition(self, expr: Expression) -> Condition:
        zero = Expression.constant(0, max(1, int(expr.size or 4)))
        return Condition(Expression.binary_op("INT_SLESS", zero, expr), False)

    def _condition_is_signed_nonpositive_of_param(self, condition: Condition, param: Expression) -> bool:
        if condition is None or not getattr(condition, "negated", False):
            return False
        expr = getattr(condition, "expression", None)
        if expr is None or expr.expr_type != ExpressionType.BINARY_OP or expr.operator != "INT_SLESS":
            return False
        operands = list(getattr(expr, "operands", None) or ())
        if len(operands) != 2:
            return False
        left, right = operands
        return self._constant_int_value(left) == 0 and self._expression_is_same_parameter_ignoring_subpiece(right, param)

    def _condition_is_signed_positive_of_param(self, condition: Condition, param: Expression) -> bool:
        if condition is None or getattr(condition, "negated", False):
            return False
        expr = getattr(condition, "expression", None)
        if expr is None or expr.expr_type != ExpressionType.BINARY_OP or expr.operator != "INT_SLESS":
            return False
        operands = list(getattr(expr, "operands", None) or ())
        if len(operands) != 2:
            return False
        left, right = operands
        return self._constant_int_value(left) == 0 and self._expression_is_same_parameter_ignoring_subpiece(right, param)

    def _condition_is_signed_less_than_one_of_param(self, condition: Condition, param: Expression) -> bool:
        if condition is None or getattr(condition, "negated", False):
            return False
        expr = getattr(condition, "expression", None)
        if expr is None or expr.expr_type != ExpressionType.BINARY_OP or expr.operator != "INT_SLESS":
            return False
        operands = list(getattr(expr, "operands", None) or ())
        if len(operands) != 2:
            return False
        left, right = operands
        return self._expression_is_same_parameter_ignoring_subpiece(left, param) and self._constant_int_value(right) == 1

    def _condition_is_param_equal_const(self, condition: Condition, param: Expression, value: int) -> bool:
        if condition is None:
            return False
        expr = getattr(condition, "expression", None)
        if expr is None or expr.expr_type != ExpressionType.BINARY_OP:
            return False
        operator = getattr(expr, "operator", None)
        negated = bool(getattr(condition, "negated", False))
        if operator == "INT_NOTEQUAL" and negated:
            pass
        elif operator == "INT_EQUAL" and not negated:
            pass
        else:
            return False
        operands = list(getattr(expr, "operands", None) or ())
        if len(operands) != 2:
            return False
        left, right = operands
        if (
            self._expression_is_same_parameter_ignoring_subpiece(left, param)
        ) and self._constant_int_value(right) == value:
            return True
        if (
            self._expression_is_same_parameter_ignoring_subpiece(right, param)
        ) and self._constant_int_value(left) == value:
            return True
        return False

    def _analysis_return_size_bytes(self, analysis: FunctionReturnAnalysis) -> int:
        for ret in getattr(analysis, "returns", []) or []:
            size = int(getattr(ret.value, "size", 0) or 0)
            if size > 0:
                return size
        surface = analysis.get_comparison_surface()
        bits = int(getattr(surface, "explicit_bit_width", 0) or 0)
        if bits > 0:
            return max(1, (bits + 7) // 8)
        return 4

    def _make_synthetic_outcome_return(
        self,
        analysis: FunctionReturnAnalysis,
        *,
        value: Expression,
        conditions: Sequence[Condition],
        branch_index: int,
        tag: str,
    ) -> ReturnInfo:
        return ReturnInfo(
            address=str(getattr(analysis, "entry_point", None) or "outcome-summary"),
            value=value,
            conditions=list(conditions),
            branch_index=branch_index,
            return_kind="outcome_summary",
            acceptance_status="accepted",
            summary_candidate_id=("outcome_partition", tag, getattr(analysis, "function_name", None)),
        )

    def _coerce_expression_size(self, expr: Expression, size: int) -> Expression:
        if int(getattr(expr, "size", 0) or 0) == int(size or 0):
            return expr
        return expr.clone_with(size=max(1, int(size or getattr(expr, "size", 0) or 4)))

    def _expression_is_param_minus_one(self, expr: Expression, param: Expression) -> bool:
        if expr is None or expr.expr_type != ExpressionType.BINARY_OP or expr.operator not in {"INT_ADD", "INT_SUB"}:
            return False
        if len(expr.operands or ()) != 2:
            return False
        left, right = expr.operands
        if not self._expression_is_same_parameter(left, param):
            return False
        if right.expr_type != ExpressionType.CONSTANT:
            return False
        try:
            value = int(right.value)
        except (TypeError, ValueError):
            return False
        bits = max(1, int(getattr(left, "size", 0) or getattr(expr, "size", 0) or 4)) * 8
        mask = (1 << bits) - 1
        if expr.operator == "INT_SUB":
            return value == 1
        return (value & mask) == mask

    def _expression_is_same_parameter(self, expr: Expression, param: Expression) -> bool:
        if expr is None or param is None:
            return False
        if expr.expr_type != ExpressionType.PARAMETER or param.expr_type != ExpressionType.PARAMETER:
            return False
        expr_index = getattr(expr, "value", None)
        param_index = getattr(param, "value", None)
        if isinstance(expr_index, int) and isinstance(param_index, int) and expr_index >= 0 and param_index >= 0:
            return expr_index == param_index
        return (getattr(expr, "name", None) or "") == (getattr(param, "name", None) or "")

    def _expression_is_same_parameter_ignoring_subpiece(self, expr: Expression, param: Expression) -> bool:
        current = expr
        if (
            current is not None
            and current.expr_type == ExpressionType.BINARY_OP
            and current.operator == "SUBPIECE"
            and current.operands
        ):
            current = current.operands[0]
        return self._expression_is_same_parameter(current, param)

    def _expression_contains_phi_circular(self, expr: Optional[Expression]) -> bool:
        if expr is None:
            return False
        if expr.expr_type == ExpressionType.UNKNOWN and "phi_circular" in str(getattr(expr, "value", "")):
            return True
        runtime_ref = getattr(expr, "runtime_ref", None)
        if getattr(runtime_ref, "reason", None) == "phi_circular" or getattr(runtime_ref, "kind", None) == "phi_circular":
            return True
        return any(self._expression_contains_phi_circular(operand) for operand in getattr(expr, "operands", []) or [])

    def _conditions_equivalent(
        self,
        left: Sequence[Condition],
        right: Sequence[Condition],
    ) -> bool:
        left_conditions = tuple(left or ())
        right_conditions = tuple(right or ())
        left_implies_right = ConditionSMTOracle.conjunction_is_unsat(
            list(left_conditions) + [condition.negate() for condition in right_conditions]
        )
        right_implies_left = ConditionSMTOracle.conjunction_is_unsat(
            list(right_conditions) + [condition.negate() for condition in left_conditions]
        )
        return left_implies_right is True and right_implies_left is True

    def _high_function_has_forbidden_control_outcome_ops(self, high_function, *, allow_call: bool) -> bool:
        forbidden = {"CALLIND", "BRANCHIND", "LOAD", "STORE", "CALLOTHER"}
        if not allow_call:
            forbidden.add("CALL")
        for block in self._iter_high_basic_blocks(high_function):
            for op in self._iter_high_block_ops(block):
                mnemonic = getattr(op, "getMnemonic", lambda: None)()
                if mnemonic in forbidden or self._is_control_outcome_forbidden_fp_mnemonic(mnemonic):
                    return True
        return False

    def _is_control_outcome_forbidden_fp_mnemonic(self, mnemonic: Optional[str]) -> bool:
        if not mnemonic:
            return False
        return (
            mnemonic.startswith("FLOAT_")
            or mnemonic in {"INT2FLOAT", "FLOAT2FLOAT", "TRUNC", "CEIL", "FLOOR", "ROUND", "NAN"}
        )

    def _high_function_has_cfg_cycle(self, high_function) -> bool:
        blocks = list(self._iter_high_basic_blocks(high_function))
        block_keys = {self._block_debug_key(block) for block in blocks}
        visiting: Set[Any] = set()
        visited: Set[Any] = set()

        def visit(block) -> bool:
            key = self._block_debug_key(block)
            if key in visiting:
                return True
            if key in visited:
                return False
            visiting.add(key)
            for succ in self._block_successors(block):
                if self._block_debug_key(succ) not in block_keys:
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

    def _high_function_has_nonreturning_region_candidate(self, high_function) -> bool:
        if self._high_function_has_cfg_cycle(high_function):
            return True
        for block in self._iter_high_basic_blocks(high_function):
            out_size = int(getattr(block, "getOutSize", lambda: 0)() or 0)
            if out_size != 0:
                continue
            has_return = any(
                getattr(op, "getMnemonic", lambda: None)() == "RETURN"
                for op in self._iter_high_block_ops(block)
            )
            if not has_return:
                return True
        return False

    def _block_reaches(self, start, target, allowed: Set[Any]) -> bool:
        stack = [start]
        seen = set()
        while stack:
            current = stack.pop()
            if current in seen:
                continue
            seen.add(current)
            if current is target:
                return True
            out_size = int(getattr(current, "getOutSize", lambda: 0)() or 0)
            for index in range(out_size):
                succ = getattr(current, "getOut", lambda _idx: None)(index)
                if succ in allowed and succ not in seen:
                    stack.append(succ)
        return False

    def _high_function_cbranch_count(self, high_function) -> int:
        return sum(
            1
            for block in self._iter_high_basic_blocks(high_function)
            for op in self._iter_high_block_ops(block)
            if getattr(op, "getMnemonic", lambda: None)() == "CBRANCH"
        )

    def _iter_high_basic_blocks(self, high_function):
        if high_function is None or not callable(getattr(high_function, "getBasicBlocks", None)):
            return
        try:
            for block in high_function.getBasicBlocks():
                yield block
        except Exception:
            return

    def _iter_high_block_ops(self, block):
        iterator = getattr(block, "getIterator", lambda: None)()
        if iterator is None:
            return
        while iterator.hasNext():
            yield iterator.next()

    def _mark_incomplete_control_flow(self, analysis: FunctionReturnAnalysis) -> None:
        """後段で保守的に扱うべき不完全な制御フロー要約を記録する。"""
        auto_notes = {
            "unknown_return",
            "overlapping_unconditional_returns",
            "indirect_control_flow_unresolved",
            "deferred_call_return_unresolved",
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
        if analysis.has_unresolved_return_value() and getattr(analysis, "deferred_calls", None):
            reasons.append("deferred_call_return_unresolved")

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
            bound_parameter_values, bound_parameter_storage_values = (
                self._bound_parameter_maps_for_target_args(target_ref, args)
            )
            scope_key = self._analysis_scope_key(
                target_ref,
                bound_parameter_values,
                bound_parameter_storage_values,
            )
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
            deferred_ref = getattr(info, "deferred_call_ref", None)
            pcode_ref = getattr(deferred_ref, "pcode_op_ref", None)
            stable_key_fn = getattr(pcode_ref, "stable_key", None)
            if not callable(stable_key_fn):
                continue
            pcode_key = stable_key_fn()
            target_specific_key = _call_argument_evidence_storage_key(
                pcode_key,
                getattr(info, "target_ref", None),
            )
            call_evidence = (
                evidence.get(target_specific_key)
                if target_specific_key is not None
                else None
            )
            if call_evidence is None:
                call_evidence = evidence.get(pcode_key)
            if call_evidence is None:
                continue
            target_matches = getattr(call_evidence, "target_matches", None)
            target_match_ok = not callable(target_matches) or target_matches(getattr(info, "target_ref", None))
            reason = getattr(call_evidence, "reason", None)
            if not target_match_ok:
                status = CallArgumentEvidence.RECOVERY_INCONCLUSIVE
                is_blocker = True
            else:
                status = getattr(call_evidence, "recovery_status", CallArgumentEvidence.RECOVERY_INCONCLUSIVE)
                if status not in {
                    CallArgumentEvidence.RECOVERY_COMPLETE,
                    CallArgumentEvidence.RECOVERY_RECOVERABLE_PARTIAL,
                    CallArgumentEvidence.RECOVERY_INCONCLUSIVE,
                }:
                    status = CallArgumentEvidence.RECOVERY_INCONCLUSIVE
            if status == CallArgumentEvidence.RECOVERY_COMPLETE:
                args = getattr(call_evidence, "arguments", ())
                info.arguments = [self._clone_expression(arg) for arg in args]
                changed = True
                is_blocker = False
            elif status == CallArgumentEvidence.RECOVERY_RECOVERABLE_PARTIAL:
                is_blocker = False
            else:
                status = CallArgumentEvidence.RECOVERY_INCONCLUSIVE
                is_blocker = True

            if callable(getattr(info, "set_call_argument_recovery_state", None)):
                info.set_call_argument_recovery_state(status, reason)
            else:
                info.call_argument_recovery_status = status
                info.call_argument_recovery_reason = reason
            if is_blocker:
                incomplete = True
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
            binary_id=self._binary_id,
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
            value_site_metadata = self._site_metadata_with_return_value_pcode_op_refs(
                site_metadata,
                return_varnode=return_source,
            )
            return [
                self._make_return_info(
                    address=address,
                    value=candidate_value,
                    conditions=normalized_conditions,
                    branch_index=return_index_base,
                    site_metadata=value_site_metadata,
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
            value_site_metadata = self._site_metadata_with_return_value_pcode_op_refs(
                site_metadata,
                return_varnode=return_source,
            )
            return [
                self._make_return_info(
                    address=address,
                    value=candidate_value,
                    conditions=normalized_conditions,
                    branch_index=return_index_base,
                    site_metadata=value_site_metadata,
                )
            ]

        split_cases = self._split_object_centric_return_case(
            candidate_value,
            normalized_conditions,
        )
        results: List[ReturnInfo] = []
        value_site_metadata = self._site_metadata_with_return_value_pcode_op_refs(
            site_metadata,
            return_varnode=return_source,
        )
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
                    site_metadata=value_site_metadata,
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
        needs_wrapper_recovery = self._analysis_needs_wrapper_recovery(analysis)

        if needs_wrapper_recovery:
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

        recovered_uncovered = self._recover_uncovered_terminal_call_returns_from_pcode(
            analysis,
            tracer,
            condition_tracker,
            return_ops,
            current_function,
            active_functions or set(),
        )
        if recovered_uncovered is not None:
            if self.debug:
                self._debug_print(
                    f"Call-wrapper recovery supplemented {len(recovered_uncovered)} return case(s) "
                    "after detecting uncovered terminal-call return path(s)"
                )
            return recovered_uncovered

        if self.debug:
            if needs_wrapper_recovery:
                self._debug_print(
                    "Call-wrapper recovery declined: no safe P-code/CFG reconstruction was available"
                )
            else:
                self._debug_print(
                    "Call-wrapper recovery declined: no unresolved return or uncovered terminal-call path"
                )
        return None

    def _recover_uncovered_terminal_call_returns_from_pcode(
        self,
        analysis: FunctionReturnAnalysis,
        tracer: PcodeTracer,
        condition_tracker: ConditionTracker,
        return_ops: List[Any],
        current_function,
        active_functions: Set[Tuple[Any, ...]],
    ) -> Optional[List[ReturnInfo]]:
        """既存 return partition から漏れた terminal CALL/CALLIND path だけを補完する。"""
        if analysis is None or not analysis.returns or not return_ops:
            return None

        recovered: List[ReturnInfo] = []
        for return_index, return_op in enumerate(return_ops):
            raw_entries = condition_tracker.get_all_valid_block_paths_to_return(return_op)
            path_entries = self._coerce_block_path_entries(raw_entries)
            if not path_entries:
                return None

            site_metadata = self._describe_pcode_site(return_op, analysis.entry_point)
            address = cast(str, site_metadata.get("address") or analysis.entry_point)

            for path_index, (block_path, path_conditions) in enumerate(path_entries):
                if self._return_path_is_covered_by_existing_return(
                    analysis,
                    path_conditions,
                ):
                    continue

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
                        self._debug_print(
                            "Call-wrapper uncovered-path recovery declined: uncovered path "
                            f"{path_index} to RETURN #{return_index} has no safe terminal CALL/CALLIND"
                        )
                    return None

                path_recovered = self._recover_implicit_return_from_terminal_call(
                    terminal_call,
                    address,
                    tracer,
                    condition_tracker,
                    list(path_conditions),
                    return_index * 1000 + path_index * 100,
                    all_path_conditions=[list(path_conditions)],
                    active_functions=active_functions,
                    current_function=current_function,
                    site_metadata=site_metadata,
                )
                if not path_recovered:
                    if self.debug:
                        self._debug_print(
                            "Call-wrapper uncovered-path recovery declined: terminal call expansion "
                            f"failed on path {path_index} to RETURN #{return_index}"
                        )
                    return None
                recovered.extend(path_recovered)

        if not recovered:
            return None

        if self._call_wrapper_recovery_conflicts_with_existing_returns(
            list(analysis.returns),
            recovered,
        ):
            return None
        if "uncovered_terminal_call_return_recovery" not in analysis.analysis_notes:
            analysis.analysis_notes.append("uncovered_terminal_call_return_recovery")
        merged = self._merge_equivalent_return_infos(
            self._prune_less_precise_return_infos(list(analysis.returns) + recovered)
        )
        return merged

    def _return_path_is_covered_by_existing_return(
        self,
        analysis: FunctionReturnAnalysis,
        path_conditions: Sequence[Condition],
    ) -> bool:
        path_conditions = ConditionSimplifier.simplify_conditions_object_centric(
            list(path_conditions or [])
        )
        if ConditionSimplifier.object_centric_is_contradiction(path_conditions):
            return True
        path_constraint_set = ConditionSimplifier.build_constraint_set(path_conditions)
        if path_constraint_set.is_contradictory:
            return True
        for ret in analysis.returns or []:
            ret_conditions = self._return_info_effective_region_conditions(ret)
            if path_constraint_set.implies_all(ret_conditions):
                return True
        return False

    def _call_wrapper_recovery_conflicts_with_existing_returns(
        self,
        existing_returns: List[ReturnInfo],
        recovered_returns: List[ReturnInfo],
    ) -> bool:
        for existing in existing_returns or []:
            existing_conditions = self._return_info_effective_region_conditions(existing)
            for recovered in recovered_returns or []:
                recovered_conditions = self._return_info_effective_region_conditions(recovered)
                combined = ConditionSimplifier.simplify_conditions_object_centric(
                    list(existing_conditions) + list(recovered_conditions)
                )
                if ConditionSimplifier.object_centric_is_contradiction(combined):
                    continue
                if _expressions_equivalent(existing.value, recovered.value):
                    continue
                return True
        return False

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
            binary_id=analysis.binary_id,
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
            binary_id=analysis.binary_id,
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

    def _normalize_bound_parameter_storage_values(
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
            normalized[normalized_key] = self._clone_expression(expr)
        return normalized

    def _bound_parameter_values_from_call_args(
        self,
        args: Optional[Sequence[Expression]],
        callee_parameters: Optional[Sequence[Dict]],
    ) -> Dict[int, Expression]:
        bound_by_identity: Dict[int, Expression] = {}
        for ordinal, arg in enumerate(args or []):
            if arg is None or callee_parameters is None or ordinal >= len(callee_parameters):
                continue
            callee_param = callee_parameters[ordinal] or {}
            try:
                parameter_index = int(callee_param.get("index"))
            except Exception:
                continue
            if parameter_index < 0:
                continue
            bound_by_identity[parameter_index] = arg
        return self._normalize_bound_parameter_values(bound_by_identity)

    def _bound_parameter_storage_values_from_call_args(
        self,
        args: Optional[Sequence[Expression]],
        callee_parameters: Optional[Sequence[Dict]],
    ) -> Dict[Tuple[Any, ...], Expression]:
        bound_by_storage: Dict[Tuple[Any, ...], Expression] = {}
        for ordinal, arg in enumerate(args or []):
            if arg is None or callee_parameters is None or ordinal >= len(callee_parameters):
                continue
            callee_param = callee_parameters[ordinal] or {}
            storage_info = self._coerce_wrapper_storage_info(callee_param.get("storage"))
            if storage_info is None:
                continue
            try:
                storage_key = storage_info.storage_identity_key()
            except Exception:
                storage_key = None
            if storage_key is None:
                continue
            bound_by_storage[tuple(storage_key)] = arg
        return self._normalize_bound_parameter_storage_values(bound_by_storage)

    def _bound_parameter_maps_for_target_args(
        self,
        target,
        args: Optional[Sequence[Expression]],
    ) -> Tuple[Dict[int, Expression], Dict[Tuple[Any, ...], Expression]]:
        target_ref = self._coerce_runtime_target_ref(target)
        if target_ref is None:
            return {}, {}
        callee_parameters = self._get_freshest_callee_parameters(target_ref)
        return (
            self._bound_parameter_values_from_call_args(args, callee_parameters),
            self._bound_parameter_storage_values_from_call_args(args, callee_parameters),
        )

    def _analysis_scope_key(
        self,
        target,
        bound_parameter_values: Optional[Dict[int, Expression]] = None,
        bound_parameter_storage_values: Optional[Dict[Tuple[Any, ...], Expression]] = None,
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
        normalized_bound_parameter_storage_values = self._normalize_bound_parameter_storage_values(
            bound_parameter_storage_values,
        )
        storage_bound_signature = tuple(
            (
                tuple(key),
                ConditionNormalizer.expression_signature(
                    expr,
                    include_memory_read_order=False,
                ),
            )
            for key, expr in sorted(
                normalized_bound_parameter_storage_values.items(),
                key=lambda item: repr(item[0]),
            )
        )
        return ("analysis_scope", target_key, bound_signature, storage_bound_signature)

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
        bound_parameter_storage_values: Optional[Dict[Tuple[Any, ...], Expression]] = None,
    ) -> PcodeTracer:
        try:
            return PcodeTracer(
                self.program,
                high_function,
                debug=self.debug,
                bound_parameter_values=bound_parameter_values,
                bound_parameter_storage_values=bound_parameter_storage_values,
                binary_id=self._binary_id,
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
        bound_parameter_storage_values: Optional[Dict[Tuple[Any, ...], Expression]] = None,
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
                bound_parameter_storage_values=bound_parameter_storage_values,
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
        bound_parameter_storage_values: Optional[Dict[Tuple[Any, ...], Expression]] = None,
    ):
        function_cache_key = self._function_cache_key(function)
        if function_cache_key is None:
            return None
        self._effect_summary_parameter_cache[function_cache_key] = list(parameters)
        summary_cache_key = self._analysis_scope_key(
            function,
            bound_parameter_values,
            bound_parameter_storage_values,
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
            callee_parameters_for_binding = self._get_freshest_callee_parameters(target_ref)
            callee_bound_parameter_values = self._bound_parameter_values_from_call_args(
                args,
                callee_parameters_for_binding,
            )
            callee_bound_parameter_storage_values = self._bound_parameter_storage_values_from_call_args(
                args,
                callee_parameters_for_binding,
            )
            callee_scope_key = self._analysis_scope_key(
                callee,
                callee_bound_parameter_values,
                callee_bound_parameter_storage_values,
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

            fresh_callee_parameters = self._collect_parameters(callee_high)
            callee_parameters = self._choose_richer_parameter_descriptors(
                callee_parameters_for_binding,
                fresh_callee_parameters,
            )
            callee_bound_parameter_values = self._bound_parameter_values_from_call_args(
                args,
                callee_parameters,
            )
            callee_bound_parameter_storage_values = self._bound_parameter_storage_values_from_call_args(
                args,
                callee_parameters,
            )
            callee_tracer = self._make_tracer(
                callee_high,
                bound_parameter_values=callee_bound_parameter_values,
                bound_parameter_storage_values=callee_bound_parameter_storage_values,
            )
            callee_tracer.record_deferred_call = self._make_deferred_call_recorder(callee)
            callee_tracker = ConditionTracker(callee_tracer)
            callee_tracer.condition_tracker = callee_tracker
            from .phi_resolver import PhiHandler

            callee_phi_handler = PhiHandler(callee_tracer, callee_tracker)
            callee_tracer.phi_handler = callee_phi_handler
            callee_tracker.build()
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
                bound_parameter_storage_values=callee_bound_parameter_storage_values,
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

        already_specialized = self._analysis_is_fully_argument_specialized(analysis)
        if len(args) < len(analysis.parameters) and not already_specialized:
            self._debug_print(
                f"Call expansion skipped for '{target_label}': "
                f"expected {len(analysis.parameters)} args, got {len(args)}"
            )
            return None

        specialized = analysis if already_specialized else self._specialize_call_analysis(analysis, args)
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
        return bool(bound_by_index or bound_by_storage)

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

        try:
            local_parameters = self._collect_parameters(high_function)
        except Exception:
            local_parameters = []
        bound_parameter_values = self._bound_parameter_values_from_call_args(
            args,
            local_parameters,
        )
        bound_parameter_storage_values = self._bound_parameter_storage_values_from_call_args(
            args,
            local_parameters,
        )
        tracer = self._make_tracer(
            high_function,
            bound_parameter_values=bound_parameter_values,
            bound_parameter_storage_values=bound_parameter_storage_values,
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
                "data_type_obj": descriptor.data_type_obj,
                "is_signed": descriptor.is_signed,
                "storage": descriptor.storage_info,
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

        bound_parameter_values, bound_parameter_storage_values = (
            self._bound_parameter_maps_for_target_args(target_ref, args)
        )
        cache_key = self._analysis_scope_key(
            callee,
            bound_parameter_values,
            bound_parameter_storage_values,
        )
        generic_cache_key = self._function_cache_key(callee)
        cached = self._call_analysis_cache.get(cache_key)
        if cached is not None and len(getattr(cached, "parameters", []) or []) >= minimum_param_count:
            return cached

        analysis = self.analyze_function(
            callee,
            timeout=60,
            active_functions=self._extend_active_functions(active_functions, target_ref),
            bound_parameter_values=bound_parameter_values,
            bound_parameter_storage_values=bound_parameter_storage_values,
        )
        if cached is None:
            self._call_analysis_cache[cache_key] = analysis
            if generic_cache_key is not None and not bound_parameter_values and not bound_parameter_storage_values:
                self._call_analysis_cache[generic_cache_key] = analysis
            return analysis
        if analysis is None:
            return cached
        if len(getattr(analysis, "parameters", []) or []) >= len(getattr(cached, "parameters", []) or []):
            self._call_analysis_cache[cache_key] = analysis
            if generic_cache_key is not None and not bound_parameter_values and not bound_parameter_storage_values:
                self._call_analysis_cache[generic_cache_key] = analysis
            return analysis
        return cached

    def _call_summary_is_safe(
        self,
        value: Expression,
        conditions: List[Condition],
        args: List[Expression],
    ) -> bool:
        if (
            self._expression_contains_unknown_or_call(value)
            and not self._expression_unknowns_are_deferred_call_refs(value)
        ):
            return False
        if not self._expression_references_only_allowed_objects(value, args):
            return False

        for cond in conditions:
            if self._expression_contains_unknown_or_call(cond.expression):
                return False
            if not self._expression_references_only_allowed_objects(cond.expression, args):
                return False

        return True

    def _expression_unknowns_are_deferred_call_refs(self, expr: Optional[Expression]) -> bool:
        if expr is None:
            return True
        if expr.expr_type == ExpressionType.UNKNOWN:
            runtime_ref = getattr(expr, "runtime_ref", None)
            return getattr(runtime_ref, "deferred_call_ref", None) is not None
        if expr.expr_type == ExpressionType.CALL:
            return False
        if expr.expr_type == ExpressionType.PHI and expr.value:
            for cond, value in expr.value:
                if cond is not None and not self._expression_unknowns_are_deferred_call_refs(cond.expression):
                    return False
                if not self._expression_unknowns_are_deferred_call_refs(value):
                    return False
            return True
        for operand in getattr(expr, "operands", []) or []:
            if not self._expression_unknowns_are_deferred_call_refs(operand):
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
                call_argument_recovery_status=getattr(
                    info,
                    "call_argument_recovery_status",
                    CallArgumentEvidence.RECOVERY_INCONCLUSIVE,
                ),
                call_argument_recovery_reason=getattr(
                    info,
                    "call_argument_recovery_reason",
                    None,
                ),
                effect_class=getattr(info, "effect_class", None),
                match_evidence=getattr(info, "match_evidence", None),
                domain_policy=getattr(info, "domain_policy", None),
                abi_return_width_bits=getattr(info, "abi_return_width_bits", None),
                abi_return_type_policy=getattr(info, "abi_return_type_policy", None),
                call_site_multiplicity=getattr(info, "call_site_multiplicity", None),
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
                    return_value_pcode_op_refs=tuple(
                        getattr(ret, "return_value_pcode_op_refs", ()) or ()
                    ),
                    return_kind=getattr(ret, "return_kind", "exact") or "exact",
                    acceptance_status=getattr(ret, "acceptance_status", None),
                    summary_candidate_id=getattr(ret, "summary_candidate_id", None),
                    summary_candidate_source_key=getattr(
                        ret,
                        "summary_candidate_source_key",
                        None,
                    ),
                    summary_transition_evidence_key=getattr(
                        ret,
                        "summary_transition_evidence_key",
                        None,
                    ),
                    validation_blockers=tuple(
                        getattr(ret, "validation_blockers", ()) or ()
                    ),
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
            return_type_provenance=dict(getattr(analysis, "return_type_provenance", {}) or {}),
            comparison_surface=analysis.comparison_surface,
            analysis_scope_key=analysis.analysis_scope_key,
            program_is_big_endian=analysis.program_is_big_endian,
            completed_recovery_proof_ids=tuple(
                getattr(analysis, "completed_recovery_proof_ids", ()) or ()
            ),
            completed_recovery_proof_evidence=tuple(
                getattr(analysis, "completed_recovery_proof_evidence", ()) or ()
            ),
            binary_id=analysis.binary_id,
            summary_return_candidates=tuple(
                getattr(analysis, "summary_return_candidates", ()) or ()
            ),
            return_outcomes=tuple(getattr(analysis, "return_outcomes", ()) or ()),
            divergence_outcomes=tuple(getattr(analysis, "divergence_outcomes", ()) or ()),
            unknown_outcomes=tuple(getattr(analysis, "unknown_outcomes", ()) or ()),
            analysis_view_identity=getattr(analysis, "analysis_view_identity", None),
            partition_revision=int(getattr(analysis, "partition_revision", 0) or 0),
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
                existing = self._current_deferred_calls[deferred_key]
                merged_status, merged_reason = self._merge_call_argument_recovery_state(
                    getattr(existing, "call_argument_recovery_status", None),
                    getattr(existing, "call_argument_recovery_reason", None),
                    getattr(info, "call_argument_recovery_status", None),
                    getattr(info, "call_argument_recovery_reason", None),
                )
                existing.set_call_argument_recovery_state(
                    merged_status,
                    merged_reason,
                )
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
                    call_argument_recovery_status=getattr(
                        info,
                        "call_argument_recovery_status",
                        CallArgumentEvidence.RECOVERY_INCONCLUSIVE,
                    ),
                    call_argument_recovery_reason=getattr(
                        info,
                        "call_argument_recovery_reason",
                        None,
                    ),
                    effect_class=getattr(info, "effect_class", None),
                    match_evidence=getattr(info, "match_evidence", None),
                    domain_policy=getattr(info, "domain_policy", None),
                    abi_return_width_bits=getattr(info, "abi_return_width_bits", None),
                    abi_return_type_policy=getattr(info, "abi_return_type_policy", None),
                    call_site_multiplicity=getattr(info, "call_site_multiplicity", None),
                )

    @staticmethod
    def _merge_call_argument_recovery_state(
        existing_status: Optional[str],
        existing_reason: Optional[str],
        incoming_status: Optional[str],
        incoming_reason: Optional[str],
    ) -> Tuple[str, Optional[str]]:
        rank = {
            CallArgumentEvidence.RECOVERY_COMPLETE: 0,
            CallArgumentEvidence.RECOVERY_RECOVERABLE_PARTIAL: 1,
            CallArgumentEvidence.RECOVERY_INCONCLUSIVE: 2,
        }

        def normalize_status(status: Optional[str]) -> str:
            value = str(status or CallArgumentEvidence.RECOVERY_INCONCLUSIVE)
            return value if value in rank else CallArgumentEvidence.RECOVERY_INCONCLUSIVE

        existing_norm = normalize_status(existing_status)
        incoming_norm = normalize_status(incoming_status)
        existing_rank = rank[existing_norm]
        incoming_rank = rank[incoming_norm]

        if incoming_rank > existing_rank:
            return incoming_norm, incoming_reason or existing_reason
        if existing_rank > incoming_rank:
            return existing_norm, existing_reason
        if (existing_reason is None) and (incoming_reason is not None):
            return incoming_norm, incoming_reason
        return existing_norm, existing_reason

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

        if expr.expr_type == ExpressionType.UNKNOWN:
            runtime_ref = getattr(expr, "runtime_ref", None)
            return getattr(runtime_ref, "deferred_call_ref", None) is not None
        if expr.expr_type == ExpressionType.CALL:
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
        return_type_obj=None,
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
            if return_type_obj is not None and self._is_void_type(return_type_obj):
                fallback_condition_sets = list(all_valid_path_conditions or [])
                if not fallback_condition_sets:
                    fallback_condition_sets = [list(path_conditions)]
                fallback_returns: List[ReturnInfo] = []
                for path_idx, candidate_conditions in enumerate(fallback_condition_sets):
                    simplified_conds = ConditionSimplifier.simplify_conditions_object_centric(
                        list(candidate_conditions)
                    )
                    fallback_returns.append(
                        self._make_return_info(
                            address=address,
                            value=Expression.unknown("void"),
                            conditions=simplified_conds,
                            branch_index=return_index * 1000 + path_idx,
                            site_metadata=site_metadata,
                        )
                    )
                return self._merge_equivalent_return_infos(
                    self._prune_less_precise_return_infos(fallback_returns)
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
                    return_type_obj=return_type_obj,
                )
                if implicit_results is not None:
                    return implicit_results
                return self._merge_equivalent_return_infos(
                    self._prune_less_precise_return_infos(
                        [
                            self._make_return_info(
                                address=address,
                                value=Expression.unknown("void"),
                                conditions=ConditionSimplifier.simplify_conditions_object_centric(
                                    list(candidate_conditions)
                                ),
                                branch_index=return_index * 1000 + path_idx,
                                site_metadata=site_metadata,
                            )
                            for path_idx, candidate_conditions in enumerate(
                                list(all_valid_path_conditions or []) or [list(path_conditions)]
                            )
                        ]
                    )
                )
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
        return_type_obj=None,
    ) -> Optional[List[ReturnInfo]]:
        """RETURN オペランドが欠落している場合に、返り値レジスタ由来の値を復元する。"""
        if return_type_obj is not None and self._is_void_type(return_type_obj):
            return None
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

        value_site_metadata = self._site_metadata_with_return_value_pcode_op_refs(
            site_metadata,
            return_varnode=tracked.varnode,
            producer_op=producer_op,
        )
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
            site_metadata=value_site_metadata,
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
        from ..transform.expander import ExpandedValue

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

        value_site_metadata = self._site_metadata_with_return_value_pcode_op_refs(
            site_metadata,
            return_varnode=return_varnode,
        )

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

        phi_expansion_candidate_origin_keys: Tuple[Tuple[Any, ...], ...] = ()
        if has_multiequal:
            phi_expansion_candidate_origin_keys = self._phi_origin_keys_from_return_varnode_trace(
                tracer,
                return_varnode,
            )

        results = self._build_return_infos_from_expansions(
            address,
            expanded_values,
            return_index,
            site_metadata=value_site_metadata,
            return_kind="phi_expansion" if has_multiequal else None,
            candidate_phi_origin_keys=phi_expansion_candidate_origin_keys,
        )
        if has_multiequal and results:
            results = self._append_smt_lowerable_phi_return_fallback_infos(
                results,
                tracer=tracer,
                return_varnode=return_varnode,
                path_condition_sets=all_path_conditions or ([path_conditions] if path_conditions else [[]]),
                address=address,
                return_index=return_index,
                site_metadata=value_site_metadata,
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
                site_metadata=value_site_metadata,
            )]
        
        return results

    def _append_smt_lowerable_phi_return_fallback_infos(
        self,
        return_infos: List[ReturnInfo],
        *,
        tracer,
        return_varnode,
        path_condition_sets: Sequence[Sequence[Condition]],
        address: str,
        return_index: int,
        site_metadata: Optional[Dict[str, Optional[object]]] = None,
    ):
        try:
            fallback_value = tracer.trace_varnode(return_varnode, use_cache=False)
        except Exception:
            return return_infos
        if not isinstance(fallback_value, Expression):
            return return_infos
        if not self._expression_contains_phi(fallback_value):
            return return_infos
        rewritten_value, _changed = self._normalize_callother_userop_expression(fallback_value)
        fallback_value = rewritten_value
        if fallback_value is None or expression_contains_unsupported_smt_ops(fallback_value):
            return return_infos
        candidate_phi_origin_keys = tuple(
            sorted(
                self._phi_circular_origin_stable_keys(fallback_value)
                | set(self._phi_origin_keys_from_varnode_defs(return_varnode)),
                key=repr,
            )
        )
        fallback_conditions = list(path_condition_sets or ())
        if not fallback_conditions:
            fallback_conditions = [[]]
        additions = []
        union_condition = self._path_condition_sets_union_condition(fallback_conditions)
        if union_condition is not None:
            union_conditions = ConditionSimplifier.simplify_conditions_object_centric([union_condition])
            if not ConditionSimplifier.object_centric_is_contradiction(union_conditions):
                union_value = self._normalize_expanded_return_value(
                    fallback_value,
                    union_conditions,
                )
                if union_value is None:
                    union_value = fallback_value
                if (
                    union_value is not None
                    and not expression_contains_unsupported_smt_ops(union_value)
                    and not self._expression_contains_phi(union_value)
                ):
                    info = self._make_return_info(
                        address=address,
                        value=union_value,
                        conditions=union_conditions,
                        branch_index=return_index * 100 + 80,
                        site_metadata=site_metadata,
                    )
                    info = replace(
                        info,
                        return_kind="phi_union_reachability_fallback",
                        summary_candidate_source_key=(
                            "phi_union_reachability_fallback",
                            ("candidate_discovery_only_phi_origin_keys", candidate_phi_origin_keys),
                        ) if candidate_phi_origin_keys else getattr(info, "summary_candidate_source_key", None),
                    )
                    additions.append(info)
        for index, conditions in enumerate(fallback_conditions):
            simplified = ConditionSimplifier.simplify_conditions_object_centric(
                list(conditions or [])
            )
            if ConditionSimplifier.object_centric_is_contradiction(simplified):
                continue
            normalized_value = self._normalize_expanded_return_value(
                fallback_value,
                simplified,
            )
            if normalized_value is None:
                normalized_value = fallback_value

            if self._expression_contains_phi(normalized_value):
                finite_candidates = self._phi_free_finite_fallback_candidates(
                    fallback_value,
                    simplified,
                )
            else:
                finite_candidates = [(simplified, normalized_value)]

            for finite_index, (finite_conditions, finite_value) in enumerate(finite_candidates):
                if self._expression_contains_phi(finite_value):
                    continue
                if any(
                    self._expression_contains_phi(getattr(condition, "expression", None))
                    or self._expression_contains_unknown_or_call(getattr(condition, "expression", None))
                    for condition in finite_conditions or ()
                ):
                    continue
                branch_index = return_index * 100 + 90 + index
                if len(finite_candidates) > 1:
                    branch_index = branch_index * 100 + finite_index
                info = self._make_return_info(
                    address=address,
                    value=finite_value,
                    conditions=finite_conditions,
                    branch_index=branch_index,
                    site_metadata=site_metadata,
                )
                info = replace(
                    info,
                    return_kind="phi_reachability_fallback",
                    summary_candidate_source_key=(
                        "phi_reachability_fallback",
                        ("candidate_phi_origin_keys", candidate_phi_origin_keys),
                        ("return_phi_origin_keys", candidate_phi_origin_keys),
                    ) if candidate_phi_origin_keys else getattr(info, "summary_candidate_source_key", None),
                )
                additions.append(info)
        if not additions:
            return return_infos
        if self.debug:
            self._debug_print(
                "Preserved SMT-lowerable PHI return fallback for broad return-path coverage"
            )
        return self._merge_equivalent_return_infos(
            self._prune_less_precise_return_infos(list(return_infos or []) + additions)
        )

    def _phi_origin_keys_from_return_varnode_trace(
        self,
        tracer,
        return_varnode,
    ) -> Tuple[Tuple[Any, ...], ...]:
        keys: Set[Tuple[Any, ...]] = set(self._phi_origin_keys_from_varnode_defs(return_varnode))
        try:
            fallback_value = tracer.trace_varnode(return_varnode, use_cache=False)
        except Exception:
            fallback_value = None
        if isinstance(fallback_value, Expression):
            keys.update(self._phi_circular_origin_stable_keys(fallback_value))
        return tuple(sorted(keys, key=repr))

    def _phi_origin_keys_from_varnode_defs(
        self,
        varnode,
        *,
        max_depth: int = 8,
    ) -> Set[Tuple[Any, ...]]:
        keys: Set[Tuple[Any, ...]] = set()
        seen: Set[int] = set()

        def visit(current, depth: int) -> None:
            if current is None or depth > int(max_depth):
                return
            marker = id(current)
            if marker in seen:
                return
            seen.add(marker)
            try:
                op = current.getDef()
            except Exception:
                op = None
            if op is None:
                return
            if getattr(op, "getMnemonic", lambda: None)() == "MULTIEQUAL":
                key = self._pcode_op_stable_key(op)
                if isinstance(key, tuple):
                    keys.add(key)
            try:
                input_count = int(op.getNumInputs())
            except Exception:
                input_count = 0
            for index in range(input_count):
                try:
                    visit(op.getInput(index), depth + 1)
                except Exception:
                    continue

        visit(varnode, 0)
        return keys

    def _path_condition_sets_union_condition(
        self,
        path_condition_sets: Sequence[Sequence[Condition]],
    ) -> Optional[Condition]:
        disjuncts: List[Expression] = []
        for conditions in path_condition_sets or ():
            conjunct = self._condition_set_conjunction_expression(conditions)
            if conjunct is None:
                return None
            disjuncts.append(conjunct)
        if len(disjuncts) <= 1:
            return None
        union_expr = disjuncts[0]
        for disjunct in disjuncts[1:]:
            union_expr = Expression.binary_op("BOOL_OR", union_expr, disjunct)
            union_expr.size = 1
        return Condition(union_expr)

    def _condition_set_conjunction_expression(
        self,
        conditions: Sequence[Condition],
    ) -> Optional[Expression]:
        terms = [self._condition_to_expression(condition) for condition in conditions or ()]
        terms = [term for term in terms if term is not None]
        if not terms:
            one = Expression.constant(1, size=1)
            return one
        result = terms[0]
        for term in terms[1:]:
            result = Expression.binary_op("BOOL_AND", result, term)
            result.size = 1
        return result

    def _condition_to_expression(self, condition: Condition) -> Optional[Expression]:
        expr = getattr(condition, "expression", None)
        if expr is None:
            return None
        if not bool(getattr(condition, "negated", False)):
            return expr
        negated = Expression.unary_op("BOOL_NEGATE", expr)
        negated.size = 1
        return negated

    def _phi_free_finite_fallback_candidates(
        self,
        fallback_value: Expression,
        conditions: Sequence[Condition],
    ) -> List[Tuple[List[Condition], Expression]]:
        finite_condition_sets = self._split_small_finite_parameter_reachability_conditions(
            conditions,
        )
        if len(finite_condition_sets) <= 1:
            return []
        candidates: List[Tuple[List[Condition], Expression]] = []
        skipped_phi = 0
        skipped_none = 0
        for finite_conditions in finite_condition_sets:
            finite_value = self._normalize_expanded_return_value(
                fallback_value,
                finite_conditions,
            )
            if finite_value is None:
                skipped_none += 1
                continue
            if self._expression_contains_phi(finite_value):
                skipped_phi += 1
                continue
            candidates.append((finite_conditions, finite_value))
        if self.debug and (skipped_phi or skipped_none):
            self._debug_print(
                "Finite PHI fallback split retained "
                f"{len(candidates)}/{len(finite_condition_sets)} cases "
                f"(skipped_phi={skipped_phi}, skipped_none={skipped_none})"
            )
        return candidates

    def _split_small_finite_parameter_reachability_conditions(
        self,
        conditions: Sequence[Condition],
        *,
        search_min: int = -8,
        search_max: int = 64,
        max_cases: int = 16,
    ) -> List[List[Condition]]:
        parameter = self._single_parameter_expression_in_conditions(conditions)
        if parameter is None:
            return [list(conditions or [])]
        feasible_values: List[int] = []
        for value in range(int(search_min), int(search_max) + 1):
            equality = self._parameter_equals_condition(parameter, value)
            if not self._conditions_are_unsat(list(conditions or []) + [equality]):
                feasible_values.append(value)
                if len(feasible_values) > int(max_cases):
                    return [list(conditions or [])]
        if len(feasible_values) <= 1:
            return [list(conditions or [])]
        uncovered_conditions = list(conditions or [])
        for value in feasible_values:
            uncovered_conditions.append(self._parameter_equals_condition(parameter, value).negate())
        if not self._conditions_are_unsat(uncovered_conditions):
            return [list(conditions or [])]
        result: List[List[Condition]] = []
        for value in feasible_values:
            split_conditions = ConditionSimplifier.simplify_conditions_object_centric(
                list(conditions or []) + [self._parameter_equals_condition(parameter, value)]
            )
            if ConditionSimplifier.object_centric_is_contradiction(split_conditions):
                continue
            result.append(split_conditions)
        return result or [list(conditions or [])]

    def _single_parameter_expression_in_conditions(
        self,
        conditions: Sequence[Condition],
    ) -> Optional[Expression]:
        parameters: Dict[Tuple[Any, ...], Expression] = {}
        for condition in conditions or []:
            for node in _iter_expression_nodes(getattr(condition, "expression", None), include_phi_conditions=True):
                if getattr(node, "expr_type", None) != ExpressionType.PARAMETER:
                    continue
                try:
                    key = node.structural_key()
                except Exception:
                    continue
                parameters[key] = node
                if len(parameters) > 1:
                    return None
        return next(iter(parameters.values()), None)

    def _parameter_equals_condition(self, parameter: Expression, value: int) -> Condition:
        size = max(1, int(getattr(parameter, "size", 0) or 4))
        expr = Expression.binary_op("INT_EQUAL", parameter, Expression.constant(int(value), size=size))
        expr.size = 1
        return Condition(expr)

    def _conditions_are_unsat(self, conditions: Sequence[Condition]) -> bool:
        try:
            solver_result = ConditionSMTOracle.conjunction_is_unsat(list(conditions or []))
        except Exception:
            solver_result = None
        if solver_result is not None:
            return bool(solver_result)
        return ConditionSimplifier.object_centric_is_contradiction(list(conditions or []))

    def _phi_expression_key_set(
        self,
        expr: Optional[Expression],
    ) -> Set[Tuple[Any, ...]]:
        keys: Set[Tuple[Any, ...]] = set()

        def visit(node: Optional[Expression]) -> None:
            if node is None:
                return
            if getattr(node, "expr_type", None) == ExpressionType.PHI:
                try:
                    keys.add(node.structural_key(budget=256))
                except Exception:
                    pass
                for condition, value in getattr(node, "value", None) or []:
                    if condition is not None:
                        visit(getattr(condition, "expression", None))
                    visit(value)
                return
            for operand in getattr(node, "operands", None) or []:
                visit(operand)

        visit(expr)
        return keys

    def _build_return_infos_from_expansions(
        self,
        address: str,
        expanded_values,
        return_index: int,
        site_metadata: Optional[Dict[str, Optional[object]]] = None,
        return_kind: Optional[str] = None,
        candidate_phi_origin_keys: Sequence[Tuple[Any, ...]] = (),
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

                info = self._make_return_info(
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
                split_candidate_phi_origin_keys = tuple(
                    sorted(
                        self._phi_circular_origin_stable_keys(split_value)
                        or self._phi_circular_origin_stable_keys(ev.value)
                        or set(candidate_phi_origin_keys or ()),
                        key=repr,
                    )
                )
                if return_kind:
                    source_key_items: List[Tuple[Any, ...]] = []
                    if split_candidate_phi_origin_keys:
                        source_key_items.append(("candidate_phi_origin_keys", split_candidate_phi_origin_keys))
                        source_key_items.append(("return_phi_origin_keys", split_candidate_phi_origin_keys))
                    info = replace(
                        info,
                        return_kind=return_kind,
                        summary_candidate_source_key=(
                            (return_kind, *source_key_items)
                            if source_key_items
                            else getattr(info, "summary_candidate_source_key", None)
                        ),
                    )
                results.append(info)
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
            if any(
                self._return_value_is_multiplicative_phi_recurrence_candidate(info.value)
                for info in unresolved_group
            ):
                if self.debug:
                    self._debug_print(
                        "Preserved unresolved multiplicative PHI return cases for "
                        "structural recurrence summary validation"
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

    def _return_value_is_multiplicative_phi_recurrence_candidate(self, value: Optional[Expression]) -> bool:
        if getattr(value, "expr_type", None) != ExpressionType.BINARY_OP:
            return False
        if getattr(value, "operator", None) not in {"INT_MULT", "INT_LEFT"}:
            return False
        operands = tuple(getattr(value, "operands", ()) or ())
        if len(operands) != 2:
            return False
        has_phi_unknown = any(self._expression_contains_phi_circular_marker(operand) for operand in operands)
        has_constant = any(getattr(operand, "expr_type", None) == ExpressionType.CONSTANT for operand in operands)
        return bool(has_phi_unknown and has_constant)

    def _expression_contains_phi_circular_marker(self, expr: Optional[Expression]) -> bool:
        if expr is None:
            return False
        if getattr(expr, "expr_type", None) == ExpressionType.UNKNOWN:
            if str(getattr(expr, "name", "") or getattr(expr, "value", "") or "") == "phi_circular":
                return True
            runtime_ref = getattr(expr, "runtime_ref", None)
            if (
                isinstance(runtime_ref, UnknownValueRef)
                and getattr(runtime_ref, "reason", None) == "phi_circular"
            ):
                return True
            if getattr(runtime_ref, "kind", None) == "phi_circular":
                return True
        return any(
            self._expression_contains_phi_circular_marker(operand)
            for operand in (getattr(expr, "operands", None) or ())
        )

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
                    replace(
                        info,
                        value=info.value,
                        conditions=region,
                        branch_index=self._split_branch_index(info.branch_index, original_index, split_index),
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
            if (
                self._expression_contains_deferred_call_value(current.value)
                and not _expressions_equivalent(prior.value, current.value)
            ):
                if self.debug:
                    self._debug_print(
                        "preserving deferred-call return region because prior concrete "
                        "case does not prove the unresolved region redundant"
                    )
                return False
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

    def _expression_contains_deferred_call_value(self, expr: Optional[Expression]) -> bool:
        if expr is None:
            return False
        if getattr(expr, "expr_type", None) == ExpressionType.UNKNOWN:
            runtime_ref = getattr(expr, "runtime_ref", None)
            if getattr(runtime_ref, "deferred_call_ref", None) is not None:
                return True
        if getattr(expr, "expr_type", None) == ExpressionType.PHI and getattr(expr, "value", None):
            for condition, value in expr.value or []:
                if condition is not None and self._expression_contains_deferred_call_value(condition.expression):
                    return True
                if self._expression_contains_deferred_call_value(value):
                    return True
            return False
        for operand in getattr(expr, "operands", None) or ():
            if self._expression_contains_deferred_call_value(operand):
                return True
        return False

    def _clear_resolved_call_effect_blockers(self, analysis: Optional[FunctionReturnAnalysis]) -> None:
        if analysis is None:
            return
        if getattr(analysis, "deferred_calls", None):
            return
        if any(
            self._expression_contains_deferred_call_value(getattr(ret, "value", None))
            or any(
                self._expression_contains_deferred_call_value(getattr(cond, "expression", None))
                for cond in (getattr(ret, "conditions", None) or [])
            )
            for ret in (getattr(analysis, "returns", None) or [])
        ):
            return
        blocking_notes = {
            "effect_call_argument_evidence",
            "effect_call_argument_evidence_incomplete",
        }
        effect_summary = getattr(analysis, "effect_summary", None)
        if effect_summary is not None and getattr(effect_summary, "call_argument_evidence", None):
            return
        if any(note in blocking_notes for note in getattr(analysis, "analysis_notes", []) or []):
            analysis.analysis_notes = [
                note
                for note in (analysis.analysis_notes or [])
                if note not in blocking_notes
            ]
            if "bounded_call_effect_resolved" not in analysis.analysis_notes:
                analysis.analysis_notes.append("bounded_call_effect_resolved")

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
        return replace(
            primary,
            value=primary.value,
            conditions=normalized_conditions,
            branch_index=self._min_branch_index(primary.branch_index, secondary.branch_index),
            summary_candidate_source_key=self._merge_return_info_summary_candidate_source_keys(
                primary,
                secondary,
            ),
        )

    def _merge_return_info_summary_candidate_source_keys(
        self,
        primary: ReturnInfo,
        secondary: ReturnInfo,
    ) -> Optional[Tuple[Any, ...]]:
        primary_key = getattr(primary, "summary_candidate_source_key", None)
        secondary_key = getattr(secondary, "summary_candidate_source_key", None)
        if primary_key is None:
            return secondary_key
        if secondary_key is None or secondary_key == primary_key:
            return primary_key
        candidate_keys = tuple(
            sorted(
                self._candidate_phi_origin_keys_from_summary_source_key(primary_key)
                | self._candidate_phi_origin_keys_from_summary_source_key(secondary_key),
                key=repr,
            )
        )
        return_keys = tuple(
            sorted(
                self._return_phi_origin_keys_from_summary_source_key(primary_key)
                | self._return_phi_origin_keys_from_summary_source_key(secondary_key),
                key=repr,
            )
        )
        proof_sources = tuple(
            key for key in (primary_key, secondary_key)
            if self._candidate_phi_origin_keys_from_summary_source_key(key)
            or self._return_phi_origin_keys_from_summary_source_key(key)
        )
        discovery_only_sources = tuple(
            key for key in (primary_key, secondary_key)
            if key not in proof_sources
        )
        items: List[Tuple[Any, ...]] = []
        if candidate_keys:
            items.append(("candidate_phi_origin_keys", candidate_keys))
        if return_keys:
            items.append(("return_phi_origin_keys", return_keys))
        if proof_sources:
            items.append(("proof_candidate_sources", proof_sources))
        if discovery_only_sources:
            items.append(("discovery_only_sources", discovery_only_sources))
        return ("merged_return_info_sources", *items)

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
            reduced_value = self._reduce_phi_expression_under_conditions_with_smt(
                reduced_value if reduced_value is not None else value,
                conditions,
            )
            if reduced_value is not None:
                normalized_value = reduced_value
            if self.debug and normalized_value is not value:
                self._debug_print(
                    "Reduced PHI-bearing expanded return under active conditions: "
                    f"{self._debug_expr_summary(value)} -> {self._debug_expr_summary(normalized_value)}"
                )

        substituted_value = self._substitute_parameter_constants_under_conditions(
            normalized_value,
            conditions,
        )
        if substituted_value is not None and substituted_value is not normalized_value:
            normalized_value = substituted_value
            if self.debug:
                self._debug_print(
                    "Specialized expanded return under exact parameter conditions: "
                    f"{self._debug_expr_summary(value)} -> {self._debug_expr_summary(normalized_value)}"
                )
        assignments = self._parameter_constant_assignments_from_conditions(conditions)
        evaluated_value = self._evaluate_expression_under_parameter_assignments(
            normalized_value,
            assignments,
        )
        if evaluated_value is not None and evaluated_value is not normalized_value:
            normalized_value = evaluated_value
            if self.debug:
                self._debug_print(
                    "Evaluated expanded return PHI selectors under exact parameter conditions: "
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

    def _substitute_parameter_constants_under_conditions(
        self,
        expr: Optional[Expression],
        conditions: Sequence[Condition],
    ) -> Optional[Expression]:
        assignments = self._parameter_constant_assignments_from_conditions(conditions)
        if not assignments:
            return expr
        substituted = self._substitute_parameter_constants(expr, assignments)
        if substituted is None:
            return expr
        folded = self._fold_constant_expression(substituted, fallback_expr=expr)
        return folded if folded is not None else substituted

    def _parameter_constant_assignments_from_conditions(
        self,
        conditions: Sequence[Condition],
    ) -> Dict[Tuple[Any, ...], Tuple[Expression, int]]:
        assignments: Dict[Tuple[Any, ...], Tuple[Expression, int]] = {}
        for condition in conditions or ():
            if getattr(condition, "negated", False):
                continue
            expr = getattr(condition, "expression", None)
            if getattr(expr, "expr_type", None) != ExpressionType.BINARY_OP:
                continue
            if getattr(expr, "operator", None) != "INT_EQUAL":
                continue
            operands = list(getattr(expr, "operands", None) or [])
            if len(operands) != 2:
                continue
            for parameter, constant in ((operands[0], operands[1]), (operands[1], operands[0])):
                if getattr(parameter, "expr_type", None) != ExpressionType.PARAMETER:
                    continue
                if getattr(constant, "expr_type", None) != ExpressionType.CONSTANT:
                    continue
                try:
                    key = parameter.structural_key()
                    value = int(getattr(constant, "value", 0) or 0)
                except Exception:
                    continue
                existing = assignments.get(key)
                if existing is not None and existing[1] != value:
                    assignments.pop(key, None)
                    continue
                assignments[key] = (parameter, value)
        return assignments

    def _substitute_parameter_constants(
        self,
        expr: Optional[Expression],
        assignments: Mapping[Tuple[Any, ...], Tuple[Expression, int]],
    ) -> Optional[Expression]:
        if expr is None:
            return expr
        if getattr(expr, "expr_type", None) == ExpressionType.PARAMETER:
            try:
                key = expr.structural_key()
            except Exception:
                key = None
            assigned = assignments.get(key) if key is not None else None
            if assigned is None:
                return expr
            parameter, value = assigned
            return Expression.constant(
                int(value),
                size=max(1, int(getattr(parameter, "size", 0) or getattr(expr, "size", 0) or 4)),
            )
        if getattr(expr, "expr_type", None) == ExpressionType.PHI:
            changed = False
            branches = []
            for condition, value in getattr(expr, "value", None) or []:
                rewritten_condition = condition
                if condition is not None:
                    rewritten_condition_expr = self._substitute_parameter_constants(
                        getattr(condition, "expression", None),
                        assignments,
                    )
                    if rewritten_condition_expr is not getattr(condition, "expression", None):
                        rewritten_condition = Condition(
                            rewritten_condition_expr,
                            getattr(condition, "negated", False),
                        )
                        changed = True
                rewritten_value = self._substitute_parameter_constants(value, assignments)
                if rewritten_value is not value:
                    changed = True
                branches.append((rewritten_condition, rewritten_value if rewritten_value is not None else value))
            if not changed:
                return expr
            rebuilt = Expression.phi(branches)
            rebuilt.size = getattr(expr, "size", 0)
            return rebuilt
        operands = list(getattr(expr, "operands", None) or [])
        if not operands:
            return expr
        rewritten_operands = []
        changed = False
        for operand in operands:
            rewritten = self._substitute_parameter_constants(operand, assignments)
            if rewritten is None:
                rewritten = operand
            rewritten_operands.append(rewritten)
            changed = changed or rewritten is not operand
        if not changed:
            return expr
        rebuilt = expr.clone_with(operands=rewritten_operands)
        folded = self._fold_constant_expression(rebuilt, fallback_expr=expr)
        return folded if folded is not None else rebuilt

    def _reduce_phi_expression_under_conditions_with_smt(
        self,
        expr: Optional[Expression],
        conditions: Sequence[Condition],
        *,
        _active_ids: Optional[Set[int]] = None,
    ) -> Optional[Expression]:
        """Reduce PHI branches whose selector reachability is SMT-proved.

        PHI rendering is ordered: the first true condition wins, and the final
        branch is the fallback.  A branch can be selected only when active
        return reachability proves all earlier selectors false and proves this
        selector true.  Ambiguous selectors are preserved.
        """

        if expr is None:
            return expr
        active_ids = set() if _active_ids is None else set(_active_ids)
        expr_id = id(expr)
        if expr_id in active_ids:
            return expr
        active_ids.add(expr_id)

        expr_type = getattr(expr, "expr_type", None)
        if expr_type == ExpressionType.PHI:
            branches = list(getattr(expr, "value", None) or [])
            if not branches:
                return expr

            prior_conditions: List[Condition] = []
            surviving: List[Tuple[Optional[Condition], Expression]] = []
            changed = False
            active_conditions = list(conditions or [])
            assignments = self._parameter_constant_assignments_from_conditions(active_conditions)

            for branch_condition, branch_value in branches:
                branch_reachability = [
                    prior.negate()
                    for prior in prior_conditions
                    if prior is not None
                ]
                if branch_condition is not None:
                    branch_reachability.append(branch_condition)

                if branch_reachability and (
                    self._conditions_conjunction_is_false_under_assignments(
                        branch_reachability,
                        assignments,
                    )
                    or self._conditions_are_unsat(active_conditions + branch_reachability)
                ):
                    changed = True
                    if branch_condition is not None:
                        prior_conditions.append(branch_condition)
                    continue

                if self._active_conditions_imply_all(
                    active_conditions,
                    branch_reachability,
                    assignments=assignments,
                ):
                    return self._reduce_phi_expression_under_conditions_with_smt(
                        branch_value,
                        active_conditions + branch_reachability,
                        _active_ids=active_ids,
                    )

                reduced_branch = self._reduce_phi_expression_under_conditions_with_smt(
                    branch_value,
                    active_conditions + branch_reachability,
                    _active_ids=active_ids,
                )
                if reduced_branch is None:
                    reduced_branch = branch_value
                if reduced_branch is not branch_value:
                    changed = True
                surviving.append((branch_condition, reduced_branch))
                if branch_condition is not None:
                    prior_conditions.append(branch_condition)

            if not surviving:
                return expr
            if len(surviving) == 1:
                return surviving[0][1]
            if not changed:
                return expr
            rebuilt = Expression.phi(surviving)
            rebuilt.size = getattr(expr, "size", 0)
            return rebuilt

        operands = list(getattr(expr, "operands", None) or [])
        if not operands:
            return expr
        rewritten_operands = []
        changed = False
        for operand in operands:
            rewritten = self._reduce_phi_expression_under_conditions_with_smt(
                operand,
                conditions,
                _active_ids=active_ids,
            )
            if rewritten is None:
                rewritten = operand
            rewritten_operands.append(rewritten)
            changed = changed or rewritten is not operand
        if not changed:
            return expr
        return expr.clone_with(operands=rewritten_operands)

    def _active_conditions_imply_all(
        self,
        active_conditions: Sequence[Condition],
        conclusions: Sequence[Condition],
        *,
        assignments: Optional[Mapping[Tuple[Any, ...], Tuple[Expression, int]]] = None,
    ) -> bool:
        for conclusion in conclusions or ():
            truth = self._condition_truth_under_parameter_assignments(
                conclusion,
                assignments or {},
            )
            if truth is True:
                continue
            if truth is False:
                return False
            try:
                negated = conclusion.negate()
            except Exception:
                return False
            if not self._conditions_are_unsat(list(active_conditions or []) + [negated]):
                return False
        return True

    def _conditions_conjunction_is_false_under_assignments(
        self,
        conditions: Sequence[Condition],
        assignments: Mapping[Tuple[Any, ...], Tuple[Expression, int]],
    ) -> bool:
        if not assignments:
            return False
        for condition in conditions or ():
            truth = self._condition_truth_under_parameter_assignments(condition, assignments)
            if truth is False:
                return True
        return False

    def _condition_truth_under_parameter_assignments(
        self,
        condition: Optional[Condition],
        assignments: Mapping[Tuple[Any, ...], Tuple[Expression, int]],
        *,
        _active_ids: Optional[Set[int]] = None,
    ) -> Optional[bool]:
        if condition is None or not assignments:
            return None
        substituted = self._evaluate_expression_under_parameter_assignments(
            getattr(condition, "expression", None),
            assignments,
            _active_ids=_active_ids,
        )
        evaluated = eval_constant_raw(substituted) if substituted is not None else None
        if evaluated is None:
            return None
        raw_value, _bits = evaluated
        truth = bool(raw_value)
        if getattr(condition, "negated", False):
            truth = not truth
        return truth

    def _evaluate_expression_under_parameter_assignments(
        self,
        expr: Optional[Expression],
        assignments: Mapping[Tuple[Any, ...], Tuple[Expression, int]],
        *,
        _active_ids: Optional[Set[int]] = None,
    ) -> Optional[Expression]:
        if expr is None or not assignments:
            return expr
        active_ids = set() if _active_ids is None else set(_active_ids)
        expr_id = id(expr)
        if expr_id in active_ids:
            return expr
        active_ids.add(expr_id)

        if getattr(expr, "expr_type", None) == ExpressionType.PARAMETER:
            try:
                key = expr.structural_key()
            except Exception:
                key = None
            assigned = assignments.get(key) if key is not None else None
            if assigned is None:
                return expr
            parameter, value = assigned
            return Expression.constant(
                int(value),
                size=max(1, int(getattr(parameter, "size", 0) or getattr(expr, "size", 0) or 4)),
            )

        if getattr(expr, "expr_type", None) == ExpressionType.PHI:
            branches = list(getattr(expr, "value", None) or [])
            if not branches:
                return expr
            rewritten_branches: List[Tuple[Optional[Condition], Expression]] = []
            changed = False
            for condition, value in branches:
                if condition is None:
                    selected = self._evaluate_expression_under_parameter_assignments(
                        value,
                        assignments,
                        _active_ids=active_ids,
                    )
                    if not rewritten_branches:
                        return selected if selected is not None else value
                    if selected is not None and selected is not value:
                        changed = True
                    rewritten_branches.append((None, selected if selected is not None else value))
                    continue
                truth = self._condition_truth_under_parameter_assignments(
                    condition,
                    assignments,
                    _active_ids=active_ids,
                )
                if truth is True:
                    selected = self._evaluate_expression_under_parameter_assignments(
                        value,
                        assignments,
                        _active_ids=active_ids,
                    )
                    return selected if selected is not None else value
                if truth is False:
                    changed = True
                    continue
                rewritten_condition = condition
                rewritten_condition_expr = self._evaluate_expression_under_parameter_assignments(
                    getattr(condition, "expression", None),
                    assignments,
                    _active_ids=active_ids,
                )
                if rewritten_condition_expr is not None and rewritten_condition_expr is not getattr(condition, "expression", None):
                    rewritten_condition = Condition(
                        rewritten_condition_expr,
                        bool(getattr(condition, "negated", False)),
                    )
                    changed = True
                rewritten_value = self._evaluate_expression_under_parameter_assignments(
                    value,
                    assignments,
                    _active_ids=active_ids,
                )
                if rewritten_value is not None and rewritten_value is not value:
                    changed = True
                rewritten_branches.append((rewritten_condition, rewritten_value if rewritten_value is not None else value))
            if not rewritten_branches:
                return expr
            if len(rewritten_branches) == 1:
                return rewritten_branches[0][1]
            if not changed:
                return expr
            rebuilt = Expression.phi(rewritten_branches)
            rebuilt.size = getattr(expr, "size", 0)
            return rebuilt

        operands = list(getattr(expr, "operands", None) or [])
        if not operands:
            return expr
        rewritten_operands = []
        changed = False
        for operand in operands:
            rewritten = self._evaluate_expression_under_parameter_assignments(
                operand,
                assignments,
                _active_ids=active_ids,
            )
            if rewritten is None:
                rewritten = operand
            rewritten_operands.append(rewritten)
            changed = changed or rewritten is not operand
        if not changed:
            return expr
        rebuilt = expr.clone_with(operands=rewritten_operands)
        folded = self._fold_constant_expression(rebuilt, fallback_expr=expr)
        return folded if folded is not None else rebuilt

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
        self._last_analysis_failure = None
        function = self._find_function_by_name(function_name)
        if function is None:
            message = f"Function '{function_name}' not found"
            self._last_function_lookup_error = message
            self._last_analysis_failure = AnalysisFailure(
                status=ANALYSIS_STATUS_FUNCTION_LOOKUP_MISS,
                message=message,
                function_name=function_name,
            )
            self._debug_print(self._last_function_lookup_error)
            return None
        try:
            return self.analyze_function(function, timeout)
        except Exception as exc:
            self._last_analysis_failure = AnalysisFailure(
                status=ANALYSIS_STATUS_ANALYSIS_EXCEPTION,
                message=str(exc),
                function_name=function_name,
            )
            raise

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

        self._normalize_return_partition(summary)
        self._mark_incomplete_control_flow(summary)
        return summary

    def get_last_function_lookup_error(self) -> Optional[str]:
        return self._last_function_lookup_error

    def get_last_analysis_failure(self) -> Optional[AnalysisFailure]:
        return self._last_analysis_failure

    def get_last_analysis_failure_status(self) -> Optional[str]:
        failure = self._last_analysis_failure
        return failure.status if failure is not None else None

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

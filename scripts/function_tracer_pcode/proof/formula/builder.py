# -*- coding: utf-8 -*-
"""SMT式構築モジュール"""

import hashlib
import re
from typing import List, Dict, Optional, Tuple, Any

from scripts.function_tracer_pcode.core import (
    Condition,
    Expression,
    ExpressionType,
    FunctionReturnAnalysis,
    ReadonlyReductionRef,
    loop_summary_method_b_key,
)
from scripts.function_tracer_pcode.core.signature import is_floating_data_type
from scripts.function_tracer_pcode.core.render_smt import (
    CallDeclarationConflict,
    call_smt_declaration_lines,
    collect_call_smt_declarations,
    collect_float_predicate_smt_declarations,
    collect_intrinsic_smt_declarations,
    collect_unknown_smt_declarations,
    collect_global_address_identities,
    global_address_symbol_name,
    GLOBAL_ADDRESS_BITS,
    expression_uses_smt_uf,
    expression_uses_smt_float_theory,
    expression_smt_bit_width,
    smt_logic_name,
)
from scripts.function_tracer_pcode.proof.formula.params import (
    build_fragment_backed_parameter_constraint,
    collect_fragment_infos_by_param_index,
    build_parameter_constraint,
    build_parameter_semantic_constraints,
    build_parameter_pairs,
    build_symbol_name_mapping,
    collect_param_info,
    merge_param_and_extra_vars,
)
from scripts.function_tracer_pcode.proof.formula.returns import (
    ReturnWidthMismatchError,
    build_return_definition,
    get_return_size,
    require_equal_return_bit_widths,
)
from scripts.function_tracer_pcode.semantics.param_semantics import infer_parameter_semantics
from scripts.function_tracer_pcode.semantics.semantic_width import (
    align_return_value_extension_surfaces,
    normalize_analysis_semantic_width,
)
from scripts.function_tracer_pcode.proof.formula.types import (
    ExtraVariableInfo,
    FormulaBuildContext,
    FormulaBuilderResult,
    ParameterInfo,
    ParameterPair,
)
from scripts.function_tracer_pcode.proof.formula.variable import (
    VariableAnalyzer,
    ExtraVariableAnalysis,
    get_parameter_fragment_constraints,
)
from scripts.function_tracer_pcode.proof.formula.symbol_replace import build_symbol_replacer
from scripts.function_tracer_pcode.analysis.memory_resolver import (
    collect_memory_bit_widths_from_analysis,
)

from scripts.function_tracer_pcode.proof.ub.constraints import UbConstraintBuilder


# Re-exports kept for callers that import these names from this module.
from scripts.function_tracer_pcode.proof.formula.variable import VariableClassification


def _rewrite_guard_parameter_metadata_for_smt(guard, param_infos):
    """Align proof/runtime guard parameter widths with active SMT declarations."""
    if not param_infos:
        return guard
    params_by_index, params_by_name = _param_info_lookup(param_infos)
    if isinstance(guard, Condition):
        rewritten_expr = _rewrite_expr_parameter_metadata_for_smt(
            guard.expression,
            params_by_index,
            params_by_name,
        )
        if rewritten_expr is guard.expression:
            return guard
        return Condition(rewritten_expr, guard.negated)
    if isinstance(guard, Expression):
        return _rewrite_expr_parameter_metadata_for_smt(
            guard,
            params_by_index,
            params_by_name,
        )
    return guard


def _param_info_lookup(param_infos) -> Tuple[Dict[int, ParameterInfo], Dict[str, ParameterInfo]]:
    params_by_index: Dict[int, ParameterInfo] = {}
    params_by_name: Dict[str, ParameterInfo] = {}
    for info in param_infos or ():
        try:
            index = int(getattr(info, "index"))
        except (TypeError, ValueError):
            index = -1
        if index >= 0:
            params_by_index[index] = info
        name = getattr(info, "original_name", None)
        if isinstance(name, str) and name:
            params_by_name[name] = info
    return params_by_index, params_by_name


def _rewrite_expr_parameter_metadata_for_smt(
    expr: Optional[Expression],
    params_by_index: Dict[int, ParameterInfo],
    params_by_name: Dict[str, ParameterInfo],
) -> Optional[Expression]:
    if expr is None:
        return expr
    if expr.expr_type == ExpressionType.PARAMETER:
        return _rewrite_parameter_leaf_for_smt(expr, params_by_index, params_by_name)
    if expr.expr_type == ExpressionType.PHI and expr.value:
        changed = False
        branches = []
        for condition, value in expr.value:
            new_condition = None
            if condition is not None:
                new_condition_expr = _rewrite_expr_parameter_metadata_for_smt(
                    condition.expression,
                    params_by_index,
                    params_by_name,
                )
                changed = changed or (new_condition_expr is not condition.expression)
                new_condition = Condition(new_condition_expr, condition.negated)
            new_value = _rewrite_expr_parameter_metadata_for_smt(
                value,
                params_by_index,
                params_by_name,
            )
            changed = changed or (new_value is not value)
            branches.append((new_condition, new_value))
        if not changed:
            return expr
        rebuilt = Expression.phi(branches)
        rebuilt.size = expr.size
        rebuilt.data_type = expr.data_type
        rebuilt.data_type_obj = getattr(expr, "data_type_obj", None)
        rebuilt.storage_info = expr.storage_info
        rebuilt.read_order_key = expr.read_order_key
        rebuilt.runtime_ref = getattr(expr, "runtime_ref", None)
        return rebuilt

    operands = getattr(expr, "operands", None) or []
    if not operands:
        return expr
    rewritten_operands = [
        _rewrite_expr_parameter_metadata_for_smt(operand, params_by_index, params_by_name)
        for operand in operands
    ]
    rewritten_operands = _normalize_guard_operand_widths_for_smt(expr.operator, rewritten_operands)
    if all(new is old for new, old in zip(rewritten_operands, operands)):
        return expr
    return Expression(
        expr_type=expr.expr_type,
        value=expr.value,
        operator=expr.operator,
        operands=rewritten_operands,
        size=expr.size,
        name=expr.name,
        data_type=expr.data_type,
        data_type_obj=getattr(expr, "data_type_obj", None),
        storage_info=expr.storage_info,
        read_order_key=expr.read_order_key,
        runtime_ref=getattr(expr, "runtime_ref", None),
        opcode=getattr(expr, "opcode", None),
    )


def _normalize_guard_operand_widths_for_smt(operator, operands):
    if len(operands) != 2:
        return operands
    left, right = operands
    if operator in {
        "INT_EQUAL",
        "INT_NOTEQUAL",
        "INT_LESS",
        "INT_SLESS",
        "INT_LESSEQUAL",
        "INT_SLESSEQUAL",
    }:
        return _normalize_comparison_literal_widths_for_smt(left, right)
    if operator == "INT_AND":
        return _normalize_mask_literal_widths_for_smt(left, right)
    return operands


def _normalize_comparison_literal_widths_for_smt(left, right):
    if _expr_is_constant(left) and _expr_bit_width(right) > 0:
        narrowed = _narrow_constant_for_guard_smt(left, _expr_bit_width(right))
        if narrowed is not left:
            return [narrowed, right]
    if _expr_is_constant(right) and _expr_bit_width(left) > 0:
        narrowed = _narrow_constant_for_guard_smt(right, _expr_bit_width(left))
        if narrowed is not right:
            return [left, narrowed]
    return [left, right]


def _normalize_mask_literal_widths_for_smt(left, right):
    if _expr_is_constant(left) and _expr_uses_parameter(right) and _expr_bit_width(right) > 0:
        narrowed = _narrow_constant_for_guard_smt(left, _expr_bit_width(right))
        if narrowed is not left:
            return [narrowed, right]
    if _expr_is_constant(right) and _expr_uses_parameter(left) and _expr_bit_width(left) > 0:
        narrowed = _narrow_constant_for_guard_smt(right, _expr_bit_width(left))
        if narrowed is not right:
            return [left, narrowed]
    return [left, right]


def _narrow_constant_for_guard_smt(expr, target_bits: int):
    if not _expr_is_constant(expr) or target_bits <= 0:
        return expr
    current_bits = _expr_bit_width(expr)
    if current_bits <= 0 or current_bits <= target_bits:
        return expr
    value = int(expr.value)
    current_mask = (1 << current_bits) - 1
    target_mask = (1 << target_bits) - 1
    value_mod = value & current_mask
    if value_mod & target_mask != value_mod and value_mod != target_mask:
        return expr
    narrowed = value_mod & target_mask
    return Expression.constant(narrowed, size=max(1, (target_bits + 7) // 8))


def _expr_is_constant(expr) -> bool:
    return getattr(expr, "expr_type", None) == ExpressionType.CONSTANT


def _expr_bit_width(expr) -> int:
    if expr is None:
        return 0
    try:
        return int(expr.get_bit_width())
    except (AttributeError, TypeError, ValueError):
        return 0


def _expr_uses_parameter(expr) -> bool:
    if expr is None:
        return False
    if getattr(expr, "expr_type", None) == ExpressionType.PARAMETER:
        return True
    if getattr(expr, "expr_type", None) == ExpressionType.PHI and getattr(expr, "value", None):
        for condition, value in expr.value:
            if condition is not None and _expr_uses_parameter(getattr(condition, "expression", None)):
                return True
            if _expr_uses_parameter(value):
                return True
        return False
    return any(_expr_uses_parameter(operand) for operand in getattr(expr, "operands", None) or [])


def _rewrite_parameter_leaf_for_smt(
    expr: Expression,
    params_by_index: Dict[int, ParameterInfo],
    params_by_name: Dict[str, ParameterInfo],
) -> Expression:
    info = None
    try:
        index = int(getattr(expr, "value"))
    except (TypeError, ValueError):
        index = -1
    if index >= 0:
        info = params_by_index.get(index)
    if info is None and expr.name:
        info = params_by_name.get(expr.name)
    if info is None:
        return expr

    try:
        bit_width = int(getattr(info, "bit_width", 0) or 0)
    except (TypeError, ValueError):
        bit_width = 0
    if bit_width <= 0:
        return expr
    desired_size = max(1, (bit_width + 7) // 8)
    desired_index = getattr(info, "index", expr.value)
    desired_name = getattr(info, "original_name", None) or expr.name
    if desired_size == expr.size and desired_index == expr.value and desired_name == expr.name:
        return expr
    return Expression(
        expr_type=expr.expr_type,
        value=desired_index,
        operator=expr.operator,
        operands=list(expr.operands or []),
        size=desired_size,
        name=desired_name,
        data_type=expr.data_type,
        data_type_obj=getattr(expr, "data_type_obj", None),
        storage_info=expr.storage_info,
        read_order_key=expr.read_order_key,
        runtime_ref=getattr(expr, "runtime_ref", None),
        opcode=getattr(expr, "opcode", None),
    )


class CallFormulaUnsupported(ValueError):
    """conditional lane で CALL を UF として宣言できない（fail closed）。

    幅が取れない CALL、同じ symbol に別 signature を要求する CALL のいずれも
    ここで止める。silent rename や片側優先は、証明していない値の一致を主張する
    ことになるので行わない。
    """


class FormulaBuilder:
    """2つの関数解析結果からSMT式を構築"""
    
    def __init__(
        self,
        debug: bool = False,
        exclude_ub: bool = True,
        assume_fp_non_nan: bool = False,
        allow_call: bool = False,
    ):
        """
        Args:
            debug: デバッグ出力を有効にする
            exclude_ub: UB（未定義動作）除外制約を追加する
            assume_fp_non_nan: FP引数がNaNでないことを明示前提として追加する
            allow_call: ``ExpressionType.CALL`` を uninterpreted function として
                受け入れる。**conditional view 由来の formula 専用**
                (Issue #20 PR-20-B2)。既定の無条件 lane は ``False`` のままで、
                CALL を含む通常 analysis は従来どおり unsupported として扱われる。
        """
        self.debug = debug
        self.exclude_ub = exclude_ub
        self.assume_fp_non_nan = assume_fp_non_nan
        if type(allow_call) is not bool:
            raise TypeError("allow_call must be an exact bool")
        self.allow_call = allow_call
        self.variable_analyzer = VariableAnalyzer(debug=debug)
        self.ub_constraint_builder = UbConstraintBuilder(debug=debug)
    
    def build_equivalence_formula_extended(
        self,
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
        func1_suffix: str = "_1",
        func2_suffix: str = "_2",
        extra_assertions: Optional[List[str]] = None,  # ★ NEW
        canonical_return_observation_width: Optional[int] = None,
    ) -> FormulaBuilderResult:
        """
        2つの関数の等価性検証用SMT式を構築（拡張版）
        
        Args:
            analysis1, analysis2: 各関数の解析結果
            func1_suffix, func2_suffix: サフィックス
            extra_assertions: 追加のアサート文（(check-sat)の直前に挿入）
        
        Returns:
            FormulaBuilderResult: 構築結果（詳細情報付き）
        """
        analysis1, analysis2, _, _ = self._normalize_analyses(analysis1, analysis2)

        lines = []
        context = self._prepare_formula_context(
            analysis1, analysis2, func1_suffix, func2_suffix, emit_debug_info=True
        )
        render_analysis1 = normalize_analysis_semantic_width(
            analysis1,
            infer_parameter_semantics(analysis1),
            context.extra_vars1,
        )
        render_analysis2 = normalize_analysis_semantic_width(
            analysis2,
            infer_parameter_semantics(analysis2),
            context.extra_vars2,
        )
        
        # ヘッダー
        lines.append("; " + "=" * 60)
        lines.append("; Equivalence Check")
        lines.append(f"; Function 1: {analysis1.function_name}")
        lines.append(f"; Function 2: {analysis2.function_name}")
        lines.append("; " + "=" * 60)
        lines.append("")
        lines.append(f"(set-logic {context.smt_logic})")
        lines.append("")
        lines.extend(context.header_lines)
        
        # 全変数の情報を統合（パラメータ + 追加変数）
        all_vars1 = self._merge_param_and_extra_vars(context.params1, context.extra_vars1)
        all_vars2 = self._merge_param_and_extra_vars(context.params2, context.extra_vars2)
        
        # 関数1のreturn値を定義
        lines.append("; " + "-" * 40)
        lines.append(f"; Return value for {analysis1.function_name}")
        lines.append("; " + "-" * 40)
        return_var1 = f"return{func1_suffix}"
        return_def1 = self._build_return_definition(render_analysis1, return_var1, all_vars1)
        lines.extend(return_def1)
        lines.append("")
        
        # 関数2のreturn値を定義
        lines.append("; " + "-" * 40)
        lines.append(f"; Return value for {analysis2.function_name}")
        lines.append("; " + "-" * 40)
        return_var2 = f"return{func2_suffix}"
        return_def2 = self._build_return_definition(render_analysis2, return_var2, all_vars2)
        lines.extend(return_def2)
        lines.append("")
        
        # 等価性の否定をアサート
        lines.extend(
            self._build_equivalence_assertion(
                return_var1,
                return_var2,
                context.return_size1,
                context.return_size2,
                canonical_return_observation_width=canonical_return_observation_width,
            )
        )
        
        # ★ NEW: 追加アサート（(check-sat)の直前に挿入）
        if extra_assertions:
            lines.append("")
            lines.extend(extra_assertions)
        
        lines.append("")
        lines.append("(check-sat)")
        lines.append("(get-model)")
        
        return FormulaBuilderResult(
            formula="\n".join(lines),
            return_var1=return_var1,
            return_var2=return_var2,
            extra_vars1=context.extra_vars1,
            extra_vars2=context.extra_vars2,
            constrained_fragments=context.constrained_fragments,
            param_fragment_constrained=context.param_fragment_constrained
        )

    def _prepare_formula_context(
        self,
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
        func1_suffix: str,
        func2_suffix: str,
        emit_debug_info: bool = False,
    ) -> FormulaBuildContext:
        """宣言・制約・補助情報をまとめて構築する"""
        params1 = self._collect_param_info(analysis1.parameters, func1_suffix)
        params2 = self._collect_param_info(analysis2.parameters, func2_suffix)
        self._apply_semantic_hints(params1, infer_parameter_semantics(analysis1))
        self._apply_semantic_hints(params2, infer_parameter_semantics(analysis2))

        param_names1 = {p.original_name for p in params1}
        param_names2 = {p.original_name for p in params2}

        return_size1 = self._get_return_size(analysis1)
        return_size2 = self._get_return_size(analysis2)

        var_analyses1 = self.variable_analyzer.analyze_all_extra_variables(
            analysis1, param_names1, return_size1
        )
        var_analyses2 = self.variable_analyzer.analyze_all_extra_variables(
            analysis2, param_names2, return_size2
        )

        extra_vars1 = self._build_extra_variable_infos(var_analyses1, func1_suffix)
        extra_vars2 = self._build_extra_variable_infos(var_analyses2, func2_suffix)

        if self.debug and emit_debug_info:
            self._print_debug_info(params1, params2, extra_vars1, extra_vars2)

        param_pairs = self._build_parameter_pairs(params1, params2)
        (
            header_lines,
            runtime_unknown_declarations,
            constrained_fragments,
            param_fragment_constrained,
        ) = self._build_base_header_lines(
            analysis1,
            analysis2,
            params1,
            params2,
            extra_vars1,
            extra_vars2,
            var_analyses1,
            var_analyses2,
            param_pairs,
            func1_suffix,
            func2_suffix,
        )
        smt_logic = self._select_smt_logic(analysis1, analysis2)
        smt_logic = self._upgrade_smt_logic_for_header_declarations(
            smt_logic,
            header_lines,
        )

        return FormulaBuildContext(
            params1=params1,
            params2=params2,
            extra_vars1=extra_vars1,
            extra_vars2=extra_vars2,
            var_analyses1=var_analyses1,
            var_analyses2=var_analyses2,
            param_pairs=param_pairs,
            return_size1=return_size1,
            return_size2=return_size2,
            smt_logic=smt_logic,
            header_lines=header_lines,
            runtime_unknown_declarations=runtime_unknown_declarations,
            constrained_fragments=constrained_fragments,
            param_fragment_constrained=param_fragment_constrained,
        )

    def _normalize_analyses(
        self,
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
    ):
        """Apply semantic-width normalization before SMT lowering."""
        hints1 = infer_parameter_semantics(analysis1)
        hints2 = infer_parameter_semantics(analysis2)
        normalized1 = normalize_analysis_semantic_width(analysis1, hints1)
        normalized2 = normalize_analysis_semantic_width(analysis2, hints2)
        normalized1, normalized2 = align_return_value_extension_surfaces(normalized1, normalized2)
        return normalized1, normalized2, hints1, hints2

    def _select_smt_logic(
        self,
        *analyses: FunctionReturnAnalysis,
    ) -> str:
        analyses = [analysis for analysis in analyses if analysis is not None]
        uses_arrays = any(collect_memory_bit_widths_from_analysis(analysis) for analysis in analyses)
        uses_float_theory = False
        uses_uf = False
        for analysis in analyses:
            for expr, guards in self._iter_analysis_expressions_with_guards(analysis):
                if expression_uses_smt_float_theory(expr):
                    uses_float_theory = True
                if expression_uses_smt_uf(expr, float_mode="fp"):
                    uses_uf = True
                for guard in guards or ():
                    guard_expr = getattr(guard, "expression", guard)
                    if expression_uses_smt_float_theory(guard_expr):
                        uses_float_theory = True
                    if expression_uses_smt_uf(guard_expr, float_mode="fp"):
                        uses_uf = True
                if uses_float_theory and uses_uf:
                    break
            if uses_float_theory and uses_uf:
                break
        return smt_logic_name(
            uses_float_theory=uses_float_theory,
            uses_arrays=uses_arrays,
            uses_uf=uses_uf,
        )

    def _upgrade_smt_logic_for_header_declarations(
        self,
        smt_logic: str,
        header_lines: List[str],
    ) -> str:
        if any("fp.isNaN" in str(line) for line in header_lines or []):
            has_uf = any(
                str(line).lstrip().startswith("(declare-fun ")
                for line in header_lines or []
            )
            if has_uf:
                if smt_logic in {"QF_AUFBV", "QF_AUFBVFP"}:
                    return "QF_AUFBVFP"
                return "QF_UFFPBV"
            if smt_logic == "QF_AUFBV":
                return "QF_AUFBVFP"
            return "QF_FPBV"
        if not any(str(line).lstrip().startswith("(declare-fun ") for line in header_lines or []):
            return smt_logic
        if smt_logic == "QF_BV":
            return "QF_UFBV"
        if smt_logic == "QF_FPBV":
            return "QF_UFFPBV"
        return smt_logic

    def _build_base_header_lines(
        self,
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
        params1: List[ParameterInfo],
        params2: List[ParameterInfo],
        extra_vars1: List[ExtraVariableInfo],
        extra_vars2: List[ExtraVariableInfo],
        var_analyses1: Dict[str, ExtraVariableAnalysis],
        var_analyses2: Dict[str, ExtraVariableAnalysis],
        param_pairs: List[ParameterPair],
        func1_suffix: str,
        func2_suffix: str
    ) -> Tuple[List[str], List[Tuple[str, int]], List[str], List[str]]:
        """共通の宣言・制約セクションを組み立てる"""
        lines: List[str] = []

        render_declaration_analysis1 = normalize_analysis_semantic_width(
            analysis1,
            infer_parameter_semantics(analysis1),
            extra_vars1,
        )
        render_declaration_analysis2 = normalize_analysis_semantic_width(
            analysis2,
            infer_parameter_semantics(analysis2),
            extra_vars2,
        )
        declaration_analyses = (
            analysis1,
            analysis2,
            render_declaration_analysis1,
            render_declaration_analysis2,
        )

        mem_widths = self._collect_memory_widths(*declaration_analyses)
        if mem_widths:
            lines.extend(self._build_memory_declarations(mem_widths))

        lines.extend(self._build_param_declarations(analysis1.function_name, params1))

        if extra_vars1:
            lines.extend(
                self._build_extra_var_declarations(analysis1.function_name, extra_vars1)
            )

        lines.extend(self._build_param_declarations(analysis2.function_name, params2))

        if extra_vars2:
            lines.extend(
                self._build_extra_var_declarations(analysis2.function_name, extra_vars2)
            )

        runtime_unknown_decls = self._collect_runtime_unknown_declarations(
            *declaration_analyses,
        )
        if runtime_unknown_decls:
            lines.extend(self._build_runtime_unknown_declarations(runtime_unknown_decls))

        global_objects = self._collect_global_address_identities(*declaration_analyses)
        if global_objects:
            lines.extend(self._build_global_address_constraints(global_objects))

        intrinsic_decls = self._collect_intrinsic_smt_declarations(
            *declaration_analyses,
        )
        if intrinsic_decls:
            lines.extend(self._build_intrinsic_smt_declarations(intrinsic_decls))

        call_decls = self._collect_call_smt_declarations(*declaration_analyses)
        if call_decls:
            lines.extend(self._build_call_smt_declarations(call_decls))

        float_predicate_decls = self._collect_float_predicate_smt_declarations(
            *declaration_analyses,
        )
        if float_predicate_decls:
            lines.extend(self._build_float_predicate_smt_declarations(float_predicate_decls))

        loop_summary_notes = self._collect_loop_summary_smt_notes(
            *declaration_analyses,
        )
        if loop_summary_notes:
            lines.extend(self._build_loop_summary_smt_notes(loop_summary_notes))

        readonly_witness_axioms = self._build_readonly_reduction_witness_axioms_section(
            (
                (
                    render_declaration_analysis1,
                    self._merge_param_and_extra_vars(params1, extra_vars1),
                ),
                (
                    render_declaration_analysis2,
                    self._merge_param_and_extra_vars(params2, extra_vars2),
                ),
            )
        )
        if readonly_witness_axioms:
            lines.extend(readonly_witness_axioms)

        semantic_lines = self._build_param_semantic_constraints_section(params1, params2)
        if semantic_lines:
            lines.extend(semantic_lines)

        lines.extend(
            self._build_param_constraints_section(
                param_pairs,
                var_analyses1,
                var_analyses2,
            )
        )

        constrained_fragments: List[str] = []
        param_fragment_constrained: List[str] = []
        constraint_lines, constrained_vars = self._build_extra_var_constraints(
            extra_vars1,
            extra_vars2,
            var_analyses1,
            var_analyses2,
            func1_suffix,
            func2_suffix,
        )
        if constraint_lines:
            lines.extend(constraint_lines)
            constrained_fragments.extend(constrained_vars)
            param_fragment_constrained.extend(constrained_vars)

        if self.exclude_ub:
            ub_lines = self._build_ub_constraints_section(
                analysis1,
                analysis2,
                params1,
                params2,
                extra_vars1,
                extra_vars2,
            )
            if ub_lines:
                lines.extend(ub_lines)

        fp_non_nan_lines = self._build_fp_non_nan_assumptions_section(
            analysis1,
            analysis2,
            params1,
            params2,
        )
        if fp_non_nan_lines:
            lines.extend(fp_non_nan_lines)

        return lines, runtime_unknown_decls, constrained_fragments, param_fragment_constrained

    def _build_fp_non_nan_assumptions_section(
        self,
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
        params1: List[ParameterInfo],
        params2: List[ParameterInfo],
    ) -> List[str]:
        if not self.assume_fp_non_nan:
            return []
        lines: List[str] = [
            "",
            "; " + "-" * 40,
            "; Explicit FP input-domain assumptions",
            "; Enabled by --assume-fp-non-nan; this is conditional equivalence.",
            "; " + "-" * 40,
        ]
        for side_label, analysis, params in (
            ("function1", analysis1, params1),
            ("function2", analysis2, params2),
        ):
            descriptors = self._parameter_descriptors_by_identity(analysis)
            for param in params:
                descriptor = descriptors.get(("index", param.index)) or descriptors.get(
                    ("name", param.original_name)
                )
                if not self._parameter_descriptor_is_fp(descriptor):
                    continue
                fp_sort = self._fp_sort_for_bit_width(param.bit_width)
                if fp_sort is None:
                    # Skip unsupported precision-width parameters so this section only
                    # adds concrete assumptions that can be rendered as SMT-LIB fp.isNaN.
                    continue
                ebits, sbits = fp_sort
                lines.append(
                    f"; {side_label}:{param.original_name} is assumed non-NaN"
                )
                lines.append(
                    f"(assert (not (fp.isNaN ((_ to_fp {ebits} {sbits}) {param.smt_name}))))"
                )

        if not any(line.strip().startswith("(assert ") for line in lines):
            return []
        lines.append("")
        return lines

    def _has_fp_non_nan_domain_assumptions(
        self,
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
        params1: List[ParameterInfo],
        params2: List[ParameterInfo],
    ) -> bool:
        if not self.assume_fp_non_nan:
            return False
        for analysis, params in ((analysis1, params1), (analysis2, params2)):
            descriptors = self._parameter_descriptors_by_identity(analysis)
            for param in params:
                descriptor = descriptors.get(("index", param.index)) or descriptors.get(
                    ("name", param.original_name)
                )
                if not self._parameter_descriptor_is_fp(descriptor):
                    continue
                if self._fp_sort_for_bit_width(param.bit_width) is not None:
                    return True
        return False

    @staticmethod
    def _parameter_descriptors_by_identity(
        analysis: FunctionReturnAnalysis,
    ) -> Dict[Tuple[str, Any], Dict[str, Any]]:
        descriptors: Dict[Tuple[str, Any], Dict[str, Any]] = {}
        for raw in getattr(analysis, "parameters", ()) or ():
            if not isinstance(raw, dict):
                continue
            descriptor = dict(raw)
            index = descriptor.get("index")
            if isinstance(index, int) and index >= 0:
                descriptors[("index", index)] = descriptor
            name = descriptor.get("name")
            if isinstance(name, str) and name:
                descriptors[("name", name)] = descriptor
        return descriptors

    @staticmethod
    def _parameter_descriptor_is_fp(descriptor: Optional[Dict[str, Any]]) -> bool:
        if not isinstance(descriptor, dict):
            return False
        data_type_obj = descriptor.get("data_type_obj")
        data_type_name = str(descriptor.get("data_type") or "")

        if is_floating_data_type(data_type_obj, data_type_name):
            return True

        data_type = str(descriptor.get("data_type") or "").lower()
        if data_type in {"float", "double"}:
            return True

        # Fallback for alias/normalized forms and typedef-like spellings when
        # runtime type objects are not available.
        return bool(
            re.search(r"(?:^|[\s_])(?:float|double|_float16|_float32|_float64)(?:$|[\s_])", data_type)
            or re.search(r"\blong\s*double\b", data_type)
        )

    @staticmethod
    def _fp_sort_for_bit_width(bit_width: int) -> Optional[Tuple[int, int]]:
        try:
            bits = int(bit_width)
        except (TypeError, ValueError):
            return None
        # FP precondition mode currently supports fp.isNaN assertions only for
        # 32/64bit floating-point parameters where SMT translation is direct.
        if bits == 32:
            return 8, 24
        if bits == 64:
            return 11, 53
        return None
    
    # ============================================
    # NEW: UB制約セクション構築
    # ============================================
    def _build_ub_constraints_section(
        self,
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
        params1: List[ParameterInfo],
        params2: List[ParameterInfo],
        extra_vars1: List[ExtraVariableInfo],
        extra_vars2: List[ExtraVariableInfo],
    ) -> List[str]:
        """UB除外制約セクションを構築"""
        lines = []

        symbol_replace_fn1 = build_symbol_replacer(params1, extra_vars1)
        symbol_replace_fn2 = build_symbol_replacer(params2, extra_vars2)
        
        ub1_constraints = self.ub_constraint_builder.build_constraints(
            analysis1,
            params1,
            symbol_replace_fn=symbol_replace_fn1,
        )
        
        ub2_constraints = self.ub_constraint_builder.build_constraints(
            analysis2,
            params2,
            symbol_replace_fn=symbol_replace_fn2,
        )
        
        if ub1_constraints or ub2_constraints:
            lines.append("; " + "-" * 40)
            lines.append("; UB Exclusion Constraints (C semantics)")
            lines.append("; Exclude undefined behavior inputs")
            lines.append("; " + "-" * 40)
            
            if ub1_constraints:
                lines.append(f"; Function 1: {analysis1.function_name}")
                lines.extend(ub1_constraints)
            
            if ub2_constraints:
                lines.append(f"; Function 2: {analysis2.function_name}")
                lines.extend(ub2_constraints)
            
            lines.append("")
        
        return lines
    
    def _build_extra_variable_infos(
        self,
        analyses: Dict[str, ExtraVariableAnalysis],
        suffix: str
    ) -> List[ExtraVariableInfo]:
        """分析結果からExtraVariableInfoを構築"""
        result = []
        for name, analysis in analyses.items():
            result.append(ExtraVariableInfo(
                original_name=name,
                smt_name=f"{name}{suffix}",
                bit_width=analysis.bit_width,
                analysis=analysis
            ))
        return result
    
    def _print_debug_info(
        self,
        params1: List[ParameterInfo],
        params2: List[ParameterInfo],
        extra_vars1: List[ExtraVariableInfo],
        extra_vars2: List[ExtraVariableInfo]
    ):
        """デバッグ情報を出力"""
        print("[FormulaBuilder] Function 1 parameters:")
        for p in params1:
            signed_str = "signed" if p.is_signed else "unsigned"
            semantic_str = ""
            if p.semantic_narrow_bits is not None and p.semantic_signedness:
                semantic_str = f", semantic={p.semantic_signedness}:{p.semantic_narrow_bits}"
            print(f"  {p.original_name} -> {p.smt_name} ({p.bit_width}bit, {signed_str}{semantic_str})")
        if extra_vars1:
            print("[FormulaBuilder] Function 1 extra variables:")
            for v in extra_vars1:
                status = ""
                if v.analysis:
                    status = f" [{v.analysis.classification.name}]"
                    if v.analysis.fragment_info:
                        ext_type = v.analysis.fragment_info.extension_type.name
                        parent = v.analysis.fragment_info.parent_param_name
                        status += f" -> {parent} ({ext_type})"
                print(f"  {v.original_name} -> {v.smt_name} ({v.bit_width}bit){status}")
        
        print("[FormulaBuilder] Function 2 parameters:")
        for p in params2:
            signed_str = "signed" if p.is_signed else "unsigned"
            semantic_str = ""
            if p.semantic_narrow_bits is not None and p.semantic_signedness:
                semantic_str = f", semantic={p.semantic_signedness}:{p.semantic_narrow_bits}"
            print(f"  {p.original_name} -> {p.smt_name} ({p.bit_width}bit, {signed_str}{semantic_str})")
        if extra_vars2:
            print("[FormulaBuilder] Function 2 extra variables:")
            for v in extra_vars2:
                status = ""
                if v.analysis:
                    status = f" [{v.analysis.classification.name}]"
                    if v.analysis.fragment_info:
                        ext_type = v.analysis.fragment_info.extension_type.name
                        parent = v.analysis.fragment_info.parent_param_name
                        status += f" -> {parent} ({ext_type})"
                print(f"  {v.original_name} -> {v.smt_name} ({v.bit_width}bit){status}")
    
    def _build_param_declarations(
        self,
        func_name: str,
        params: List[ParameterInfo]
    ) -> List[str]:
        """パラメータ宣言を構築"""
        lines = []
        lines.append("; " + "-" * 40)
        lines.append(f"; Parameters for {func_name}")
        lines.append("; (Bit widths from Ghidra analysis)")
        lines.append("; " + "-" * 40)
        for p in params:
            signed_comment = "signed" if p.is_signed else "unsigned"
            lines.append(f"; {p.smt_name}: {signed_comment}")
            lines.append(f"(declare-const {p.smt_name} (_ BitVec {p.bit_width}))")
        lines.append("")
        return lines

    def _build_memory_declarations(self, mem_widths: List[int]) -> List[str]:
        """共有メモリ配列の宣言を構築する。"""
        lines: List[str] = []
        lines.append("; " + "-" * 40)
        lines.append("; Shared memory arrays")
        lines.append("; Memory loads are modeled as array selects by bit width")
        lines.append("; " + "-" * 40)
        for bits in mem_widths:
            lines.append(
                f"(declare-const mem{bits} (Array (_ BitVec 64) (_ BitVec {bits})))"
            )
        lines.append("")
        return lines

    def _collect_memory_widths(
        self,
        *analyses: FunctionReturnAnalysis,
    ) -> List[int]:
        """SMT rendering inputsで使われるメモリ load 幅を収集する。"""
        widths = set()
        for analysis in analyses:
            if analysis is None:
                continue
            widths.update(collect_memory_bit_widths_from_analysis(analysis))
        return sorted(widths)
    
    def _build_extra_var_declarations(
        self,
        func_name: str,
        extra_vars: List[ExtraVariableInfo]
    ) -> List[str]:
        """追加変数宣言を構築"""
        lines = []
        lines.append("; " + "-" * 40)
        lines.append(f"; Extra variables for {func_name}")
        lines.append("; (Non-parameter variables found in expressions)")
        lines.append("; " + "-" * 40)
        for v in extra_vars:
            if v.analysis:
                comment = v.analysis.classification.name
                if v.analysis.reason:
                    comment += f": {v.analysis.reason}"
                lines.append(f"; {v.smt_name}: {comment}")
            lines.append(f"(declare-const {v.smt_name} (_ BitVec {v.bit_width}))")
        lines.append("")
        return lines

    def _collect_global_address_identities(
        self,
        *analyses: FunctionReturnAnalysis,
    ) -> List[Tuple[str, int]]:
        """Distinct named global objects addressed by either side (Issue #104)."""
        identities: List[Tuple[str, int]] = []

        def extend_from_expression(expr) -> None:
            for identity in collect_global_address_identities(expr):
                if identity not in identities:
                    identities.append(identity)

        for analysis in analyses:
            if analysis is None:
                continue
            for ret in getattr(analysis, "returns", []) or []:
                extend_from_expression(getattr(ret, "value", None))
                for condition in getattr(ret, "conditions", None) or []:
                    extend_from_expression(getattr(condition, "expression", None))
            effect_summary = getattr(analysis, "effect_summary", None)
            if effect_summary is not None:
                extend_from_expression(getattr(effect_summary, "synthetic_expr", None))
                for effect in getattr(effect_summary, "effects", []) or []:
                    extend_from_expression(getattr(effect, "value", None))
                    for condition in getattr(effect, "conditions", None) or []:
                        extend_from_expression(getattr(condition, "expression", None))
        return identities

    def _build_global_address_constraints(
        self,
        identities: List[Tuple[str, int]],
    ) -> List[str]:
        """Constraints on the shared base addresses of named global objects.

        The base symbols themselves are declared with the runtime unknown
        objects (they are replay targets).  Distinct objects occupy disjoint,
        non-wrapping, non-null byte ranges; nothing else is assumed, so
        parameter pointers may still alias a global exactly as before.
        """
        bits = GLOBAL_ADDRESS_BITS
        lines: List[str] = []
        lines.append("; " + "-" * 40)
        lines.append("; Named global objects (Issue #104)")
        lines.append("; Shared symbolic base addresses: same source object on both sides")
        lines.append("; " + "-" * 40)
        symbols = [(global_address_symbol_name((name, size, 0)), int(size), name) for name, size in identities]
        for symbol, size, name in symbols:
            lines.append(f"; {symbol}: {name} ({size} bytes)")
            lines.append(f"(assert (not (= {symbol} (_ bv0 {bits}))))")
            lines.append(f"(assert (bvult {symbol} (bvsub (_ bv{(1 << bits) - 1} {bits}) (_ bv{size} {bits}))))")
        for index, (left, left_size, _l) in enumerate(symbols):
            for right, right_size, _r in symbols[index + 1:]:
                lines.append(
                    "(assert (or "
                    f"(bvule (bvadd {left} (_ bv{left_size} {bits})) {right}) "
                    f"(bvule (bvadd {right} (_ bv{right_size} {bits})) {left})))"
                )
        lines.append("")
        return lines

    def _build_runtime_unknown_declarations(
        self,
        declarations: List[Tuple[str, int]],
    ) -> List[str]:
        lines: List[str] = []
        lines.append("; " + "-" * 40)
        lines.append("; Runtime UNKNOWN objects")
        lines.append("; Structured runtime identities lowered as deterministic SMT symbols")
        lines.append("; " + "-" * 40)
        for symbol_name, bit_width in declarations:
            lines.append(f"(declare-const {symbol_name} (_ BitVec {bit_width}))")
        lines.append("")
        return lines

    def _build_intrinsic_smt_declarations(
        self,
        declarations: List[str],
    ) -> List[str]:
        lines: List[str] = []
        lines.append("; " + "-" * 40)
        lines.append("; Intrinsic function declarations")
        lines.append("; Structured object-centric summaries lowered as SMT functions")
        lines.append("; " + "-" * 40)
        lines.extend(declarations)
        lines.append("")
        return lines

    def _build_float_predicate_smt_declarations(
        self,
        declarations: List[str],
    ) -> List[str]:
        lines: List[str] = []
        lines.append("; " + "-" * 40)
        lines.append("; Floating-point predicate declarations")
        lines.append("; Unsupported FLOAT_* widths fall back to uninterpreted Bool predicates.")
        lines.append("; " + "-" * 40)
        lines.extend(declarations)
        lines.append("")
        return lines

    def _build_loop_summary_smt_notes(
        self,
        notes: List[str],
    ) -> List[str]:
        lines: List[str] = []
        lines.append("; " + "-" * 40)
        lines.append("; Loop summary SMT identities")
        lines.append("; Method-B identities are canonicalized before declaration sharing")
        lines.append("; " + "-" * 40)
        lines.extend(notes)
        lines.append("")
        return lines

    def _build_readonly_reduction_witness_axioms_section(
        self,
        analysis_param_infos: Tuple[Tuple[FunctionReturnAnalysis, List[Any]], ...],
    ) -> List[str]:
        axioms: List[str] = []
        seen = set()
        for analysis, param_infos in analysis_param_infos:
            if analysis is None:
                continue
            symbol_name_mapping = build_symbol_name_mapping(param_infos)
            for expr, case_guards in self._iter_analysis_expressions_with_guards(analysis):
                for axiom in self._readonly_reduction_witness_axioms_for_expr(
                    expr,
                    symbol_name_mapping,
                    param_infos=param_infos,
                    case_guards=case_guards,
                ):
                    if axiom in seen:
                        continue
                    seen.add(axiom)
                    axioms.append(axiom)

        if not axioms:
            return []
        lines: List[str] = []
        lines.append("; " + "-" * 40)
        lines.append("; Readonly reduction finite witness axioms")
        lines.append("; Proof-backed READONLY_SUM values are tied to concrete memory terms for witnessed counts")
        lines.append("; " + "-" * 40)
        lines.extend(axioms)
        lines.append("")
        return lines

    def _iter_analysis_expressions_with_guards(self, analysis: FunctionReturnAnalysis):
        def visit(expr, guards=()):
            if expr is None:
                return
            guards = tuple(guard for guard in (guards or ()) if guard is not None)
            yield expr, guards
            if getattr(expr, "expr_type", None) == ExpressionType.PHI and getattr(expr, "value", None):
                for condition, value in expr.value:
                    if condition is not None:
                        yield from visit(getattr(condition, "expression", None), guards)
                        yield from visit(value, guards + (condition,))
                    else:
                        yield from visit(value, guards)
                return
            for operand in getattr(expr, "operands", []) or []:
                yield from visit(operand, guards)

        def visit_conditions(conditions):
            for condition in conditions or []:
                condition_guards = tuple(cond for cond in (conditions or ()) if cond is not None)
                yield from visit(getattr(condition, "expression", None), condition_guards)

        for ret in getattr(analysis, "returns", []) or []:
            return_guards = tuple(
                condition
                for condition in (getattr(ret, "conditions", None) or ())
                if condition is not None
            )
            yield from visit(getattr(ret, "value", None), return_guards)
            yield from visit_conditions(getattr(ret, "conditions", None))

        effect_summary = getattr(analysis, "effect_summary", None)
        if effect_summary is not None:
            yield from visit(getattr(effect_summary, "synthetic_expr", None))
            for effect in getattr(effect_summary, "effects", []) or []:
                effect_guards = tuple(
                    condition
                    for condition in (getattr(effect, "conditions", None) or ())
                    if condition is not None
                )
                yield from visit(getattr(effect, "value", None), effect_guards)
                yield from visit_conditions(getattr(effect, "conditions", None))

    def _readonly_reduction_witness_axioms_for_expr(
        self,
        expr,
        symbol_name_mapping,
        *,
        param_infos=(),
        case_guards=(),
    ) -> List[str]:
        if expr is None or getattr(expr, "expr_type", None) != ExpressionType.INTRINSIC:
            return []
        reduction_ref = getattr(expr, "runtime_ref", None)
        if not isinstance(reduction_ref, ReadonlyReductionRef):
            return []
        proof = getattr(reduction_ref, "accumulator_proof", None)
        if proof is None:
            return []
        operands = list(getattr(expr, "operands", []) or [])
        if len(operands) != 2:
            return []
        if not self._readonly_reduction_expr_operands_match_ref(expr, reduction_ref):
            return []

        base_expr, count_expr = operands
        result_bits = max(1, int(expression_smt_bit_width(expr) or 0))
        result_size = max(1, (result_bits + 7) // 8)
        count_bits = max(1, int(expression_smt_bit_width(count_expr) or 0))
        base_bits = max(1, int(expression_smt_bit_width(base_expr) or 0))
        function_application = expr.to_smt(symbol_name_mapping=symbol_name_mapping, float_mode="fp")
        count_smt = count_expr.to_smt(symbol_name_mapping=symbol_name_mapping, float_mode="fp")
        base_smt = base_expr.to_smt(symbol_name_mapping=symbol_name_mapping, float_mode="fp")
        base_addr_smt = self._coerce_smt_bitvec_width(base_smt, base_bits, 64)
        proof_guards = tuple(getattr(proof, "guard_constraints", ()) or ())
        loop_summary = getattr(reduction_ref, "loop_summary", None)
        loop_guards = tuple(getattr(loop_summary, "guard_constraints", ()) or ()) if loop_summary is not None else ()
        guard_terms = self._readonly_witness_guard_smt_terms(
            tuple(case_guards or ()) + proof_guards + loop_guards,
            symbol_name_mapping,
            param_infos=param_infos,
        )
        if guard_terms is None:
            return []

        axioms: List[str] = []
        for count_value in self._readonly_reduction_witness_counts(reduction_ref, proof):
            terms = self._readonly_terms_for_count(proof, reduction_ref, count_value)
            if terms is None:
                continue
            value_smt = self._readonly_terms_value_smt(
                base_addr_smt,
                terms,
                result_bits=result_bits,
                result_size=result_size,
                constant_bias=int(getattr(reduction_ref, "constant_bias", 0) or 0),
            )
            if value_smt is None:
                continue
            count_literal = self._bv_literal(count_value, count_bits)
            antecedent = self._readonly_witness_antecedent_smt(
                count_guard=f"(= {count_smt} {count_literal})",
                guard_terms=guard_terms,
            )
            axioms.append(
                f"(assert (=> {antecedent} "
                f"(= {function_application} {value_smt})))"
            )
        return axioms

    def _readonly_witness_guard_smt_terms(
        self,
        guards,
        symbol_name_mapping,
        *,
        param_infos=(),
    ) -> Optional[Tuple[str, ...]]:
        terms: List[str] = []
        seen = set()
        for guard in guards or ():
            term = self._readonly_guard_to_smt(
                guard,
                symbol_name_mapping,
                param_infos=param_infos,
            )
            if term is None:
                return None
            if term in {"", "true"} or term in seen:
                continue
            seen.add(term)
            terms.append(term)
        return tuple(terms)

    def _readonly_guard_to_smt(
        self,
        guard,
        symbol_name_mapping,
        *,
        param_infos=(),
    ) -> Optional[str]:
        if guard is None:
            return "true"
        if isinstance(guard, bool):
            return "true" if guard else "false"
        guard = _rewrite_guard_parameter_metadata_for_smt(guard, param_infos)
        to_smt = getattr(guard, "to_smt", None)
        if callable(to_smt):
            try:
                return str(to_smt(symbol_name_mapping=symbol_name_mapping, float_mode="fp"))
            except (AttributeError, TypeError, ValueError):
                return None
        expression = getattr(guard, "expression", None)
        if expression is not None:
            return self._readonly_guard_to_smt(
                expression,
                symbol_name_mapping,
                param_infos=param_infos,
            )
        return None

    def _readonly_witness_antecedent_smt(
        self,
        *,
        count_guard: str,
        guard_terms: Tuple[str, ...],
    ) -> str:
        terms = (count_guard,) + tuple(guard_terms or ())
        if len(terms) == 1:
            return terms[0]
        return f"(and {' '.join(terms)})"

    def _readonly_reduction_expr_operands_match_ref(
        self,
        expr,
        reduction_ref: ReadonlyReductionRef,
    ) -> bool:
        operands = list(getattr(expr, "operands", []) or [])
        if len(operands) != 2:
            return False
        base_expr, count_expr = operands
        return self._readonly_base_operand_matches_ref(
            base_expr,
            getattr(reduction_ref, "pointer_base_ref", None),
        ) and self._readonly_count_operand_matches_ref(count_expr, reduction_ref)

    def _readonly_base_operand_matches_ref(
        self,
        expr,
        pointer_ref,
    ) -> bool:
        if pointer_ref is None:
            return False
        is_parameter = getattr(pointer_ref, "is_parameter", None)
        if callable(is_parameter) and is_parameter():
            parameter_index = getattr(pointer_ref, "parameter_index", None)
            if parameter_index is None:
                return False
            expr_index = self._expression_parameter_index_through_width_views(expr)
            if expr_index is None:
                return False
            try:
                return int(expr_index) == int(parameter_index)
            except (TypeError, ValueError):
                return False
        is_storage = getattr(pointer_ref, "is_storage", None)
        if callable(is_storage) and is_storage():
            ref_storage_key = getattr(pointer_ref, "storage_identity_key", None)
            if ref_storage_key is None:
                return False
            expr_storage_key = self._expression_storage_identity_through_width_views(expr)
            return expr_storage_key is not None and tuple(expr_storage_key) == tuple(ref_storage_key)
        return False

    def _readonly_count_operand_matches_ref(
        self,
        expr,
        reduction_ref: ReadonlyReductionRef,
    ) -> bool:
        count_storage_key = getattr(reduction_ref, "count_parameter_storage_identity_key", None)
        ref_storage_key = tuple(count_storage_key) if count_storage_key is not None else None
        count_index = getattr(reduction_ref, "count_parameter_index", None)
        ref_index = None
        try:
            if count_index is not None and int(count_index) >= 0:
                ref_index = int(count_index)
        except (TypeError, ValueError):
            pass

        expr_storage_key = self._expression_storage_identity_through_width_views(expr)
        if expr_storage_key is not None:
            expr_storage_key = tuple(expr_storage_key)
        if ref_storage_key is not None and expr_storage_key is not None:
            return ref_storage_key == expr_storage_key

        expr_index = self._expression_parameter_index_through_width_views(expr)
        normalized_expr_index = None
        try:
            if expr_index is not None and int(expr_index) >= 0:
                normalized_expr_index = int(expr_index)
        except (TypeError, ValueError):
            pass
        if ref_storage_key is not None or expr_storage_key is not None:
            return (
                ref_index is not None
                and normalized_expr_index is not None
                and ref_index == normalized_expr_index
            )
        return ref_index is not None and normalized_expr_index is not None and ref_index == normalized_expr_index

    def _expression_parameter_index_through_width_views(self, expr) -> Optional[int]:
        if expr is None:
            return None
        if getattr(expr, "expr_type", None) == ExpressionType.PARAMETER:
            index = getattr(expr, "value", None)
            try:
                return int(index) if index is not None and int(index) >= 0 else None
            except (TypeError, ValueError):
                return None
        if getattr(expr, "expr_type", None) == ExpressionType.UNARY_OP and getattr(expr, "operator", None) in {
            "CAST",
            "COPY",
            "INT_ZEXT",
            "INT_SEXT",
        }:
            operands = list(getattr(expr, "operands", []) or [])
            if len(operands) == 1:
                return self._expression_parameter_index_through_width_views(operands[0])
        if getattr(expr, "expr_type", None) == ExpressionType.BINARY_OP and getattr(expr, "operator", None) == "SUBPIECE":
            operands = list(getattr(expr, "operands", []) or [])
            if len(operands) == 2 and getattr(operands[1], "expr_type", None) == ExpressionType.CONSTANT:
                try:
                    if int(getattr(operands[1], "value", 0) or 0) == 0:
                        return self._expression_parameter_index_through_width_views(operands[0])
                except (TypeError, ValueError):
                    return None
        return None

    def _expression_storage_identity_through_width_views(self, expr) -> Optional[Tuple[Any, ...]]:
        if expr is None:
            return None
        storage_info = getattr(expr, "storage_info", None)
        storage_key_fn = getattr(storage_info, "storage_identity_key", None)
        if callable(storage_key_fn):
            try:
                storage_key = storage_key_fn()
            except (AttributeError, TypeError, ValueError):
                storage_key = None
            if storage_key is not None:
                return tuple(storage_key)
        if getattr(expr, "expr_type", None) == ExpressionType.UNARY_OP and getattr(expr, "operator", None) in {
            "CAST",
            "COPY",
            "INT_ZEXT",
            "INT_SEXT",
        }:
            operands = list(getattr(expr, "operands", []) or [])
            if len(operands) == 1:
                return self._expression_storage_identity_through_width_views(operands[0])
        if getattr(expr, "expr_type", None) == ExpressionType.BINARY_OP and getattr(expr, "operator", None) == "SUBPIECE":
            operands = list(getattr(expr, "operands", []) or [])
            if len(operands) == 2 and getattr(operands[1], "expr_type", None) == ExpressionType.CONSTANT:
                try:
                    if int(getattr(operands[1], "value", 0) or 0) == 0:
                        return self._expression_storage_identity_through_width_views(operands[0])
                except (TypeError, ValueError):
                    return None
        return None

    def _readonly_reduction_witness_counts(self, reduction_ref, proof) -> Tuple[int, ...]:
        counts = set()
        for witnesses in (
            getattr(reduction_ref, "semantic_witnesses", ()) or (),
            getattr(proof, "loop_body_witnesses", ()) or (),
            getattr(proof, "exact_return_witnesses", ()) or (),
        ):
            for witness in witnesses:
                try:
                    count_value = int(getattr(witness, "exact_count", 0) or 0)
                except (TypeError, ValueError):
                    count_value = 0
                if 0 < count_value <= 16:
                    counts.add(count_value)

        try:
            start_index = max(0, int(getattr(proof, "start_index", 0) or 0))
        except (TypeError, ValueError):
            start_index = 0
        seed_terms = tuple(getattr(proof, "seed_terms", ()) or ())
        try:
            seed_count = int(getattr(proof, "seed_term_count", 0) or 0)
        except (TypeError, ValueError):
            seed_count = 0
        materialization_bound = min(16, max(4, start_index + max(len(seed_terms), seed_count) + 4, *(counts or {0})))
        for count_value in range(1, materialization_bound + 1):
            if proof.full_terms_for_count_value(count_value) is not None:
                counts.add(count_value)
        return tuple(sorted(counts))

    def _readonly_terms_for_count(self, proof, reduction_ref, count_value: int):
        try:
            terms = proof.full_terms_for_count_value(int(count_value))
        except (AttributeError, TypeError, ValueError):
            terms = None
        if terms is not None:
            return tuple(terms)
        for witnesses in (
            getattr(reduction_ref, "semantic_witnesses", ()) or (),
            getattr(proof, "loop_body_witnesses", ()) or (),
            getattr(proof, "exact_return_witnesses", ()) or (),
        ):
            for witness in witnesses:
                try:
                    witness_count = int(getattr(witness, "exact_count", 0) or 0)
                except (TypeError, ValueError):
                    continue
                if witness_count == int(count_value):
                    return tuple(getattr(witness, "terms", ()) or ())
        return None

    def _readonly_terms_value_smt(
        self,
        base_addr_smt: str,
        terms,
        *,
        result_bits: int,
        result_size: int,
        constant_bias: int,
    ) -> Optional[str]:
        result_bits = max(1, int(result_bits))
        total = None
        for term in terms or ():
            try:
                byte_offset = int(getattr(term, "byte_offset"))
                access_size = max(1, int(getattr(term, "access_size", 0) or 0))
            except (TypeError, ValueError):
                return None
            access_bits = access_size * 8
            address_smt = base_addr_smt
            if byte_offset:
                address_smt = f"(bvadd {base_addr_smt} {self._bv_literal(byte_offset, 64)})"
            load_smt = f"(select mem{access_bits} {address_smt})"
            load_smt = self._coerce_smt_bitvec_width(load_smt, access_bits, result_bits)
            total = load_smt if total is None else f"(bvadd {total} {load_smt})"
        if total is None:
            total = self._bv_literal(0, result_bits)
        bias = self._normalize_unsigned_value(constant_bias, result_size * 8)
        if bias:
            total = f"(bvadd {total} {self._bv_literal(bias, result_bits)})"
        return total

    def _coerce_smt_bitvec_width(self, value_smt: str, source_bits: int, target_bits: int) -> str:
        source_bits = max(1, int(source_bits))
        target_bits = max(1, int(target_bits))
        if source_bits == target_bits:
            return value_smt
        if source_bits < target_bits:
            return f"((_ zero_extend {target_bits - source_bits}) {value_smt})"
        return f"((_ extract {target_bits - 1} 0) {value_smt})"

    def _bv_literal(self, value: int, bits: int) -> str:
        bits = max(1, int(bits))
        return f"(_ bv{self._normalize_unsigned_value(value, bits)} {bits})"

    def _normalize_unsigned_value(self, value: int, bits: int) -> int:
        bits = max(1, int(bits))
        return int(value) & ((1 << bits) - 1)

    def _collect_runtime_unknown_declarations(
        self,
        *analyses: FunctionReturnAnalysis,
    ) -> List[Tuple[str, int]]:
        declarations: List[Tuple[str, int]] = []
        seen = set()

        def extend_from_expression(expr) -> None:
            for decl in collect_unknown_smt_declarations(expr):
                if decl in seen:
                    continue
                seen.add(decl)
                declarations.append(decl)

        def extend_from_conditions(conditions) -> None:
            for condition in conditions or []:
                extend_from_expression(getattr(condition, "expression", None))

        for analysis in analyses:
            if analysis is None:
                continue
            for ret in getattr(analysis, "returns", []) or []:
                extend_from_expression(getattr(ret, "value", None))
                extend_from_conditions(getattr(ret, "conditions", None))

            effect_summary = getattr(analysis, "effect_summary", None)
            if effect_summary is not None:
                extend_from_expression(getattr(effect_summary, "synthetic_expr", None))
                for effect in getattr(effect_summary, "effects", []) or []:
                    extend_from_expression(getattr(effect, "value", None))
                    extend_from_conditions(getattr(effect, "conditions", None))

            for deferred in (getattr(analysis, "deferred_calls", None) or {}).values():
                extend_from_expression(getattr(deferred, "call_target_expr", None))
                for arg in getattr(deferred, "arguments", []) or []:
                    extend_from_expression(arg)

        return declarations

    def _collect_call_smt_declarations(
        self,
        *analyses: FunctionReturnAnalysis,
    ) -> List[str]:
        """conditional lane でだけ CALL の UF 宣言を集める。

        無条件 lane (``allow_call=False``) では常に空を返すので、既存 formula の
        出力は 1 バイトも変わらない。宣言規則は condition SMT oracle と共有の
        ``core/render_smt`` helper が唯一の実装で、同名の CALL に別 signature が
        要求されたら silent rename せず :class:`CallFormulaUnsupported` を送出する。
        """

        if not self.allow_call:
            return []
        declarations: Dict[str, Tuple[Tuple[int, ...], int]] = {}
        for analysis in analyses:
            if analysis is None:
                continue
            for expr, guards in self._iter_analysis_expressions_with_guards(analysis):
                for candidate_expr in (expr, *(
                    getattr(guard, "expression", guard) for guard in guards or ()
                )):
                    try:
                        collected = collect_call_smt_declarations(candidate_expr, declarations)
                    except CallDeclarationConflict as conflict:
                        raise CallFormulaUnsupported(str(conflict)) from conflict
                    if collected is None:
                        raise CallFormulaUnsupported(
                            "a CALL application has no usable SMT signature"
                        )
        return call_smt_declaration_lines(declarations)

    def _build_call_smt_declarations(
        self,
        declarations: List[str],
    ) -> List[str]:
        lines: List[str] = []
        lines.append("; " + "-" * 40)
        lines.append("; Conditional external call declarations")
        lines.append("; Catalog-modelled calls lowered as uninterpreted SMT functions")
        lines.append("; " + "-" * 40)
        lines.extend(declarations)
        lines.append("")
        return lines

    def _collect_intrinsic_smt_declarations(
        self,
        *analyses: FunctionReturnAnalysis,
    ) -> List[str]:
        declarations: List[str] = []
        seen = set()

        def extend_from_expression(expr) -> None:
            for decl in collect_intrinsic_smt_declarations(expr):
                if decl in seen:
                    continue
                seen.add(decl)
                declarations.append(decl)

        def extend_from_conditions(conditions) -> None:
            for condition in conditions or []:
                extend_from_expression(getattr(condition, "expression", None))

        for analysis in analyses:
            if analysis is None:
                continue
            for ret in getattr(analysis, "returns", []) or []:
                extend_from_expression(getattr(ret, "value", None))
                extend_from_conditions(getattr(ret, "conditions", None))

            effect_summary = getattr(analysis, "effect_summary", None)
            if effect_summary is not None:
                extend_from_expression(getattr(effect_summary, "synthetic_expr", None))
                for effect in getattr(effect_summary, "effects", []) or []:
                    extend_from_expression(getattr(effect, "value", None))
                    extend_from_conditions(getattr(effect, "conditions", None))

        return declarations

    def _collect_float_predicate_smt_declarations(
        self,
        *analyses: FunctionReturnAnalysis,
    ) -> List[str]:
        declarations: List[str] = []
        seen = set()

        def extend_from_expression(expr) -> None:
            for decl in collect_float_predicate_smt_declarations(expr, float_mode="fp"):
                if decl in seen:
                    continue
                seen.add(decl)
                declarations.append(decl)

        def extend_from_conditions(conditions) -> None:
            for condition in conditions or []:
                extend_from_expression(getattr(condition, "expression", None))

        for analysis in analyses:
            if analysis is None:
                continue
            for ret in getattr(analysis, "returns", []) or []:
                extend_from_expression(getattr(ret, "value", None))
                extend_from_conditions(getattr(ret, "conditions", None))

            effect_summary = getattr(analysis, "effect_summary", None)
            if effect_summary is not None:
                extend_from_expression(getattr(effect_summary, "synthetic_expr", None))
                for effect in getattr(effect_summary, "effects", []) or []:
                    extend_from_expression(getattr(effect, "value", None))
                    extend_from_conditions(getattr(effect, "conditions", None))

            for deferred in (getattr(analysis, "deferred_calls", None) or {}).values():
                extend_from_expression(getattr(deferred, "call_target_expr", None))
                for arg in getattr(deferred, "arguments", []) or []:
                    extend_from_expression(arg)

        return declarations

    def _collect_loop_summary_smt_notes(
        self,
        *analyses: FunctionReturnAnalysis,
    ) -> List[str]:
        notes: List[str] = []
        seen = set()

        def extend_from_expression(expr) -> None:
            if expr is None or getattr(expr, "expr_type", None) is None:
                return
            expr_kind = expr.expr_type.__class__
            if expr.expr_type == expr_kind.INTRINSIC:
                runtime_ref = getattr(expr, "runtime_ref", None)
                loop_summary = getattr(runtime_ref, "loop_summary", None)
                if loop_summary is not None:
                    note = self._loop_summary_smt_note(expr, runtime_ref, loop_summary)
                    if note not in seen:
                        seen.add(note)
                        notes.append(note)
            if expr.expr_type == expr_kind.PHI and getattr(expr, "value", None):
                for condition, value in expr.value:
                    if condition is not None:
                        extend_from_expression(getattr(condition, "expression", None))
                    extend_from_expression(value)
                return
            for operand in getattr(expr, "operands", []) or []:
                extend_from_expression(operand)

        def extend_from_conditions(conditions) -> None:
            for condition in conditions or []:
                extend_from_expression(getattr(condition, "expression", None))

        for analysis in analyses:
            if analysis is None:
                continue
            for ret in getattr(analysis, "returns", []) or []:
                extend_from_expression(getattr(ret, "value", None))
                extend_from_conditions(getattr(ret, "conditions", None))

            effect_summary = getattr(analysis, "effect_summary", None)
            if effect_summary is not None:
                extend_from_expression(getattr(effect_summary, "synthetic_expr", None))
                for effect in getattr(effect_summary, "effects", []) or []:
                    extend_from_expression(getattr(effect, "value", None))
                    extend_from_conditions(getattr(effect, "conditions", None))

        return notes

    def _loop_summary_smt_note(
        self,
        expr,
        runtime_ref,
        loop_summary,
    ) -> str:
        method_b_key = loop_summary_method_b_key(loop_summary)
        if method_b_key is not None:
            digest = hashlib.sha1(repr(method_b_key).encode("utf-8")).hexdigest()[:12]
            status = f"method_b:{digest}"
        else:
            requires_effect_proof = getattr(loop_summary, "requires_effect_proof", None)
            requires_path_proof = getattr(loop_summary, "requires_path_proof", None)
            try:
                stable_key = getattr(loop_summary, "stable_key", lambda: None)()
            except (AttributeError, TypeError, ValueError):
                stable_key = None
            if callable(requires_effect_proof) and requires_effect_proof():
                status = "opaque:effect_proof_required"
            elif callable(requires_path_proof) and requires_path_proof():
                status = "opaque:path_proof_required"
            elif stable_key is None:
                status = "opaque:unkeyable"
            else:
                digest = hashlib.sha1(repr(stable_key).encode("utf-8")).hexdigest()[:12]
                status = f"stable:{digest}"
        intrinsic_name = getattr(expr, "name", None) or "INTRINSIC"
        runtime_name = type(runtime_ref).__qualname__
        return f"; loop-summary {intrinsic_name} {runtime_name} {status}"
    
    def _build_param_constraints_section(
        self,
        param_pairs: List[ParameterPair],
        analyses1: Dict[str, ExtraVariableAnalysis],
        analyses2: Dict[str, ExtraVariableAnalysis],
    ) -> List[str]:
        """パラメータ制約セクションを構築"""
        lines = []
        lines.append("; " + "-" * 40)
        lines.append("; Parameter equality constraints")
        lines.append("; For matching bit widths: direct equality unless semantic narrowing is inferred")
        lines.append("; For different bit widths: overlapping bits equal, upper bits free")
        lines.append("; " + "-" * 40)

        fragments1 = collect_fragment_infos_by_param_index(analyses1)
        fragments2 = collect_fragment_infos_by_param_index(analyses2)
        for pair in param_pairs:
            fragment_constraint_lines = self._build_fragment_backed_parameter_constraint(
                pair,
                fragments1,
                fragments2,
            )
            if fragment_constraint_lines:
                lines.extend(fragment_constraint_lines)
                continue
            constraint_lines = self._build_parameter_constraint(pair)
            lines.extend(constraint_lines)
        
        lines.append("")
        return lines

    def _build_param_semantic_constraints_section(
        self,
        params1: List[ParameterInfo],
        params2: List[ParameterInfo],
    ) -> List[str]:
        """パラメータの意味幅整合制約を構築"""
        lines = build_parameter_semantic_constraints(params1)
        lines.extend(build_parameter_semantic_constraints(params2))
        if not lines:
            return []

        return [
            "; " + "-" * 40,
            "; Parameter semantic-width constraints",
            "; Constrain parameters that are used as narrower integers",
            "; " + "-" * 40,
            *lines,
            "",
        ]

    def _apply_semantic_hints(
        self,
        params: List[ParameterInfo],
        hints: Dict[int, Any],
    ) -> None:
        """Attach inferred semantic-width hints to parameter metadata."""
        params_by_index = {param.index: param for param in params}
        for index, hint in hints.items():
            param = params_by_index.get(index)
            if param is None:
                continue
            param.semantic_narrow_bits = hint.narrow_bits
            param.semantic_signedness = (
                hint.signedness
                if hint.signedness_source == "explicit" and hint.signedness in {"signed", "unsigned"}
                else None
            )
    
    def _build_extra_var_constraints(
        self,
        extra_vars1: List[ExtraVariableInfo],
        extra_vars2: List[ExtraVariableInfo],
        analyses1: Dict[str, ExtraVariableAnalysis],
        analyses2: Dict[str, ExtraVariableAnalysis],
        suffix1: str,
        suffix2: str
    ) -> Tuple[List[str], List[str]]:
        """
        追加変数の制約を構築
        
        パラメータ断片として識別された変数には sign/zero extension 制約を適用
        
        Returns:
            (制約行のリスト, 制約された変数名のリスト)
        """
        lines = []
        constrained_vars = []
        
        # パラメータ断片の制約を生成
        fragment_lines1, fragment_vars1 = get_parameter_fragment_constraints(analyses1, suffix1)
        fragment_lines2, fragment_vars2 = get_parameter_fragment_constraints(analyses2, suffix2)
        
        if fragment_lines1 or fragment_lines2:
            lines.append("; " + "-" * 40)
            lines.append("; Parameter fragment constraints")
            lines.append("; Upper-bits variables constrained via sign/zero extension")
            lines.append("; " + "-" * 40)
            
            if fragment_lines1:
                lines.append("; Function 1 fragments:")
                lines.extend(fragment_lines1)
            
            if fragment_lines2:
                lines.append("; Function 2 fragments:")
                lines.extend(fragment_lines2)
            
            lines.append("")
            constrained_vars.extend(fragment_vars1)
            constrained_vars.extend(fragment_vars2)
        
        return lines, constrained_vars
    
    def _merge_param_and_extra_vars(
        self,
        params: List[ParameterInfo],
        extra_vars: List[ExtraVariableInfo]
    ) -> List[ParameterInfo]:
        """パラメータと追加変数を統合"""
        return merge_param_and_extra_vars(params, extra_vars)
    
    def _build_equivalence_assertion(
        self,
        return_var1: str,
        return_var2: str,
        return_size1: int,
        return_size2: int,
        *,
        canonical_return_observation_width: Optional[int] = None,
    ) -> List[str]:
        """等価性アサートを構築"""
        lines = []
        lines.append("; " + "-" * 40)
        lines.append("; Equivalence assertion (negated)")
        lines.append("; If SAT: functions are NOT equivalent")
        lines.append("; If UNSAT: functions ARE equivalent")
        lines.append("; " + "-" * 40)
        
        try:
            require_equal_return_bit_widths(
                return_size1,
                return_size2,
                context="monolithic return equivalence assertion",
            )
        except ReturnWidthMismatchError:
            narrow_bits = self._validated_canonical_return_observation_width(
                return_size1,
                return_size2,
                canonical_return_observation_width,
            )
            if narrow_bits is None:
                raise
            left = self._canonical_return_observation_term(
                return_var1,
                return_size1,
                narrow_bits,
            )
            right = self._canonical_return_observation_term(
                return_var2,
                return_size2,
                narrow_bits,
            )
            lines.append(
                "; Canonical return observation: compare on proven observation width"
            )
            lines.append(f"; Canonical observation width: {narrow_bits}")
            lines.append(f"(assert (not (= {left} {right})))")
            return lines

        lines.append(f"(assert (not (= {return_var1} {return_var2})))")
        
        return lines

    @staticmethod
    def _validated_canonical_return_observation_width(
        return_size1: int,
        return_size2: int,
        narrow_bits: Optional[int],
    ) -> Optional[int]:
        try:
            bits1 = int(return_size1)
            bits2 = int(return_size2)
            candidate = int(narrow_bits or 0)
        except (TypeError, ValueError):
            return None
        if bits1 <= 0 or bits2 <= 0 or bits1 == bits2:
            return None
        if candidate <= 0 or candidate != min(bits1, bits2):
            return None
        return candidate

    @staticmethod
    def _canonical_return_observation_term(
        return_var: str,
        return_bits: int,
        narrow_bits: int,
    ) -> str:
        if int(return_bits) == int(narrow_bits):
            return return_var
        return f"((_ extract {int(narrow_bits) - 1} 0) {return_var})"
    
    def _collect_param_info(
        self,
        params: List[Dict],
        suffix: str
    ) -> List[ParameterInfo]:
        """パラメータ情報を収集"""
        return collect_param_info(params, suffix)
    
    def _build_parameter_pairs(
        self,
        params1: List[ParameterInfo],
        params2: List[ParameterInfo]
    ) -> List[ParameterPair]:
        """パラメータペアを構築"""
        return build_parameter_pairs(params1, params2)
    
    def _build_parameter_constraint(self, pair: ParameterPair) -> List[str]:
        """
        パラメータ間の制約を構築
        
        - 同じビット幅: 直接等価
        - 異なるビット幅: 重複するビット（下位ビット）のみ等価、上位ビットは自由
        """
        return build_parameter_constraint(pair)

    def _build_fragment_backed_parameter_constraint(
        self,
        pair: ParameterPair,
        fragments1: Dict[int, Any],
        fragments2: Dict[int, Any],
    ) -> Optional[List[str]]:
        return build_fragment_backed_parameter_constraint(
            pair,
            fragments1.get(pair.index),
            fragments2.get(pair.index),
        )
    
    def _get_return_size(self, analysis: FunctionReturnAnalysis) -> int:
        """return値のビット幅を取得"""
        return get_return_size(analysis)
    
    def _build_return_definition(
        self,
        analysis: FunctionReturnAnalysis,
        return_var_name: str,
        param_infos: List[ParameterInfo]
    ) -> List[str]:
        """
        return値の定義を構築
        
        全てのreturn定義の条件を反映したite式を生成
        """
        return build_return_definition(analysis, return_var_name, param_infos)
    
    def _build_ite_expression(self, return_defs: List[dict], return_size: int) -> str:
        """
        ite式を構築（全ての条件を反映）
        
        Args:
            return_defs: 条件と値のペアのリスト
            return_size: 戻り値のビット幅
        
        Returns:
            SMT-LIBのite式
        
        修正内容:
            - 全てのreturn定義の条件を必ず反映
            - どの条件にも該当しない場合のデフォルト値を追加
        """
        from scripts.function_tracer_pcode.proof.formula.returns import build_ite_expression

        return build_ite_expression(return_defs, return_size)
    
    def build_abi_constraints(
        self,
        abi_constraints: Dict[str, Tuple[str, int]],
        func1_suffix: str = "_1",
        func2_suffix: str = "_2"
    ) -> List[str]:
        """
        ABI整合制約のassert文リストを生成
        
        Args:
            abi_constraints: {"param0_1": ("signed", 32), ...}
                - key: 64bitパラメータ名（wide側、サフィックス付き）
                - value: (signedness, narrow_bits) タプル
            func1_suffix, func2_suffix: サフィックス
        
        Returns:
            SMT-LIB assert文のリスト（コメント含む）
        
        制約の意味:
            wide_param = sign/zero_extend(opposite_suffix_narrow_param)
            例: param0_1 (64bit) = sign_extend(param0_2 (32bit))
        """
        lines = []
        
        for param_wide, (signedness, narrow_bits) in abi_constraints.items():
            # 対応する狭いパラメータ名を推定（サフィックスを反転）
            if param_wide.endswith(func1_suffix):
                param_narrow = param_wide[:-len(func1_suffix)] + func2_suffix
            elif param_wide.endswith(func2_suffix):
                param_narrow = param_wide[:-len(func2_suffix)] + func1_suffix
            else:
                if self.debug:
                    print(f"[FormulaBuilder] Warning: Cannot determine narrow param for {param_wide}")
                continue
            
            source_expr = param_narrow
            if narrow_bits < 64:
                source_expr = f"((_ extract {narrow_bits - 1} 0) {param_narrow})"

            # 拡張ビット数
            extend_bits = 64 - narrow_bits
            
            # 制約を生成
            if extend_bits <= 0:
                comment = f"; {param_wide} must match lower {narrow_bits} bits of {param_narrow}"
                constraint = f"(assert (= {param_wide} {source_expr}))"
            elif signedness == "signed":
                comment = f"; {param_wide} must be sign-extension of lower {narrow_bits} bits of {param_narrow}"
                constraint = f"(assert (= {param_wide} ((_ sign_extend {extend_bits}) {source_expr})))"
            else:
                comment = f"; {param_wide} must be zero-extension of lower {narrow_bits} bits of {param_narrow}"
                constraint = f"(assert (= {param_wide} ((_ zero_extend {extend_bits}) {source_expr})))"
            
            lines.append(comment)
            lines.append(constraint)
        
        return lines
    
    def build_abi_assertion_section(
        self,
        abi_constraints: Dict[str, Tuple[str, int]],
        func1_suffix: str = "_1",
        func2_suffix: str = "_2"
    ) -> List[str]:
        """
        ABI整合制約セクション全体を生成（ヘッダ付き）
        
        Args:
            abi_constraints: ABI制約マップ
            func1_suffix, func2_suffix: サフィックス
        
        Returns:
            セクション全体の行リスト（ヘッダ + 制約）
            空の場合は空リスト
        """
        if not abi_constraints:
            return []
        
        lines = []
        lines.append("; " + "-" * 40)
        lines.append("; MIPS64 ABI constraints (sign/zero extension)")
        lines.append("; " + "-" * 40)
        lines.extend(
            self.build_abi_constraints(abi_constraints, func1_suffix, func2_suffix)
        )
        
        return lines

    # ★ MODIFIED: build_with_abi_constraints のコメント修正
    def build_with_abi_constraints(
        self,
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
        abi_constraints: Dict[str, Tuple[str, int]],
        func1_suffix: str = "_1",
        func2_suffix: str = "_2"
    ) -> str:
        """
        ABI整合制約を追加したSMT式を構築（後方互換性のためのラッパー）
        
        Args:
            analysis1, analysis2: 各バイナリの関数解析結果
            abi_constraints: {"param0_1": ("signed", 32), ...}
            func1_suffix, func2_suffix: サフィックス
        
        Returns:
            SMT-LIB script
        """
        # ★ 新しい helper を使用（セクション化の知識を一元化）
        abi_assertion_section = self.build_abi_assertion_section(
            abi_constraints, func1_suffix, func2_suffix
        )
        
        result = self.build_equivalence_formula_extended(
            analysis1, analysis2,
            func1_suffix, func2_suffix,
            extra_assertions=abi_assertion_section if abi_assertion_section else None
        )
        
        return result.formula
    
    def build_base_context(
        self,
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
        func1_suffix: str = "_1",
        func2_suffix: str = "_2"
    ) -> Dict[str, Any]:
        """
        Pairwise戦略用の共通SMT部分を生成
        
        Returns:
            {
                'header_lines': List[str],  # パラメータ宣言・制約のSMT行
                'params1': List[ParameterInfo],
                'params2': List[ParameterInfo],
                'extra_vars1': List[ExtraVariableInfo],
                'extra_vars2': List[ExtraVariableInfo],
            'constrained_fragments': List[str],
            'return_size1': int,
            'return_size2': int,
            'smt_logic': str,
        }
        """
        analysis1, analysis2, _, _ = self._normalize_analyses(analysis1, analysis2)
        context = self._prepare_formula_context(
            analysis1, analysis2, func1_suffix, func2_suffix
        )

        return {
            'header_lines': context.header_lines,
            'params1': context.params1,
            'params2': context.params2,
            'extra_vars1': context.extra_vars1,
            'extra_vars2': context.extra_vars2,
            'runtime_unknown_declarations': context.runtime_unknown_declarations,
            'constrained_fragments': context.constrained_fragments,
            'return_size1': context.return_size1,
            'return_size2': context.return_size2,
            'smt_logic': context.smt_logic,
            'return_coverage_domain_assumptions': {
                'fp_non_nan': self._has_fp_non_nan_domain_assumptions(
                    analysis1,
                    analysis2,
                    context.params1,
                    context.params2,
                ),
            },
        }

# -*- coding: utf-8 -*-
"""SMT式構築モジュール"""

import hashlib
from typing import List, Dict, Optional, Tuple, Set, Any

from ...model import (
    ExpressionType,
    FunctionReturnAnalysis,
    ReadonlyReductionRef,
    loop_summary_method_b_key,
)
from ...model.render_smt import (
    collect_intrinsic_smt_declarations,
    collect_unknown_smt_declarations,
    expression_smt_bit_width,
)
from .params import (
    build_fragment_backed_parameter_constraint,
    collect_fragment_infos_by_param_index,
    build_parameter_constraint,
    build_parameter_semantic_constraints,
    build_parameter_pairs,
    build_symbol_name_mapping,
    collect_param_info,
    merge_param_and_extra_vars,
)
from .returns import build_return_definition, get_return_size, require_equal_return_bit_widths
from ..param_semantics import infer_parameter_semantics
from ..semantic_width import (
    align_return_value_extension_surfaces,
    normalize_analysis_semantic_width,
    return_extension_surface_evidence_key,
)
from .types import (
    ExtraVariableInfo,
    FormulaBuildContext,
    FormulaBuilderResult,
    ParameterInfo,
    ParameterPair,
)
from .variable import (
    VariableAnalyzer, 
    ExtraVariableAnalysis, 
    VariableClassification,
    get_parameter_fragment_constraints
)
from .symbol_replace import build_symbol_replacer
from ...analysis.memory_resolver import collect_memory_bit_widths_from_analysis

from ..ub.constraints import UbConstraintBuilder


class FormulaBuilder:
    """2つの関数解析結果からSMT式を構築"""
    
    def __init__(self, debug: bool = False, exclude_ub: bool = True):
        """
        Args:
            debug: デバッグ出力を有効にする
            exclude_ub: UB（未定義動作）除外制約を追加する
        """
        self.debug = debug
        self.exclude_ub = exclude_ub
        self.variable_analyzer = VariableAnalyzer(debug=debug)
        self.ub_constraint_builder = UbConstraintBuilder(debug=debug)
    
    def build_equivalence_formula(
        self,
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
        func1_suffix: str = "_1",
        func2_suffix: str = "_2",
        extra_assertions: Optional[List[str]] = None  # ★ NEW
    ) -> Tuple[str, str, str]:
        """
        2つの関数の等価性検証用SMT式を構築
        
        Args:
            analysis1, analysis2: 各関数の解析結果
            func1_suffix, func2_suffix: サフィックス
            extra_assertions: 追加のアサート文（(check-sat)の直前に挿入）
        
        Returns:
            (smt_formula, return_var1, return_var2)
        """
        result = self.build_equivalence_formula_extended(
            analysis1, analysis2, func1_suffix, func2_suffix,
            extra_assertions=extra_assertions  # ★ NEW
        )
        return result.formula, result.return_var1, result.return_var2
    
    def build_equivalence_formula_extended(
        self,
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
        func1_suffix: str = "_1",
        func2_suffix: str = "_2",
        extra_assertions: Optional[List[str]] = None  # ★ NEW
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
        lines.append("(set-logic QF_BV)")
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

        intrinsic_decls = self._collect_intrinsic_smt_declarations(
            *declaration_analyses,
        )
        if intrinsic_decls:
            lines.extend(self._build_intrinsic_smt_declarations(intrinsic_decls))

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

        active_return_bits = self._active_return_comparison_bits(analysis1, analysis2)
        readonly_contract_axioms = self._build_readonly_reduction_contract_axioms_section(
            (
                (
                    render_declaration_analysis1,
                    self._merge_param_and_extra_vars(params1, extra_vars1),
                ),
                (
                    render_declaration_analysis2,
                    self._merge_param_and_extra_vars(params2, extra_vars2),
                ),
            ),
            active_return_bits=active_return_bits,
        )
        if readonly_contract_axioms:
            lines.extend(readonly_contract_axioms)

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

        return lines, runtime_unknown_decls, constrained_fragments, param_fragment_constrained
    
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
        print(f"[FormulaBuilder] Function 1 parameters:")
        for p in params1:
            signed_str = "signed" if p.is_signed else "unsigned"
            semantic_str = ""
            if p.semantic_narrow_bits is not None and p.semantic_signedness:
                semantic_str = f", semantic={p.semantic_signedness}:{p.semantic_narrow_bits}"
            print(f"  {p.original_name} -> {p.smt_name} ({p.bit_width}bit, {signed_str}{semantic_str})")
        if extra_vars1:
            print(f"[FormulaBuilder] Function 1 extra variables:")
            for v in extra_vars1:
                status = ""
                if v.analysis:
                    status = f" [{v.analysis.classification.name}]"
                    if v.analysis.fragment_info:
                        ext_type = v.analysis.fragment_info.extension_type.name
                        parent = v.analysis.fragment_info.parent_param_name
                        status += f" -> {parent} ({ext_type})"
                print(f"  {v.original_name} -> {v.smt_name} ({v.bit_width}bit){status}")
        
        print(f"[FormulaBuilder] Function 2 parameters:")
        for p in params2:
            signed_str = "signed" if p.is_signed else "unsigned"
            semantic_str = ""
            if p.semantic_narrow_bits is not None and p.semantic_signedness:
                semantic_str = f", semantic={p.semantic_signedness}:{p.semantic_narrow_bits}"
            print(f"  {p.original_name} -> {p.smt_name} ({p.bit_width}bit, {signed_str}{semantic_str})")
        if extra_vars2:
            print(f"[FormulaBuilder] Function 2 extra variables:")
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
            lines.append(f"(declare-const {p.smt_name} (_ BitVec {p.bit_width}))  ; {signed_comment}")
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
            comment = ""
            if v.analysis:
                comment = f"  ; {v.analysis.classification.name}"
                if v.analysis.reason:
                    comment += f": {v.analysis.reason}"
            lines.append(f"(declare-const {v.smt_name} (_ BitVec {v.bit_width})){comment}")
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
            for expr in self._iter_analysis_expressions(analysis):
                for axiom in self._readonly_reduction_witness_axioms_for_expr(
                    expr,
                    symbol_name_mapping,
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

    def _iter_analysis_expressions(self, analysis: FunctionReturnAnalysis):
        def visit(expr):
            if expr is None:
                return
            yield expr
            if getattr(expr, "expr_type", None) == ExpressionType.PHI and getattr(expr, "value", None):
                for condition, value in expr.value:
                    if condition is not None:
                        yield from visit(getattr(condition, "expression", None))
                    yield from visit(value)
                return
            for operand in getattr(expr, "operands", []) or []:
                yield from visit(operand)

        def visit_conditions(conditions):
            for condition in conditions or []:
                yield from visit(getattr(condition, "expression", None))

        for ret in getattr(analysis, "returns", []) or []:
            yield from visit(getattr(ret, "value", None))
            yield from visit_conditions(getattr(ret, "conditions", None))

        effect_summary = getattr(analysis, "effect_summary", None)
        if effect_summary is not None:
            yield from visit(getattr(effect_summary, "synthetic_expr", None))
            for effect in getattr(effect_summary, "effects", []) or []:
                yield from visit(getattr(effect, "value", None))
                yield from visit_conditions(getattr(effect, "conditions", None))

    def _readonly_reduction_witness_axioms_for_expr(
        self,
        expr,
        symbol_name_mapping,
    ) -> List[str]:
        if expr is None or getattr(expr, "expr_type", None) != ExpressionType.INTRINSIC:
            return []
        reduction_ref = getattr(expr, "runtime_ref", None)
        if not isinstance(reduction_ref, ReadonlyReductionRef):
            return []
        proof = getattr(reduction_ref, "accumulator_proof", None)
        if proof is None:
            return []
        if self._readonly_reduction_contract_key(reduction_ref, proof, expr) is None:
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
        function_application = expr.to_smt(symbol_name_mapping=symbol_name_mapping)
        count_smt = count_expr.to_smt(symbol_name_mapping=symbol_name_mapping)
        base_smt = base_expr.to_smt(symbol_name_mapping=symbol_name_mapping)
        base_addr_smt = self._coerce_smt_bitvec_width(base_smt, base_bits, 64)

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
            axioms.append(
                f"(assert (=> (= {count_smt} {count_literal}) "
                f"(= {function_application} {value_smt})))"
            )
        return axioms

    def _build_readonly_reduction_contract_axioms_section(
        self,
        analysis_param_infos: Tuple[Tuple[FunctionReturnAnalysis, List[Any]], ...],
        *,
        active_return_bits: Optional[int] = None,
    ) -> List[str]:
        entries: List[Dict[str, Any]] = []
        for analysis, param_infos in analysis_param_infos:
            if analysis is None:
                continue
            symbol_name_mapping = build_symbol_name_mapping(param_infos)
            comparison_surface = analysis.get_comparison_surface()
            for expr in self._iter_analysis_expressions(analysis):
                entry = self._readonly_reduction_contract_axiom_entry(
                    expr,
                    symbol_name_mapping,
                    comparison_surface,
                    active_return_bits=active_return_bits,
                )
                if entry is not None:
                    entries.append(entry)

        axioms: List[str] = []
        seen = set()
        for left_index, left in enumerate(entries):
            for right in entries[left_index + 1 :]:
                axiom = self._readonly_reduction_contract_axiom_for_entries(left, right)
                if axiom is None or axiom in seen:
                    continue
                seen.add(axiom)
                axioms.append(axiom)

        if not axioms:
            return []
        lines: List[str] = []
        lines.append("; " + "-" * 40)
        lines.append("; Readonly reduction contract equality axioms")
        lines.append("; Full-width READONLY_SUM contracts share the same object-centric term sequence")
        lines.append("; " + "-" * 40)
        lines.extend(axioms)
        lines.append("")
        return lines

    def _readonly_reduction_contract_axiom_entry(
        self,
        expr,
        symbol_name_mapping,
        comparison_surface=None,
        *,
        active_return_bits: Optional[int] = None,
    ) -> Optional[Dict[str, Any]]:
        if expr is None or getattr(expr, "expr_type", None) != ExpressionType.INTRINSIC:
            return None
        reduction_ref = getattr(expr, "runtime_ref", None)
        if not isinstance(reduction_ref, ReadonlyReductionRef):
            return None
        operands = list(getattr(expr, "operands", []) or [])
        if len(operands) != 2:
            return None
        if not self._readonly_reduction_expr_operands_match_ref(expr, reduction_ref):
            return None
        result_bits = max(1, int(expression_smt_bit_width(expr) or 0))
        if result_bits <= 0 or result_bits % 8 != 0:
            return None
        return {
            "expr": expr,
            "ref": reduction_ref,
            "result_bits": result_bits,
            "application": expr.to_smt(symbol_name_mapping=symbol_name_mapping),
            "surface_key": self._readonly_contract_surface_key(comparison_surface),
            "active_return_bits": self._readonly_contract_valid_projection_bits(
                active_return_bits,
                result_bits,
            ),
        }

    def _readonly_reduction_contract_axiom_for_entries(
        self,
        left: Dict[str, Any],
        right: Dict[str, Any],
    ) -> Optional[str]:
        left_ref = left["ref"]
        right_ref = right["ref"]
        if not isinstance(left_ref, ReadonlyReductionRef) or not isinstance(right_ref, ReadonlyReductionRef):
            return None
        left_bits = int(left["result_bits"])
        right_bits = int(right["result_bits"])
        target_bits = self._readonly_contract_target_bits(left, right)
        if target_bits <= 0 or target_bits % 8 != 0:
            return None
        target_size = target_bits // 8
        left_key_fn = getattr(left_ref, "readonly_term_sequence_contract_key", None)
        right_key_fn = getattr(right_ref, "readonly_term_sequence_contract_key", None)
        if not callable(left_key_fn) or not callable(right_key_fn):
            return None
        try:
            left_key = left_key_fn(result_size=target_size)
            right_key = right_key_fn(result_size=target_size)
        except (AttributeError, TypeError, ValueError):
            return None
        if left_key is None or right_key is None or left_key != right_key:
            return None

        left_value = self._coerce_smt_bitvec_width(
            str(left["application"]),
            left_bits,
            target_bits,
        )
        right_value = self._coerce_smt_bitvec_width(
            str(right["application"]),
            right_bits,
            target_bits,
        )
        if left_value == right_value:
            return None
        return f"(assert (= {left_value} {right_value}))"

    def _readonly_contract_target_bits(
        self,
        left: Dict[str, Any],
        right: Dict[str, Any],
    ) -> int:
        left_bits = int(left["result_bits"])
        right_bits = int(right["result_bits"])
        if left_bits != right_bits:
            return 0
        return left_bits

    def _readonly_contract_valid_projection_bits(
        self,
        candidate_bits: Optional[int],
        result_bits: int,
    ) -> Optional[int]:
        try:
            bits = int(candidate_bits or 0)
        except (TypeError, ValueError):
            return None
        if bits <= 0 or bits % 8 != 0:
            return None
        if bits > int(result_bits):
            return None
        return bits

    def _active_return_comparison_bits(
        self,
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
    ) -> Optional[int]:
        try:
            bits1 = int(self._get_return_size(analysis1) or 0)
            bits2 = int(self._get_return_size(analysis2) or 0)
        except (TypeError, ValueError):
            return None
        if bits1 <= 0 or bits2 <= 0 or bits1 != bits2:
            return None
        return bits1

    def _readonly_contract_surface_key(self, comparison_surface) -> Optional[Tuple[Any, ...]]:
        evidence_key = return_extension_surface_evidence_key(comparison_surface)
        if evidence_key is None:
            return None
        surface_bits, coercion, extension_kind, source_widths = evidence_key
        return (
            "return_extension_surface",
            surface_bits,
            coercion,
            extension_kind,
            source_widths,
        )

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
        return False

    def _readonly_count_operand_matches_ref(
        self,
        expr,
        reduction_ref: ReadonlyReductionRef,
    ) -> bool:
        count_index = getattr(reduction_ref, "count_parameter_index", None)
        if count_index is None:
            return False
        expr_index = self._expression_parameter_index_through_width_views(expr)
        if expr_index is None:
            return False
        try:
            return int(expr_index) == int(count_index)
        except (TypeError, ValueError):
            return False

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

    def _readonly_reduction_contract_key(self, reduction_ref, proof, expr) -> Optional[Tuple[Any, ...]]:
        result_bits = max(1, int(expression_smt_bit_width(expr) or 0))
        result_size = max(1, (result_bits + 7) // 8)
        for owner in (reduction_ref, proof):
            key_fn = getattr(owner, "readonly_term_sequence_contract_key", None)
            if not callable(key_fn):
                continue
            try:
                key = key_fn(result_size=result_size)
            except (AttributeError, TypeError, ValueError):
                key = None
            if key is not None:
                return key
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
                lines.append(f"; Function 1 fragments:")
                lines.extend(fragment_lines1)
            
            if fragment_lines2:
                lines.append(f"; Function 2 fragments:")
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
        return_size2: int
    ) -> List[str]:
        """等価性アサートを構築"""
        lines = []
        lines.append("; " + "-" * 40)
        lines.append("; Equivalence assertion (negated)")
        lines.append("; If SAT: functions are NOT equivalent")
        lines.append("; If UNSAT: functions ARE equivalent")
        lines.append("; " + "-" * 40)
        
        require_equal_return_bit_widths(
            return_size1,
            return_size2,
            context="monolithic return equivalence assertion",
        )
        lines.append(f"(assert (not (= {return_var1} {return_var2})))")
        
        return lines
    
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
    
    def _replace_param_names(
        self,
        smt_expr: str,
        param_infos: List[ParameterInfo]
    ) -> str:
        """SMT式内のパラメータ名を置換"""
        from .params import replace_symbol_names

        return replace_symbol_names(smt_expr, param_infos)
    
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
        from .returns import build_ite_expression

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
        }

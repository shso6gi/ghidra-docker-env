# -*- coding: utf-8 -*-
"""SMT式構築モジュール"""

import hashlib
from typing import List, Dict, Optional, Tuple, Set, Any

from ...model import FunctionReturnAnalysis, loop_summary_method_b_key
from ...model.render_smt import (
    collect_intrinsic_smt_declarations,
    collect_unknown_smt_declarations,
)
from .params import (
    build_fragment_backed_parameter_constraint,
    collect_fragment_infos_by_param_index,
    build_parameter_constraint,
    build_parameter_semantic_constraints,
    build_parameter_pairs,
    collect_param_info,
    merge_param_and_extra_vars,
)
from .returns import build_return_definition, get_return_size
from ..param_semantics import infer_parameter_semantics
from ..semantic_width import normalize_analysis_semantic_width
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

        mem_widths = self._collect_memory_widths(analysis1, analysis2)
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
            analysis1,
            analysis2,
        )
        if runtime_unknown_decls:
            lines.extend(self._build_runtime_unknown_declarations(runtime_unknown_decls))

        intrinsic_decls = self._collect_intrinsic_smt_declarations(
            analysis1,
            analysis2,
        )
        if intrinsic_decls:
            lines.extend(self._build_intrinsic_smt_declarations(intrinsic_decls))

        loop_summary_notes = self._collect_loop_summary_smt_notes(
            analysis1,
            analysis2,
        )
        if loop_summary_notes:
            lines.extend(self._build_loop_summary_smt_notes(loop_summary_notes))

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
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
    ) -> List[int]:
        """2 関数で使われるメモリ load 幅を収集する。"""
        widths = set(collect_memory_bit_widths_from_analysis(analysis1))
        widths.update(collect_memory_bit_widths_from_analysis(analysis2))
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
        
        if return_size1 == return_size2:
            lines.append(f"(assert (not (= {return_var1} {return_var2})))")
        else:
            overlap_size = min(return_size1, return_size2)
            lines.append(f"; Return sizes differ: {return_size1} vs {return_size2}")
            lines.append(f"; Comparing overlapping {overlap_size} bits")
            if return_size1 < return_size2:
                lines.append(f"(assert (not (= {return_var1} ((_ extract {overlap_size - 1} 0) {return_var2}))))")
            else:
                lines.append(f"(assert (not (= ((_ extract {overlap_size - 1} 0) {return_var1}) {return_var2})))")
        
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

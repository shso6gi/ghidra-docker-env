# -*- coding: utf-8 -*-
"""Pairwise戦略（分岐ペア分割方式・二段階チェック対応）"""

from typing import List, Dict, Any, Optional, Tuple
import time
import os

from ...model import FunctionReturnAnalysis, ReturnInfo, Condition
from ...smt import ParallelResult, SolverResult, SolverStatus
from .base import CheckStrategy, StrategyResult
from ..formula.symbol_replace import build_symbol_replacer
from ..normalize import (
    SignFacts,
    normalize_expression,
    NormalizationContext,
    extract_min_excluded_params,
    extract_sign_facts,
    normalize_udiv_with_guard,
    contains_udiv,
    are_structurally_equivalent,
    get_structural_summary,
)
from ..debug_trace import NormalizationRuleApplication, PairwiseDecisiveInfo


class ReturnCase:
    """ReturnInfoから抽出した1つの分岐ケース"""
    
    def __init__(
        self,
        index: int,
        conditions: List[Condition],
        value_expr,
        return_info: ReturnInfo
    ):
        self.index = index
        self.conditions = conditions
        self.value_expr = value_expr
        self.return_info = return_info
        
        # SMT文字列をキャッシュ
        self.conditions_smt: Optional[List[str]] = None
        self.value_smt: Optional[str] = None
    
    def get_conditions_smt(self, param_replace_fn) -> List[str]:
        """条件をSMT形式で取得"""
        if self.conditions_smt is None:
            self.conditions_smt = []
            for cond in self.conditions:
                cond_str = cond.to_smt()
                cond_str = param_replace_fn(cond_str)
                self.conditions_smt.append(cond_str)
        return self.conditions_smt
    
    def get_value_smt(self, param_replace_fn) -> str:
        """値をSMT形式で取得"""
        result = self.value_smt
        if result is None:
            result = str(self.value_expr.to_smt())
            result = param_replace_fn(result)
            self.value_smt = result
        return result
    
    def get_condition_summary(self) -> str:
        """条件の概要を文字列で取得"""
        if not self.conditions:
            return "unconditional"
        cond_strs = []
        for c in self.conditions[:3]:  # 最初の3つ
            cond_str = str(c)
            if cond_str:
                cond_strs.append(cond_str)
        
        if not cond_strs:
            return "unconditional"
        
        return " AND ".join(cond_strs)


class PairwiseStrategy(CheckStrategy):
    """
    Pairwise戦略（分岐ペア分割方式・二段階チェック）
    
    各ペア(i,j)に対して：
    1. Stage 1: 条件のみチェック（C1_i ∧ C2_j）
       - UNSAT → 到達不能なのでペア自体をUNSAT扱い
       - SAT → Stage 2へ
    2. Stage 2: 値不等式を追加してチェック（C1_i ∧ C2_j ∧ V1_i≠V2_j）
       - タイムアウトをhard timeoutに延長可能
    """
    
    def __init__(self, formula_builder, solver_runner, debug: bool = False):
        super().__init__(formula_builder, solver_runner, debug)
        self.per_query_timeout = 5  # Stage 1のタイムアウト（秒）
        self.per_query_timeout_hard = 30  # Stage 2のhard timeout（秒）
        self.save_unknown_queries = False  # UNKNOWNクエリを保存するか
        self.unknown_query_dir = "/tmp"  # 保存先ディレクトリ
    
    def check(
        self,
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
        save_formula: bool = False
    ) -> StrategyResult:
        """等価性をチェック（pairwise方式・二段階チェック）"""
        start_time = time.time()
        
        # ReturnInfoを抽出
        cases1 = self._extract_return_cases(analysis1)
        cases2 = self._extract_return_cases(analysis2)
        
        total_pairs = len(cases1) * len(cases2)
        
        self._debug_print("=" * 60)
        self._debug_print("Pairwise strategy (two-stage check):")
        self._debug_print(f"  Function 1: {len(cases1)} return cases")
        self._debug_print(f"  Function 2: {len(cases2)} return cases")
        self._debug_print(f"  Total pairs to check: {total_pairs}")
        self._debug_print(f"  Per-query timeout (stage1): {self.per_query_timeout}s")
        self._debug_print(f"  Per-query timeout (stage2 hard): {self.per_query_timeout_hard}s")
        self._debug_print("=" * 60)
        
        if total_pairs == 0:
            self._debug_print("No return cases to check")
            return self._create_empty_result()
        
        # 共通SMT部分を生成
        base_ctx = self.formula_builder.build_base_context(analysis1, analysis2)
        
        # シンボル置換関数を作成
        symbol_replace_fn1 = build_symbol_replacer(
            base_ctx['params1'],
            base_ctx.get('extra_vars1', [])
        )
        symbol_replace_fn2 = build_symbol_replacer(
            base_ctx['params2'],
            base_ctx.get('extra_vars2', [])
        )
        
        # デバッグ: 置換対象シンボルを表示
        if self.debug:
            self._debug_print("Symbol replacement mapping:")
            self._debug_print("  Function 1:")
            for p in base_ctx['params1']:
                self._debug_print(f"    {p.original_name} -> {p.smt_name}")
            for v in base_ctx.get('extra_vars1', []):
                self._debug_print(f"    {v.original_name} -> {v.smt_name}")
            self._debug_print("  Function 2:")
            for p in base_ctx['params2']:
                self._debug_print(f"    {p.original_name} -> {p.smt_name}")
            for v in base_ctx.get('extra_vars2', []):
                self._debug_print(f"    {v.original_name} -> {v.smt_name}")
        
        # ペアごとにチェック
        unsat_count = 0
        sat_count = 0
        unknown_count = 0
        error_count = 0
        
        sat_pair_info = None
        counterexample_raw = None
        last_formula = None
        
        # ★ 追加: 正規化ルール収集用の配列を初期化
        all_normalization_rules = []
        
        for i, case1 in enumerate(cases1):
            for j, case2 in enumerate(cases2):
                pair_id = f"({i},{j})"
                
                # 二段階チェック実行
                result = self._solve_query_twostage(
                    base_ctx, case1, case2,
                    symbol_replace_fn1, symbol_replace_fn2,
                    pair_id
                )
                
                # ★ 修正: save_formula に関わらず last_formula を保存
                if result.last_query:
                    last_formula = result.last_query
                
                # ★ 追加: 正規化ルールを収集
                if hasattr(result, 'normalization_rules') and result.normalization_rules:
                    all_normalization_rules.extend(result.normalization_rules)
                
                if result.is_equivalent is False:
                    # SAT: 反例発見 → 即座に終了
                    sat_count += 1
                    sat_pair_info = {
                        'i': i,
                        'j': j,
                        'case1_summary': case1.get_condition_summary(),
                        'case2_summary': case2.get_condition_summary(),
                        'value1': case1.get_value_smt(symbol_replace_fn1),
                        'value2': case2.get_value_smt(symbol_replace_fn2),
                        'pair_stage': result.pair_stage if hasattr(result, 'pair_stage') else 'unknown',
                        'final_query': result.last_query,  # 完全なクエリ
                    }
                    counterexample_raw = result.counterexample_raw
                    
                    self._debug_print(f"  Pair {pair_id}: SAT (NOT EQUIVALENT) - stopping")
                    self._debug_print(f"    Case1[{i}]: {sat_pair_info['case1_summary']}")
                    self._debug_print(f"    Case2[{j}]: {sat_pair_info['case2_summary']}")
                    self._debug_print(f"    Value1: {sat_pair_info['value1'][:60]}...")
                    self._debug_print(f"    Value2: {sat_pair_info['value2'][:60]}...")
                    
                    # 早期終了
                    break
                
                elif result.is_equivalent is True:
                    # UNSAT: このペアは等価
                    unsat_count += 1
                    if self.debug and (unsat_count % 10 == 0 or unsat_count <= 5):
                        self._debug_print(f"  Pair {pair_id}: UNSAT ({unsat_count}/{total_pairs})")
                
                elif result.is_equivalent is None:
                    # UNKNOWN/TIMEOUT
                    unknown_count += 1
                    self._debug_print(f"  Pair {pair_id}: final result UNKNOWN/TIMEOUT")
            
            # 早期終了チェック
            if sat_count > 0:
                break
        
        # 最終判定
        elapsed_time = time.time() - start_time
        
        if sat_count > 0:
            final_is_equiv = False
            self._debug_print("=" * 60)
            self._debug_print("Result: NOT EQUIVALENT (found SAT pair)")
        elif unknown_count > 0:
            final_is_equiv = None
            self._debug_print("=" * 60)
            self._debug_print(f"Result: UNKNOWN (timeout/unknown in {unknown_count} pairs)")
        elif unsat_count == total_pairs:
            final_is_equiv = True
            self._debug_print("=" * 60)
            self._debug_print("Result: EQUIVALENT (all pairs UNSAT)")
        else:
            # 本来ありえない（全ペアをチェックしたはず）
            final_is_equiv = None
            error_count = total_pairs - unsat_count - sat_count - unknown_count
            self._debug_print("=" * 60)
            self._debug_print(f"Result: UNKNOWN (unexpected state, errors={error_count})")
        
        self._debug_print(f"  Total pairs: {total_pairs}")
        self._debug_print(f"  UNSAT: {unsat_count}, SAT: {sat_count}, UNKNOWN: {unknown_count}, ERROR: {error_count}")
        self._debug_print(f"  Total time: {elapsed_time:.3f}s")
        self._debug_print("=" * 60)
        
        # ParallelResult を構築（統合結果として）
        aggregate_result = self._create_aggregate_result(
            final_is_equiv, elapsed_time, counterexample_raw
        )
        
        return StrategyResult(
            is_equivalent=final_is_equiv,
            solver_results=aggregate_result,
            smt_formula=last_formula,  # save_formula の条件を削除
            counterexample_raw=counterexample_raw,
            return_var1="return_1",
            return_var2="return_2",
            constrained_fragments=base_ctx.get('constrained_fragments', []),
            total_pairs=total_pairs,
            unsat_pairs=unsat_count,
            sat_pairs=sat_count,
            unknown_pairs=unknown_count,
            error_pairs=error_count,
            sat_pair_info=sat_pair_info,
            normalization_rules=all_normalization_rules  # ★ これで使える
        )
    
    def _solve_query_twostage(
        self,
        base_ctx: Dict[str, Any],
        case1: ReturnCase,
        case2: ReturnCase,
        param_replace_fn1,
        param_replace_fn2,
        pair_id: str
    ) -> 'QueryResult':
        """二段階チェック"""
        # Stage 1: 条件のみチェック
        cond_query = self._build_condition_only_query(
            base_ctx, case1, case2,
            param_replace_fn1, param_replace_fn2,
            pair_id
        )
        
        stage1_result = self._solve_query_internal(
            cond_query, pair_id, stage="conds-only", use_hard_timeout=False
        )
        
        if stage1_result.is_equivalent is True:
            # UNSAT: 条件が矛盾 → 到達不能
            stage1_result.last_query = cond_query
            stage1_result.pair_stage = "conds-only"  # ★ 追加
            return stage1_result
        
        # Stage 2: 値不等式を追加
        full_query = self._build_pair_query(
            base_ctx, case1, case2,
            param_replace_fn1, param_replace_fn2,
            pair_id
        )
        
        stage2_result = self._solve_query_internal(
            full_query, pair_id, stage="with-ineq", use_hard_timeout=True
        )
        
        stage2_result.last_query = full_query
        stage2_result.pair_stage = "with-ineq"  # ★ 追加
        
        # Stage 3: 正規化
        if stage2_result.is_equivalent is None:
            norm_result = self._try_normalization_equivalence(
                base_ctx, case1, case2,
                param_replace_fn1, param_replace_fn2,
                pair_id
            )
            
            if norm_result.is_equivalent is True:
                norm_result.last_query = full_query
                norm_result.pair_stage = "norm-ineq"  # ★ 追加
                return norm_result
            elif norm_result.is_equivalent is False:
                norm_result.last_query = full_query
                norm_result.pair_stage = "norm-ineq"  # ★ 追加
                return norm_result
        
        return stage2_result
    
    def _try_normalization_equivalence(
        self,
        base_ctx: Dict[str, Any],
        case1: ReturnCase,
        case2: ReturnCase,
        param_replace_fn1,
        param_replace_fn2,
        pair_id: str
    ) -> 'QueryResult':
        """
        正規化して値式をSMTで比較（安全性チェック付き）
        
        フロー:
        1. Facts ベースの正規化を試行（Phase 1）
        2. Phase 1の結果にUDIVが残っていれば、SMTガード証明ベースの正規化を試行（Phase 2）
        3. 構造一致チェック（ヒントとして使用）
        4. **必ずSMTで最終確認**（構造一致時も含む）
        
        Returns:
            QueryResult (正規化ルール記録を含む)
        """
        # 元の式
        value1_orig = case1.value_expr
        value2_orig = case2.value_expr
        
        # MIN除外制約を解析（SMT変数名で取得）
        header_lines = base_ctx.get('header_lines', [])
        min_excluded_smt = extract_min_excluded_params(header_lines, debug=self.debug)
        
        if self.debug and min_excluded_smt:
            self._debug_print(f"MIN-excluded SMT vars: {min_excluded_smt}")
        
        # SMT変数名 → 元のパラメータ名へのマッピングを構築
        smt_to_original = {}
        params1 = base_ctx.get('params1', [])
        params2 = base_ctx.get('params2', [])
        
        for param_info in params1:
            smt_to_original[param_info.smt_name] = param_info.original_name
        for param_info in params2:
            smt_to_original[param_info.smt_name] = param_info.original_name
        
        # MIN除外制約を元のパラメータ名に変換
        min_excluded_original = set()
        for smt_name in min_excluded_smt:
            if smt_name in smt_to_original:
                original_name = smt_to_original[smt_name]
                min_excluded_original.add(original_name)
        
        if self.debug and min_excluded_original:
            self._debug_print(f"MIN-excluded original vars: {min_excluded_original}")
        
        # === Sign facts の抽出 ===
        if self.debug:
            self._debug_print(f"  Extracting sign facts from conditions...")
        
        facts1 = extract_sign_facts(case1.conditions, debug=self.debug)
        facts2 = extract_sign_facts(case2.conditions, debug=self.debug)
        
        combined_facts = SignFacts()
        combined_facts.merge(facts1)
        combined_facts.merge(facts2)
        
        # SMT変数名を元名に変換
        nonneg_original = set()
        pos_original = set()
        neg_original = set()
        nonzero_original = set()
        
        for var_name in combined_facts.nonneg_vars:
            nonneg_original.add(smt_to_original.get(var_name, var_name))
        
        for var_name in combined_facts.pos_vars:
            pos_original.add(smt_to_original.get(var_name, var_name))
        
        for var_name in combined_facts.neg_vars:
            neg_original.add(smt_to_original.get(var_name, var_name))
        
        for var_name in combined_facts.nonzero_vars:
            nonzero_original.add(smt_to_original.get(var_name, var_name))
        
        if self.debug:
            if nonneg_original:
                self._debug_print(f"Sign facts: nonneg={nonneg_original}")
            if pos_original:
                self._debug_print(f"Sign facts: pos={pos_original}")
            if neg_original:
                self._debug_print(f"Sign facts: neg={neg_original}")
            if nonzero_original:
                self._debug_print(f"Sign facts: nonzero={nonzero_original}")
        
        # 正規化コンテキストを作成（元のパラメータ名を使用）
        norm_context = NormalizationContext(
            debug=self.debug,
            min_excluded_params=min_excluded_original,
            nonneg_vars=nonneg_original,
            pos_vars=pos_original,
            neg_vars=neg_original,
            nonzero_vars=nonzero_original,
            allow_unsafe=False
        )
        
        # ============================================
        # Phase 1: Facts ベースの正規化を試行
        # ============================================
        if self.debug:
            self._debug_print(f"  Phase 1: Facts-based normalization...")
        
        value1_norm = normalize_expression(value1_orig, norm_context)
        value2_norm = normalize_expression(value2_orig, norm_context)
        
        # ============================================
        # Phase 2: UDIVが残っていればSMTガード証明を試行
        # ============================================
        # 条件SMTを事前に取得（Phase 2で使用）
        case1_conds_smt = case1.get_conditions_smt(param_replace_fn1)
        case2_conds_smt = case2.get_conditions_smt(param_replace_fn2)
        
        # value1 にUDIVが残っているか検査
        if contains_udiv(value1_norm):
            if self.debug:
                self._debug_print(f"  Value1 contains UDIV after Phase 1, trying Phase 2 (SMT guard proof)...")
            
            value1_norm_phase2 = normalize_udiv_with_guard(
                value1_norm,
                base_ctx,
                case1_conds_smt,
                case2_conds_smt,
                self.solver_runner,
                norm_context,
                param_replace_fn1
            )
            
            if value1_norm_phase2 is not value1_norm:
                if self.debug:
                    self._debug_print(f"  Value1: Phase 2 applied transformations")
                value1_norm = value1_norm_phase2
                
                # Phase 2 後に Phase 1 を再適用
                if self.debug:
                    self._debug_print(f"  Value1: Re-applying Phase 1 after Phase 2...")
                value1_norm = normalize_expression(value1_norm, norm_context)
        
        # value2 にUDIVが残っているか検査
        if contains_udiv(value2_norm):
            if self.debug:
                self._debug_print(f"  Value2 contains UDIV after Phase 1, trying Phase 2 (SMT guard proof)...")
            
            value2_norm_phase2 = normalize_udiv_with_guard(
                value2_norm,
                base_ctx,
                case1_conds_smt,
                case2_conds_smt,
                self.solver_runner,
                norm_context,
                param_replace_fn2
            )
            
            if value2_norm_phase2 is not value2_norm:
                if self.debug:
                    self._debug_print(f"  Value2: Phase 2 applied transformations")
                value2_norm = value2_norm_phase2
                
                # Phase 2 後に Phase 1 を再適用
                if self.debug:
                    self._debug_print(f"  Value2: Re-applying Phase 1 after Phase 2...")
                value2_norm = normalize_expression(value2_norm, norm_context)
        
        # ============================================
        # 正規化結果の評価とSMT比較
        # ============================================
        
        # SMT文字列化（パラメータ名を置換）
        value1_smt_orig = param_replace_fn1(value1_orig.to_smt())
        value2_smt_orig = param_replace_fn2(value2_orig.to_smt())
        value1_smt_norm = param_replace_fn1(value1_norm.to_smt())
        value2_smt_norm = param_replace_fn2(value2_norm.to_smt())
        
        # ログ出力（詳細）
        self._debug_print(f"  Pair {pair_id} normalization attempt:")
        self._debug_print(f"    Original 1: {value1_smt_orig[:200]}")
        self._debug_print(f"    Original 2: {value2_smt_orig[:200]}")
        
        # 正規化で変更があったかチェック
        changed1 = value1_smt_orig != value1_smt_norm
        changed2 = value2_smt_orig != value2_smt_norm
        
        if changed1:
            self._debug_print(f"    Normalized 1: {value1_smt_norm[:200]}")
        else:
            self._debug_print(f"    Normalized 1: (no change)")
        
        if changed2:
            self._debug_print(f"    Normalized 2: {value2_smt_norm[:200]}")
        else:
            self._debug_print(f"    Normalized 2: (no change)")
        
        # 適用されたルールをログ出力
        if norm_context.applied_rules:
            self._debug_print(f"    Applied rules:")
            for rule in norm_context.applied_rules:
                self._debug_print(f"      - {rule.rule_name}: {rule.reason}")
        else:
            self._debug_print(f"    No normalization rules applied")
        
        # ★ 正規化ルールを記録（QueryResultに渡すため）
        from ..debug_trace import NormalizationRuleApplication
        normalization_rules = []
        for rule_app in norm_context.applied_rules:
            normalization_rules.append(NormalizationRuleApplication(
                rule_name=rule_app.rule_name,
                reason=rule_app.reason,
                applied_to=f"pair_{pair_id}",
                before=rule_app.before_expr,
                after=rule_app.after_expr,
            ))
        
        # 正規化で変更がなければスキップ（最適化）
        if not changed1 and not changed2:
            self._debug_print(f"    No normalization applied -> remain UNKNOWN")
            result = QueryResult(is_equivalent=None)
            result.normalization_rules = normalization_rules
            return result
        
        # ============================================
        # 構造的同一性チェック（ヒントとして使用）
        # ============================================
        is_struct_eq, struct_reason = are_structurally_equivalent(
            value1_norm,
            value2_norm,
            debug=self.debug
        )
        
        if is_struct_eq:
            # 構造一致検出 → ヒントとしてログ出力するが、SMT確認は必須
            self._debug_print(f"    STRUCTURAL MATCH DETECTED, SMT CONFIRMATION REQUIRED")
            self._debug_print(f"      Reason: {struct_reason}")
            self._debug_print(f"      Structure: {get_structural_summary(value1_norm, max_depth=5)}")
        else:
            # 構造不一致 → 診断ログを出力
            if self.debug:
                self._debug_print(f"    Structural match not detected:")
                self._debug_print(f"      Structure1: {get_structural_summary(value1_norm, max_depth=5)}")
                self._debug_print(f"      Structure2: {get_structural_summary(value2_norm, max_depth=5)}")
                self._debug_print(f"      Reason: {struct_reason}")
        
        # ============================================
        # SMTクエリで等価性を確認（構造一致時も含む）
        # ============================================
        self._debug_print(f"    Proceeding to SMT solver (norm-ineq)...")
        
        norm_query = self._build_normalized_inequality_query(
            base_ctx, case1, case2,
            param_replace_fn1, param_replace_fn2,
            value1_smt_norm, value2_smt_norm,
            pair_id
        )
        
        # ソルバー実行（短いタイムアウト：正規化後は簡単なはず）
        norm_result = self._solve_query_internal(
            norm_query, pair_id, stage="norm-ineq", use_hard_timeout=False
        )
        
        # ★ 正規化ルールを結果に追加
        norm_result.normalization_rules = normalization_rules
        
        # 結果判定
        if norm_result.is_equivalent is True:
            # UNSAT: 正規化後は等価 → ペアをUNSAT扱い
            self._debug_print(f"    Normalized inequality: UNSAT -> values are equivalent")
            if is_struct_eq:
                self._debug_print(f"    (Structural match was confirmed by SMT)")
            self._debug_print(f"  Pair {pair_id} normalization: values became equivalent -> UNSAT")
            return norm_result
        
        elif norm_result.is_equivalent is False:
            # SAT: 正規化後も非等価 → 反例あり
            self._debug_print(f"    Normalized inequality: SAT -> genuine counterexample found")
            if is_struct_eq:
                self._debug_print(f"    WARNING: Structural match detected but SMT found counterexample!")
                self._debug_print(f"    This indicates the structural check may have false positives.")
            self._debug_print(f"  Pair {pair_id} normalization: found counterexample -> NOT EQUIVALENT")
            return norm_result
        
        else:
            # UNKNOWN: 正規化後もタイムアウト
            self._debug_print(f"    Normalized inequality: UNKNOWN -> remain UNKNOWN")
            if is_struct_eq:
                self._debug_print(f"    (Structural match detected but SMT solver timed out)")
            return norm_result
    
    def _solve_query_internal(
        self,
        query: str,
        pair_id: str,
        stage: str = "full",
        use_hard_timeout: bool = False
    ) -> 'QueryResult':
        """内部用：クエリを実行"""
        # タイムアウトを設定
        old_timeout = self.solver_runner.timeout
        if use_hard_timeout:
            timeout = self.per_query_timeout_hard
        else:
            timeout = self.per_query_timeout
        
        self.solver_runner.timeout = timeout
        
        try:
            parallel_result = self.solver_runner.run_sequential(query)
            
            counterexample_raw = None
            if parallel_result.is_equivalent is False:
                counterexample_raw = parallel_result.get_counterexample()
            
            # ログ出力
            if parallel_result.is_equivalent is True:
                result_str = "UNSAT"
            elif parallel_result.is_equivalent is False:
                result_str = "SAT"
            else:
                result_str = "UNKNOWN/TIMEOUT"
            
            elapsed = parallel_result.results[0].elapsed_time if parallel_result.results else 0.0
            self._debug_print(f"  Pair {pair_id} {stage}: {result_str} (t={elapsed:.3f}s)")
            
            # === 追加: エラーハンドリング ===
            if parallel_result.results:
                from ...smt import SolverStatus
                for solver_result in parallel_result.results:
                    if solver_result.status == SolverStatus.ERROR:
                        error_msg = solver_result.error_message or ""
                        self._debug_print(f"  Solver error: {error_msg}")
                        
                        # パースエラーの場合、未知シンボルを抽出
                        if "unknown constant" in error_msg:
                            import re
                            match = re.search(r'unknown constant (\w+)', error_msg)
                            if match:
                                unknown_sym = match.group(1)
                                self._debug_print(f"  !!! Unknown symbol detected: '{unknown_sym}'")
                                self._debug_print(f"  This symbol should have been replaced during symbol mapping.")
                                
                                # デバッグ用：クエリの一部を表示
                                if self.debug:
                                    lines = query.split('\n')
                                    for i, line in enumerate(lines):
                                        if unknown_sym in line:
                                            start = max(0, i - 2)
                                            end = min(len(lines), i + 3)
                                            self._debug_print(f"  Context (lines {start}-{end}):")
                                            for j in range(start, end):
                                                marker = " >>> " if j == i else "     "
                                                self._debug_print(f"{marker}{lines[j]}")
            # === エラーハンドリング終了 ===
            
            # UNKNOWNクエリを保存
            if self.save_unknown_queries and parallel_result.is_equivalent is None:
                self._save_unknown_query(query, pair_id, stage)
            
            return QueryResult(
                is_equivalent=parallel_result.is_equivalent,
                counterexample_raw=counterexample_raw
            )
        
        finally:
            self.solver_runner.timeout = old_timeout
    
    def _build_condition_only_query(
        self,
        base_ctx: Dict[str, Any],
        case1: ReturnCase,
        case2: ReturnCase,
        param_replace_fn1,
        param_replace_fn2,
        pair_id: str
    ) -> str:
        """
        条件のみのSMTクエリを構築（値不等式なし）
        
        構成:
        1. 共通ヘッダ
        2. case1の条件 (C1_i)
        3. case2の条件 (C2_j)
        4. check-sat
        """
        lines = []
        
        # ヘッダー
        lines.append("; " + "=" * 60)
        lines.append(f"; Pairwise Query (Conditions Only): Pair {pair_id}")
        lines.append(f"; Case1[{case1.index}]: {case1.get_condition_summary()}")
        lines.append(f"; Case2[{case2.index}]: {case2.get_condition_summary()}")
        lines.append("; " + "=" * 60)
        lines.append("")
        lines.append("(set-logic QF_BV)")
        lines.append("")
        
        # 共通部分
        lines.extend(base_ctx['header_lines'])
        
        # Case1の条件
        conds1_smt = case1.get_conditions_smt(param_replace_fn1)
        if conds1_smt:
            lines.append("; " + "-" * 40)
            lines.append(f"; Case1[{case1.index}] conditions")
            lines.append("; " + "-" * 40)
            for cond_str in conds1_smt:
                lines.append(f"(assert {cond_str})")
            lines.append("")
        
        # Case2の条件
        conds2_smt = case2.get_conditions_smt(param_replace_fn2)
        if conds2_smt:
            lines.append("; " + "-" * 40)
            lines.append(f"; Case2[{case2.index}] conditions")
            lines.append("; " + "-" * 40)
            for cond_str in conds2_smt:
                lines.append(f"(assert {cond_str})")
            lines.append("")
        
        lines.append("(check-sat)")
        
        return "\n".join(lines)
    
    def _save_unknown_query(self, query: str, pair_id: str, stage: str) -> None:
        """UNKNOWNクエリをファイルに保存"""
        filename = f"unknown_query_{pair_id.replace(',', '_').replace('(', '').replace(')', '')}_{stage}.smt2"
        filepath = os.path.join(self.unknown_query_dir, filename)
        
        try:
            with open(filepath, 'w') as f:
                f.write(query)
            self._debug_print(f"  Saved unknown query to: {filepath}")
        except Exception as e:
            self._debug_print(f"  Failed to save unknown query: {e}")
    
    def _extract_return_cases(
        self,
        analysis: FunctionReturnAnalysis
    ) -> List[ReturnCase]:
        """FunctionReturnAnalysis から ReturnCase を抽出"""
        cases = []
        for i, ret_info in enumerate(analysis.returns):
            cases.append(ReturnCase(
                index=i,
                conditions=ret_info.conditions,
                value_expr=ret_info.value,
                return_info=ret_info
            ))
        return cases
    
    def _build_pair_query(
        self,
        base_ctx: Dict[str, Any],
        case1: ReturnCase,
        case2: ReturnCase,
        param_replace_fn1,
        param_replace_fn2,
        pair_id: str
    ) -> str:
        """ペア(i,j)用のSMTクエリを構築（値不等式含む）"""
        lines = []
        
        # ヘッダー
        lines.append("; " + "=" * 60)
        lines.append(f"; Pairwise Query: Pair {pair_id}")
        lines.append(f"; Case1[{case1.index}]: {case1.get_condition_summary()}")
        lines.append(f"; Case2[{case2.index}]: {case2.get_condition_summary()}")
        lines.append("; " + "=" * 60)
        lines.append("")
        lines.append("(set-logic QF_BV)")
        lines.append("")
        
        # 共通部分（パラメータ宣言、制約）
        lines.extend(base_ctx['header_lines'])
        
        # Case1の条件
        conds1_smt = case1.get_conditions_smt(param_replace_fn1)
        if conds1_smt:
            lines.append("; " + "-" * 40)
            lines.append(f"; Case1[{case1.index}] conditions")
            lines.append("; " + "-" * 40)
            for cond_str in conds1_smt:
                lines.append(f"(assert {cond_str})")
            lines.append("")
        
        # Case2の条件
        conds2_smt = case2.get_conditions_smt(param_replace_fn2)
        if conds2_smt:
            lines.append("; " + "-" * 40)
            lines.append(f"; Case2[{case2.index}] conditions")
            lines.append("; " + "-" * 40)
            for cond_str in conds2_smt:
                lines.append(f"(assert {cond_str})")
            lines.append("")
        
        # 値の非等価
        value1_smt = case1.get_value_smt(param_replace_fn1)
        value2_smt = case2.get_value_smt(param_replace_fn2)
        
        lines.append("; " + "-" * 40)
        lines.append("; Value inequality")
        lines.append("; " + "-" * 40)
        
        # ビット幅を取得（簡易版：式から推定、または固定値を使う）
        # ここでは return_size を base_ctx から取得
        return_size1 = base_ctx.get('return_size1', 32)
        return_size2 = base_ctx.get('return_size2', 32)
        
        if return_size1 == return_size2:
            lines.append(f"(assert (not (= {value1_smt} {value2_smt})))")
        else:
            # サイズが異なる場合は重複部分を比較
            overlap = min(return_size1, return_size2)
            if return_size1 < return_size2:
                lines.append(f"(assert (not (= {value1_smt} ((_ extract {overlap - 1} 0) {value2_smt}))))")
            else:
                lines.append(f"(assert (not (= ((_ extract {overlap - 1} 0) {value1_smt}) {value2_smt})))")
        
        lines.append("")
        lines.append("(check-sat)")
        lines.append("(get-model)")
        
        return "\n".join(lines)
    
    def _build_normalized_inequality_query(
        self,
        base_ctx: Dict[str, Any],
        case1: ReturnCase,
        case2: ReturnCase,
        param_replace_fn1,
        param_replace_fn2,
        value1_smt_norm: str,
        value2_smt_norm: str,
        pair_id: str
    ) -> str:
        """
        正規化後の値不等式クエリを構築
        
        構成:
        1. base_ctx['header_lines'] (param宣言・param同一制約・UB制約など)
        2. case1の条件（param_*_1 側）
        3. case2の条件（param_*_2 側）
        4. 正規化後の値の不等式 (not (= norm1 norm2))
        5. check-sat, get-model
        
        base_ctx に含まれる param_1_1 = param_1_2 などの制約により、
        サフィックス違いでも「同じ入力」として扱われる。
        
        Args:
            base_ctx: 共通SMT部分
            case1, case2: 比較対象のケース
            param_replace_fn1, param_replace_fn2: パラメータ置換関数
            value1_smt_norm, value2_smt_norm: 正規化後のSMT式（パラメータ名置換済み）
            pair_id: ペアID
        
        Returns:
            SMTクエリ文字列
        """
        lines = []
        
        # ヘッダー
        lines.append("; " + "=" * 60)
        lines.append(f"; Normalized Inequality Query: Pair {pair_id}")
        lines.append(f"; Check if normalized values are equivalent under base constraints")
        lines.append("; " + "=" * 60)
        lines.append("")
        lines.append("(set-logic QF_BV)")
        lines.append("")
        
        # 共通部分（param宣言・param同一制約・UB制約など）
        lines.extend(base_ctx['header_lines'])
        
        # Case1の条件
        conds1_smt = case1.get_conditions_smt(param_replace_fn1)
        if conds1_smt:
            lines.append("; " + "-" * 40)
            lines.append(f"; Case1[{case1.index}] conditions")
            lines.append("; " + "-" * 40)
            for cond_str in conds1_smt:
                lines.append(f"(assert {cond_str})")
            lines.append("")
        
        # Case2の条件
        conds2_smt = case2.get_conditions_smt(param_replace_fn2)
        if conds2_smt:
            lines.append("; " + "-" * 40)
            lines.append(f"; Case2[{case2.index}] conditions")
            lines.append("; " + "-" * 40)
            for cond_str in conds2_smt:
                lines.append(f"(assert {cond_str})")
            lines.append("")
        
        # 正規化後の値の不等式
        lines.append("; " + "-" * 40)
        lines.append("; Normalized value inequality")
        lines.append("; (param_*_1 and param_*_2 are constrained to be equal by base_ctx)")
        lines.append("; " + "-" * 40)
        
        return_size1 = base_ctx.get('return_size1', 32)
        return_size2 = base_ctx.get('return_size2', 32)
        
        if return_size1 == return_size2:
            lines.append(f"(assert (not (= {value1_smt_norm} {value2_smt_norm})))")
        else:
            # サイズが異なる場合は重複部分を比較
            overlap = min(return_size1, return_size2)
            if return_size1 < return_size2:
                lines.append(f"(assert (not (= {value1_smt_norm} ((_ extract {overlap - 1} 0) {value2_smt_norm}))))")
            else:
                lines.append(f"(assert (not (= ((_ extract {overlap - 1} 0) {value1_smt_norm}) {value2_smt_norm})))")
        
        lines.append("")
        lines.append("(check-sat)")
        lines.append("(get-model)")
        
        return "\n".join(lines)
    
    def _create_aggregate_result(
        self,
        is_equivalent: Optional[bool],
        elapsed_time: float,
        counterexample_raw: Optional[Dict]
    ) -> ParallelResult:
        """Pairwise結果を集約してParallelResultを作成"""
        status_map = {
            True: SolverStatus.UNSAT,
            False: SolverStatus.SAT,
            None: SolverStatus.UNKNOWN
        }
        status = status_map.get(is_equivalent, SolverStatus.UNKNOWN)
        
        solver_result = SolverResult(
            solver_name="pairwise_aggregate",
            status=status,
            elapsed_time=elapsed_time,
            model=counterexample_raw
        )
        
        return ParallelResult(results=[solver_result])
    
    def _create_empty_result(self) -> StrategyResult:
        """空の結果を作成"""
        return StrategyResult(
            is_equivalent=None,
            solver_results=ParallelResult(results=[]),
            total_pairs=0,
            unsat_pairs=0,
            sat_pairs=0,
            unknown_pairs=0,
            error_pairs=0
        )


class QueryResult:
    """1つのクエリの実行結果（内部用）"""
    
    def __init__(
        self,
        is_equivalent: Optional[bool],
        counterexample_raw: Optional[Dict] = None
    ):
        self.is_equivalent = is_equivalent
        self.counterexample_raw = counterexample_raw
        self.last_query: Optional[str] = None
        self.normalization_rules: List = []
        self.pair_stage: Optional[str] = None
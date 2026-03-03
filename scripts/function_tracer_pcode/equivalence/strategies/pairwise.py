# -*- coding: utf-8 -*-
"""Pairwise戦略（分岐ペア分割方式・二段階チェック対応）"""

from typing import List, Dict, Any, Optional, Tuple
import time
import os

from ...model import FunctionReturnAnalysis, ReturnInfo, Condition
from ...smt import ParallelResult, SolverResult, SolverStatus
from .base import CheckStrategy, StrategyResult


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
        
        # パラメータ置換関数を作成
        param_replace_fn1 = self._create_param_replacer(
            base_ctx['params1'], analysis1.function_name
        )
        param_replace_fn2 = self._create_param_replacer(
            base_ctx['params2'], analysis2.function_name
        )
        
        # ペアごとにチェック
        unsat_count = 0
        sat_count = 0
        unknown_count = 0
        error_count = 0
        
        sat_pair_info = None
        counterexample_raw = None
        last_formula = None
        
        for i, case1 in enumerate(cases1):
            for j, case2 in enumerate(cases2):
                pair_id = f"({i},{j})"
                
                # 二段階チェック実行
                result = self._solve_query_twostage(
                    base_ctx, case1, case2,
                    param_replace_fn1, param_replace_fn2,
                    pair_id
                )
                
                if save_formula and result.last_query:
                    last_formula = result.last_query
                
                if result.is_equivalent is False:
                    # SAT: 反例発見 → 即座に終了
                    sat_count += 1
                    sat_pair_info = {
                        'i': i,
                        'j': j,
                        'case1_summary': case1.get_condition_summary(),
                        'case2_summary': case2.get_condition_summary(),
                        'value1': case1.get_value_smt(param_replace_fn1),
                        'value2': case2.get_value_smt(param_replace_fn2),
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
            smt_formula=last_formula if save_formula else None,
            counterexample_raw=counterexample_raw,
            return_var1="return_1",
            return_var2="return_2",
            constrained_fragments=base_ctx.get('constrained_fragments', []),
            total_pairs=total_pairs,
            unsat_pairs=unsat_count,
            sat_pairs=sat_count,
            unknown_pairs=unknown_count,
            error_pairs=error_count,
            sat_pair_info=sat_pair_info
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
        """
        二段階チェック：
        1. Stage 1: 条件のみチェック（C1_i ∧ C2_j）
           - UNSAT → 到達不能なのでペア自体をUNSAT扱い
           - SAT → Stage 2へ
        2. Stage 2: 値不等式を追加してチェック（C1_i ∧ C2_j ∧ V1_i≠V2_j）
           - hard timeout で再試行
        3. Stage 3 (NEW): Stage 2が unknown の場合、正規化してSMTで比較
           - 正規化後が等価なら UNSAT 扱い
           - 正規化後も非等価なら反例として SAT
        """
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
            # UNSAT: 条件が矛盾 → 到達不能なのでペア自体をUNSAT扱い
            self._debug_print(f"  Pair {pair_id} stage1(conds-only): UNSAT (unreachable) - skip value check")
            stage1_result.last_query = cond_query
            return stage1_result
        
        if stage1_result.is_equivalent is False:
            # SAT: 条件が充足可能 → Stage 2へ
            self._debug_print(f"  Pair {pair_id} stage1(conds-only): SAT - proceed to value check")
        else:
            # UNKNOWN: 条件チェックで不明 → とりあえずStage 2へ
            self._debug_print(f"  Pair {pair_id} stage1(conds-only): UNKNOWN - proceed to value check")
        
        # Stage 2: 値不等式を追加して再チェック
        full_query = self._build_pair_query(
            base_ctx, case1, case2,
            param_replace_fn1, param_replace_fn2,
            pair_id
        )
        
        stage2_result = self._solve_query_internal(
            full_query, pair_id, stage="with-ineq", use_hard_timeout=True
        )
        
        stage2_result.last_query = full_query
        
        # Stage 3 (NEW): unknown の場合のみ正規化を試行
        if stage2_result.is_equivalent is None:
            norm_result = self._try_normalization_equivalence(
                base_ctx,  # 追加
                case1, case2,
                param_replace_fn1, param_replace_fn2,
                pair_id
            )
            
            # 正規化で確定した場合はその結果を返す
            if norm_result.is_equivalent is True:
                # UNSAT: 正規化後は等価
                norm_result.last_query = full_query
                return norm_result
            elif norm_result.is_equivalent is False:
                # SAT: 正規化後も非等価（反例発見）
                norm_result.last_query = full_query
                return norm_result
            # UNKNOWN の場合は stage2_result をそのまま使う
        
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
        正規化して値式をSMTで比較
        
        Stage 2 で unknown になったペアに対してのみ適用。
        正規化後の式がSMT的に等価なら、UNSAT 扱いに格上げする。
        
        サフィックス（_1/_2）は維持したまま、base_ctx のパラメータ同一制約
        （param_1_1 = param_1_2 など）を利用して等価性を判定する。
        
        Args:
            base_ctx: 共通SMT部分（param宣言・制約など）
            case1, case2: 比較対象のケース
            param_replace_fn1, param_replace_fn2: パラメータ置換関数
            pair_id: ペアID（ログ用）
        
        Returns:
            QueryResult: 正規化結果
                - is_equivalent=True: 正規化後は等価（UNSAT）
                - is_equivalent=False: 正規化後も非等価（SAT、反例あり）
                - is_equivalent=None: 不明（UNKNOWN）
        """
        from ..normalize import normalize_expression
        
        # 元の式
        value1_orig = case1.value_expr
        value2_orig = case2.value_expr
        
        # 正規化を適用
        value1_norm = normalize_expression(value1_orig)
        value2_norm = normalize_expression(value2_orig)
        
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
        
        # 正規化で変更がなければスキップ（最適化）
        if not changed1 and not changed2:
            self._debug_print(f"    No normalization applied -> remain UNKNOWN")
            return QueryResult(is_equivalent=None)
        
        # SMTクエリで等価性を確認
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
        
        # 結果判定
        if norm_result.is_equivalent is True:
            # UNSAT: 正規化後は等価 → ペアをUNSAT扱い
            self._debug_print(f"    Normalized inequality: UNSAT -> values are equivalent")
            self._debug_print(f"  Pair {pair_id} normalization: values became equivalent -> UNSAT")
            return QueryResult(is_equivalent=True)
        
        elif norm_result.is_equivalent is False:
            # SAT: 正規化後も非等価 → 反例あり
            self._debug_print(f"    Normalized inequality: SAT -> genuine counterexample found")
            self._debug_print(f"  Pair {pair_id} normalization: found counterexample -> NOT EQUIVALENT")
            return QueryResult(
                is_equivalent=False,
                counterexample_raw=norm_result.counterexample_raw
            )
        
        else:
            # UNKNOWN: 正規化後もタイムアウト
            self._debug_print(f"    Normalized inequality: UNKNOWN -> remain UNKNOWN")
            return QueryResult(is_equivalent=None)
    
    def _solve_query_internal(
        self,
        query: str,
        pair_id: str,
        stage: str = "full",
        use_hard_timeout: bool = False
    ) -> 'QueryResult':
        """
        内部用：クエリを実行
        
        Args:
            query: SMTクエリ
            pair_id: ペアID
            stage: ステージ名（ログ用）
            use_hard_timeout: hard timeout を使うか
        """
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
    
    def _create_param_replacer(self, params_info: List, func_name: str):
        """パラメータ名を置換する関数を作成"""
        import re
        
        def replacer(smt_expr: str) -> str:
            result = smt_expr
            # params_info は ParameterInfo のリスト
            # original_name -> smt_name に置換
            sorted_params = sorted(params_info, key=lambda p: -len(p.original_name))
            for param in sorted_params:
                pattern = r'\b' + re.escape(param.original_name) + r'\b'
                result = re.sub(pattern, param.smt_name, result)
            return result
        
        return replacer
    
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
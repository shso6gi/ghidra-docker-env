# -*- coding: utf-8 -*-
"""Pairwise戦略（分岐ペア分割方式）"""

from typing import List, Dict, Any, Optional, Tuple
import time

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
            if cond_str:  # Noneや空文字列でない場合のみ追加
                cond_strs.append(cond_str)
        
        if not cond_strs:
            return "unconditional"
        
        return " AND ".join(cond_strs)


class PairwiseStrategy(CheckStrategy):
    """
    Pairwise戦略（分岐ペア分割方式）
    
    関数1のN個のReturnInfoと関数2のM個のReturnInfoの全ペア(i,j)に対して、
    小さなSMTクエリを生成・実行:
        C1_i ∧ C2_j ∧ (V1_i ≠ V2_j)
    
    - 1つでもSATなら即座に NOT EQUIVALENT
    - 全ペアUNSATなら EQUIVALENT
    - unknownが混じれば TIMEOUT
    """
    
    def __init__(self, formula_builder, solver_runner, debug: bool = False):
        super().__init__(formula_builder, solver_runner, debug)
        self.per_query_timeout = 5  # 各クエリのタイムアウト（秒）
    
    def check(
        self,
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
        save_formula: bool = False
    ) -> StrategyResult:
        """等価性をチェック（pairwise方式）"""
        start_time = time.time()
        
        # ReturnInfoを抽出
        cases1 = self._extract_return_cases(analysis1)
        cases2 = self._extract_return_cases(analysis2)
        
        total_pairs = len(cases1) * len(cases2)
        
        self._debug_print("=" * 60)
        self._debug_print("Pairwise strategy:")
        self._debug_print(f"  Function 1: {len(cases1)} return cases")
        self._debug_print(f"  Function 2: {len(cases2)} return cases")
        self._debug_print(f"  Total pairs to check: {total_pairs}")
        self._debug_print(f"  Per-query timeout: {self.per_query_timeout}s")
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
                
                # クエリ生成
                query = self._build_pair_query(
                    base_ctx, case1, case2,
                    param_replace_fn1, param_replace_fn2,
                    pair_id
                )
                
                if save_formula:
                    last_formula = query
                
                # ソルバー実行（タイムアウトを短く）
                result = self._solve_query(query, pair_id)
                
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
                    self._debug_print(f"  Pair {pair_id}: UNKNOWN/TIMEOUT")
            
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
            return_var1="return_1",  # pairwiseでは実際には使わないが互換性のため
            return_var2="return_2",
            constrained_fragments=base_ctx.get('constrained_fragments', []),
            total_pairs=total_pairs,
            unsat_pairs=unsat_count,
            sat_pairs=sat_count,
            unknown_pairs=unknown_count,
            error_pairs=error_count,
            sat_pair_info=sat_pair_info
        )
    
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
        """
        ペア(i,j)用のSMTクエリを構築
        
        構成:
        1. 共通ヘッダ（set-logic, パラメータ宣言）
        2. パラメータ等価制約
        3. UB除外制約
        4. 追加変数制約
        5. case1の条件 (C1_i)
        6. case2の条件 (C2_j)
        7. 値の非等価 (V1_i ≠ V2_j)
        8. check-sat, get-model
        """
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
    
    def _solve_query(self, query: str, pair_id: str) -> 'QueryResult':
        """
        クエリをソルバーで実行
        
        Returns:
            QueryResult (簡易版の結果)
        """
        # タイムアウトを短く設定
        old_timeout = self.solver_runner.timeout
        self.solver_runner.timeout = self.per_query_timeout
        
        try:
            # 並列実行は不要（クエリが小さいので）
            parallel_result = self.solver_runner.run_sequential(query)
            
            counterexample_raw = None
            if parallel_result.is_equivalent is False:
                counterexample_raw = parallel_result.get_counterexample()
            
            return QueryResult(
                is_equivalent=parallel_result.is_equivalent,
                counterexample_raw=counterexample_raw
            )
        
        finally:
            self.solver_runner.timeout = old_timeout
    
    def _create_aggregate_result(
        self,
        is_equivalent: Optional[bool],
        elapsed_time: float,
        counterexample_raw: Optional[Dict]
    ) -> ParallelResult:
        """
        Pairwise結果を集約してParallelResultを作成
        """
        # 簡易的な SolverResult を作成
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
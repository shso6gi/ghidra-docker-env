# -*- coding: utf-8 -*-
"""戦略基底クラス"""

from abc import ABC, abstractmethod
from typing import Optional, Dict, Any, List
from dataclasses import dataclass, field

from ...model import FunctionReturnAnalysis
from ...smt import ParallelResult


@dataclass
class StrategyResult:
    """戦略実行結果"""
    is_equivalent: Optional[bool]
    solver_results: ParallelResult
    smt_formula: Optional[str] = None
    counterexample_raw: Optional[Dict] = None
    return_var1: Optional[str] = None
    return_var2: Optional[str] = None
    constrained_fragments: List[str] = field(default_factory=list)
    
    # Pairwise 専用フィールド
    total_pairs: int = 0
    unsat_pairs: int = 0
    sat_pairs: int = 0
    unknown_pairs: int = 0
    error_pairs: int = 0
    sat_pair_info: Optional[Dict[str, Any]] = None  # (i, j, conditions, values)


class CheckStrategy(ABC):
    """等価性判定戦略の基底クラス"""
    
    def __init__(self, formula_builder, solver_runner, debug: bool = False):
        """
        Args:
            formula_builder: FormulaBuilder インスタンス
            solver_runner: ParallelSolverRunner インスタンス
            debug: デバッグモード
        """
        self.formula_builder = formula_builder
        self.solver_runner = solver_runner
        self.debug = debug
    
    @abstractmethod
    def check(
        self,
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
        save_formula: bool = False
    ) -> StrategyResult:
        """
        等価性をチェック
        
        Args:
            analysis1: 関数1の解析結果
            analysis2: 関数2の解析結果
            save_formula: SMT式を保存するか
        
        Returns:
            StrategyResult
        """
        pass
    
    def _debug_print(self, msg: str):
        """デバッグ出力"""
        if self.debug:
            print(f"[{self.__class__.__name__}] {msg}")
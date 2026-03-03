# -*- coding: utf-8 -*-
"""等価性判定戦略モジュール"""

from .base import CheckStrategy, StrategyResult
from .monolithic import MonolithicStrategy
from .pairwise import PairwiseStrategy

__all__ = [
    'CheckStrategy',
    'StrategyResult',
    'MonolithicStrategy',
    'PairwiseStrategy',
]


def create_strategy(
    strategy_name: str,
    formula_builder,
    solver_runner,
    debug: bool = False
) -> CheckStrategy:
    """
    戦略を作成
    
    Args:
        strategy_name: "monolithic" or "pairwise"
        formula_builder: FormulaBuilder インスタンス
        solver_runner: ParallelSolverRunner インスタンス
        debug: デバッグモード
    
    Returns:
        CheckStrategy インスタンス
    """
    strategies = {
        'monolithic': MonolithicStrategy,
        'pairwise': PairwiseStrategy,
    }
    
    strategy_class = strategies.get(strategy_name.lower())
    if strategy_class is None:
        raise ValueError(
            f"Unknown strategy: {strategy_name}. "
            f"Available: {list(strategies.keys())}"
        )
    
    return strategy_class(formula_builder, solver_runner, debug=debug)
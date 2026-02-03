# -*- coding: utf-8 -*-
"""等価性判定パッケージ"""

from .checker import EquivalenceChecker, EquivalenceResult, FunctionSignature
from .formula_builder import FormulaBuilder, FormulaBuilderResult
from .type_fixer import TypeFixer, TypeFixerConfig, TypeFixResult
from .counterexample import CounterexampleFormatter, FormattedCounterexample
from .variable_analyzer import (
    VariableAnalyzer,
    ExtraVariableAnalysis,
    VariableUsageInfo,
    ConstraintRecommendation,
    get_safe_zero_constraints
)

__all__ = [
    'EquivalenceChecker',
    'EquivalenceResult',
    'FunctionSignature',
    'FormulaBuilder',
    'FormulaBuilderResult',
    'TypeFixer',
    'TypeFixerConfig',
    'TypeFixResult',
    'CounterexampleFormatter',
    'FormattedCounterexample',
    'VariableAnalyzer',
    'ExtraVariableAnalysis',
    'VariableUsageInfo',
    'ConstraintRecommendation',
    'get_safe_zero_constraints',
]
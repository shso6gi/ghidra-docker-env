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
from .expression_rewriter import (
    ExpressionRewriter,
    RewriteRule,
    RewriteResult,
    ModuloExpansionRule,
    ModuloToExpansionRule,
    rewrite_analysis_returns,
)

__all__ = [
    # Checker
    "EquivalenceChecker",
    "EquivalenceResult",
    "FunctionSignature",
    # Formula
    "FormulaBuilder",
    # Type Fixer
    "TypeFixer",
    "TypeFixerConfig",
    "TypeFixResult",
    # Counterexample
    "CounterexampleFormatter",
    "FormattedCounterexample",
    # Variable Analyzer
    'VariableAnalyzer',
    'ExtraVariableAnalysis',
    'VariableUsageInfo',
    'ConstraintRecommendation',
    'get_safe_zero_constraints',
    # Rewriter
    "ExpressionRewriter",
    "RewriteRule",
    "RewriteResult",
    "ModuloExpansionRule",
    "ModuloToExpansionRule",
    "rewrite_analysis_returns",
]
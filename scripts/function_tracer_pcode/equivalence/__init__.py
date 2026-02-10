# -*- coding: utf-8 -*-
"""等価性判定パッケージ"""
from .checker import EquivalenceChecker
from .result import EquivalenceResult, RewriteInfo
from .formula import (
    FormulaBuilder, 
    FormulaBuilderResult,
    ParameterInfo,
    ExtraVariableInfo,
    ParameterPair,
    VariableAnalyzer,
    ExtraVariableAnalysis,
    VariableClassification,
    ExtensionType,
    ParameterFragmentInfo,
    get_parameter_fragment_constraints,
)
from .type_fixer import TypeFixer, TypeFixerConfig, TypeFixResult
from .counterexample import CounterexampleFormatter, FormattedCounterexample
from ..transform import (
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
    "RewriteInfo",
    # Formula Builder
    "FormulaBuilder",
    "FormulaBuilderResult",
    "ParameterInfo",
    "ExtraVariableInfo",
    "ParameterPair",
    # Variable Analyzer
    'VariableAnalyzer',
    'ExtraVariableAnalysis',
    'VariableClassification',
    'ExtensionType',
    'ParameterFragmentInfo',
    'get_parameter_fragment_constraints',
    # Type Fixer
    "TypeFixer",
    "TypeFixerConfig",
    "TypeFixResult",
    # Counterexample
    "CounterexampleFormatter",
    "FormattedCounterexample",
    # Expression Rewriter
    'ExpressionRewriter',
    'RewriteRule',
    'RewriteResult',
    'ModuloExpansionRule',
    'ModuloToExpansionRule',
    'rewrite_analysis_returns',
]

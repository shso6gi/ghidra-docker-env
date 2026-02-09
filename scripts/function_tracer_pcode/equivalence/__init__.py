# -*- coding: utf-8 -*-
"""等価性判定パッケージ"""
from .checker import EquivalenceChecker, EquivalenceResult, FunctionSignature
from .formula_builder import (
    FormulaBuilder, 
    FormulaBuilderResult,
    ParameterInfo,
    ExtraVariableInfo,
    ParameterPair,
)
from .type_fixer import TypeFixer, TypeFixerConfig, TypeFixResult
from .counterexample import CounterexampleFormatter, FormattedCounterexample
from .variable_analyzer import (
    VariableAnalyzer,
    ExtraVariableAnalysis,
    VariableClassification,
    ExtensionType,
    ParameterFragmentInfo,
    get_parameter_fragment_constraints,
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

    # Formula Builder
    "FormulaBuilder",
    "FormulaBuilderResult",
    "ParameterInfo",
    "ExtraVariableInfo",
    "ParameterPair",
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
    'VariableClassification',
    'ExtensionType',
    'ParameterFragmentInfo',
    'get_parameter_fragment_constraints',
    
    # Rewriter
    "ExpressionRewriter",
    "RewriteRule",
    "RewriteResult",
    "ModuloExpansionRule",
    "ModuloToExpansionRule",
    "rewrite_analysis_returns",
]
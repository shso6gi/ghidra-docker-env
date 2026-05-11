# -*- coding: utf-8 -*-
"""等価性判定層.

Public imports stay concentrated here while internal responsibilities are
split across checker/workflow/reanalysis/attempts/result helpers.
"""

from .checker import EquivalenceChecker
from .result import EquivalenceResult, RewriteInfo
from .typing.fixer import TypeFixer, TypeFixerConfig, TypeFixResult
from .typing.helpers import is_long_type, is_int_type, is_unsigned_type, get_type_name_from_param
from .arch.detector import ArchitectureDetector
from .arch.mips64 import MIPS64Handler
from .phases.handler import PhaseHandler, PhaseContext
from .counterexample import CounterexampleFormatter, FormattedCounterexample
from .formula import FormulaBuilder, ParameterFragmentInfo
from .strategies import CheckStrategy, MonolithicStrategy, PairwiseStrategy
from .unknown_reason import (
    UnknownAggregationUnit,
    UnknownDecisionEffect,
    UnknownRecoveryAction,
    UnknownRecoveryActionStatus,
    UnknownReasonClass,
    UnknownReasonId,
    UnknownReasonRecord,
    UnknownReasonScope,
    UnknownRecoveryPlan,
    UnknownRecoveryProofObligation,
    UnknownRecoveryProofKind,
    build_unknown_recovery_actions,
    get_unknown_recovery_plan,
    summarize_unknown_recovery_backlog,
)

__all__ = [
    # メインクラス
    "EquivalenceChecker",
    
    # 結果
    "EquivalenceResult",
    "RewriteInfo",
    
    # 型補正
    "TypeFixer",
    "TypeFixerConfig",
    "TypeFixResult",
    
    # 型ヘルパー
    "is_long_type",
    "is_int_type",
    "is_unsigned_type",
    "get_type_name_from_param",
    
    # アーキテクチャ
    "ArchitectureDetector",
    "MIPS64Handler",
    
    # Phase管理
    "PhaseHandler",
    "PhaseContext",
    
    # 反例
    "CounterexampleFormatter",
    "FormattedCounterexample",
    
    # SMT式構築
    "FormulaBuilder",
    "ParameterFragmentInfo",

    'CheckStrategy',
    'MonolithicStrategy',
    'PairwiseStrategy',
    "UnknownAggregationUnit",
    "UnknownDecisionEffect",
    "UnknownRecoveryAction",
    "UnknownRecoveryActionStatus",
    "UnknownReasonClass",
    "UnknownReasonId",
    "UnknownReasonRecord",
    "UnknownReasonScope",
    "UnknownRecoveryPlan",
    "UnknownRecoveryProofObligation",
    "UnknownRecoveryProofKind",
    "build_unknown_recovery_actions",
    "get_unknown_recovery_plan",
    "summarize_unknown_recovery_backlog",
]

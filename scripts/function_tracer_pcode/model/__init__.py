# -*- coding: utf-8 -*-
"""データモデル層.

``Expression`` は AST の中核を保持し、render / variable collection /
``Condition`` は専用モジュールへ分離されている。
"""

from .storage import StorageInfo
from .analysis import DeferredCallInfo, ReturnInfo, FunctionReturnAnalysis, SignednessResult
from .expression import Expression, ExpressionType
from .condition import Condition
from .signature import (
    FunctionSignature,
    SignatureHypothesis,
    ResolvedTypeSpec,
    resolve_type_spec,
    resolve_signed_counterpart_spec,
)

__all__ = [
    "StorageInfo",
    "DeferredCallInfo",
    "ReturnInfo",
    "FunctionReturnAnalysis",
    "Expression",
    "ExpressionType",
    "Condition",
    "SignednessResult",
    "FunctionSignature",
    "SignatureHypothesis",
    "ResolvedTypeSpec",
    "resolve_type_spec",
    "resolve_signed_counterpart_spec",
]

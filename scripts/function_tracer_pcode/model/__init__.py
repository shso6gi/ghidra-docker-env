# -*- coding: utf-8 -*-
"""データモデル層.

``Expression`` は AST の中核を保持し、render / variable collection /
``Condition`` は専用モジュールへ分離されている。
"""

from .storage import StorageInfo
from .analysis import DeferredCallInfo, ReturnInfo, FunctionReturnAnalysis, SignednessResult
from .expression import Expression, ExpressionType
from .condition import Condition
from .structural import StructuralKey, expression_key, condition_key, key_contains_placeholder
from .signature import (
    FunctionSignature,
    SignatureHypothesis,
    ResolvedTypeSpec,
    is_suspicious_undefined_data_type,
    resolve_integer_type_spec,
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
    "StructuralKey",
    "expression_key",
    "condition_key",
    "key_contains_placeholder",
    "SignednessResult",
    "FunctionSignature",
    "SignatureHypothesis",
    "ResolvedTypeSpec",
    "is_suspicious_undefined_data_type",
    "resolve_integer_type_spec",
    "resolve_type_spec",
    "resolve_signed_counterpart_spec",
]

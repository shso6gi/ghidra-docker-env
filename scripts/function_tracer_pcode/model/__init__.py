# -*- coding: utf-8 -*-
"""データモデル層.

``Expression`` は AST の中核を保持し、render / variable collection /
``Condition`` は専用モジュールへ分離されている。
"""

from .storage import StorageInfo
from .call_target import CallTargetRef, coerce_call_target_ref
from .runtime_refs import (
    AddressValueRef,
    CanonicalLocation,
    DeferredCallRef,
    LocationBaseRef,
    LocationStep,
    ObservedMemoryReadRef,
    PostStateReadRef,
    PostStateSnapshotRef,
    PostStateValueRef,
    PcodeOpRef,
    UnknownValueRef,
)
from .intrinsics import (
    PTRADD_OPCODE,
    PTRSUB_OPCODE,
    PcodeIntrinsicSpec,
    is_supported_pcode_intrinsic,
    resolve_pcode_intrinsic,
)
from .analysis import (
    ComparisonSurface,
    DeferredCallInfo,
    ReturnInfo,
    FunctionReturnAnalysis,
    SignednessResult,
)
from .expression import Expression, ExpressionType
from .condition import Condition
from .structural import (
    StructuralKey,
    expression_key,
    expression_key_safe,
    expression_key_or_identity,
    condition_key,
    key_contains_placeholder,
    key_is_comparable,
)
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
    "CallTargetRef",
    "coerce_call_target_ref",
    "AddressValueRef",
    "CanonicalLocation",
    "DeferredCallRef",
    "LocationBaseRef",
    "LocationStep",
    "ObservedMemoryReadRef",
    "PostStateReadRef",
    "PostStateSnapshotRef",
    "PostStateValueRef",
    "PcodeOpRef",
    "UnknownValueRef",
    "PTRADD_OPCODE",
    "PTRSUB_OPCODE",
    "PcodeIntrinsicSpec",
    "is_supported_pcode_intrinsic",
    "resolve_pcode_intrinsic",
    "DeferredCallInfo",
    "ComparisonSurface",
    "ReturnInfo",
    "FunctionReturnAnalysis",
    "Expression",
    "ExpressionType",
    "Condition",
    "StructuralKey",
    "expression_key",
    "expression_key_safe",
    "expression_key_or_identity",
    "condition_key",
    "key_contains_placeholder",
    "key_is_comparable",
    "SignednessResult",
    "FunctionSignature",
    "SignatureHypothesis",
    "ResolvedTypeSpec",
    "is_suspicious_undefined_data_type",
    "resolve_integer_type_spec",
    "resolve_type_spec",
    "resolve_signed_counterpart_spec",
]

# -*- coding: utf-8 -*-
"""Compatibility re-export shim（Phase 7-1a, #97）。

canonical な実装は :mod:`scripts.function_tracer_pcode.proof.cause_identity` へ移動した。
本 module は旧 import path を維持するためだけに同一 object を再輸出する（新しい class / 関数は定義しない）。
repository 内部の import は canonical path を使うこと。本 shim は Phase 7-4 の compatibility audit で
公開互換性を確認した上で削除される。
"""

from scripts.function_tracer_pcode.proof.cause_identity import (  # noqa: F401
    CAUSE_IDENTITY_SCHEMA_VERSION,
    PROOF_REQUIREMENT_SCHEMA_VERSION,
    CauseKey,
    ExecutionCauseKey,
    IdentityScope,
    LegacyProofObligationId,
    ProofRequirementContract,
    ProofRequirementId,
    RelationalCauseKey,
    UnaryCauseKey,
    _cause_to_dict,
    _tuple,
    _tuple_item,
    canonical_cause_tuple,
    cause_key_from_dict,
)

__all__ = [
    "CAUSE_IDENTITY_SCHEMA_VERSION",
    "PROOF_REQUIREMENT_SCHEMA_VERSION",
    "CauseKey",
    "ExecutionCauseKey",
    "IdentityScope",
    "LegacyProofObligationId",
    "ProofRequirementContract",
    "ProofRequirementId",
    "RelationalCauseKey",
    "UnaryCauseKey",
    "canonical_cause_tuple",
    "cause_key_from_dict",
]

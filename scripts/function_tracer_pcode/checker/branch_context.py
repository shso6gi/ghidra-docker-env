"""Compatibility re-export shim（Phase 7-2, #97）。

canonical な実装は :mod:`scripts.function_tracer_pcode.proof.obligations.branch_context` へ移動した。
本 module は旧 import path を維持するためだけに同一 object を再輸出する（class / 関数を再定義しない）。
production code は canonical path を使うこと。本 shim は Phase 7-4 の compatibility audit まで残す。
"""

from scripts.function_tracer_pcode.proof.obligations.branch_context import (  # noqa: F401
    BranchCheckContext,
    build_branch_check_context,
)

__all__ = ["BranchCheckContext", "build_branch_check_context"]

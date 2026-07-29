# -*- coding: utf-8 -*-
"""Compatibility facade for StructuralRecurrenceSummarizer."""
from __future__ import annotations

from .recurrence._shared import *

class StructuralRecurrenceSummarizer:
    """
    Recover conservative closed-form summaries for simple scalar recurrences.

    The current implementation intentionally focuses on a sound, reusable subset:
    single-parameter, unit-step, additive self-recursive functions of the form

      f(n) = base                  when n <= L
      f(n) = f(n - 1) + (a*n + b)  when n > L

    If the pattern cannot be proved from the already recovered return cases and the
    function's direct self-call site, the summarizer declines and the caller falls
    back to the existing path-sensitive analysis.
    """

    _SIGNED_GT_OPS = {"INT_SLESS", "INT_SLESSEQUAL"}

    def __init__(
        self,
        tracer,
        debug: bool = False,
        *,
        enable_completed_recovery_proofs: bool = True,
    ):
        self.tracer = tracer
        self.debug = debug
        self.enable_completed_recovery_proofs = bool(enable_completed_recovery_proofs)

    def __getattr__(self, name: str):
        from .recurrence import resolve_method
        implementation = resolve_method(name)
        if implementation is None:
            raise AttributeError(f"{self.__class__.__name__!s} has no attribute {name!r}")
        from types import MethodType
        return MethodType(implementation, self)

    def has_summary_candidate(self, function, high_function, analysis) -> bool:
        from .recurrence.return_region import invoke as _invoke
        return _invoke("has_summary_candidate", self, function, high_function, analysis)

    def try_summarize_function(self, function, high_function, analysis) -> Optional[Tuple[List[ReturnInfo], str]]:
        from .recurrence.coordinator_1 import invoke as _invoke
        return _invoke("try_summarize_function", self, function, high_function, analysis)

    def try_summarize_pre_return_counted_scalar_loop(
        self,
        function,
        high_function,
        analysis,
        return_ops: Sequence,
    ) -> Optional[Tuple[List[ReturnInfo], str]]:
        from .recurrence.counted_loop_1 import invoke as _invoke
        return _invoke("try_summarize_pre_return_counted_scalar_loop", self, function, high_function, analysis, return_ops)





























































    def _safe_pcode_input_count(self, op) -> int:
        from .recurrence.coordinator_1 import invoke as _invoke
        return _invoke("_safe_pcode_input_count", self, op)



































    @staticmethod
    def _unique_parameters_by_name(parameters: Optional[Sequence[dict]]) -> Dict[str, dict]:
        from .recurrence.coordinator_1 import invoke as _invoke
        return _invoke("_unique_parameters_by_name", parameters)











































    def _extract_counted_scalar_loop_model(
        self,
        high_function,
        analysis,
    ) -> Optional[Tuple[CountedLoopInduction, CountedLoopAccumulator, CountedLoopGuard, Tuple[ResidueLoopCase, ...]]]:
        from .recurrence.counted_loop_1 import invoke as _invoke
        return _invoke("_extract_counted_scalar_loop_model", self, high_function, analysis)























    def _find_cbranch_op(self, block):
        from .recurrence.coordinator_1 import invoke as _invoke
        return _invoke("_find_cbranch_op", self, block)






































    def _build_pcode_expression(
        self,
        varnode,
        *,
        placeholders: Dict[object, Expression],
        _seen=None,
        _memo=None,
    ) -> Optional[Expression]:
        from .recurrence.proof_utils import invoke as _invoke
        return _invoke(
            "_build_pcode_expression",
            self,
            varnode,
            placeholders=placeholders,
            _seen=_seen,
            _memo=_memo,
        )












































    @staticmethod
    def _strict_zero_iteration_exit_region_block_ops(block) -> Optional[Tuple[object, ...]]:
        from .recurrence.return_region import invoke as _invoke
        return _invoke("_strict_zero_iteration_exit_region_block_ops", block)

    @staticmethod
    def _zero_iteration_exit_region_mnemonic_is_safe(mnemonic: object) -> bool:
        from .recurrence.return_region import invoke as _invoke
        return _invoke("_zero_iteration_exit_region_mnemonic_is_safe", mnemonic)










    @staticmethod
    def _summary_expression_evidence_key(expr: Optional[Expression]) -> Optional[Tuple[Any, ...]]:
        from .recurrence.object_identity import invoke as _invoke
        return _invoke("_summary_expression_evidence_key", expr)















































    def _canonicalize_expression(self, expr: Optional[Expression]) -> Optional[Expression]:
        from .recurrence.object_identity import invoke as _invoke
        return _invoke("_canonicalize_expression", self, expr)

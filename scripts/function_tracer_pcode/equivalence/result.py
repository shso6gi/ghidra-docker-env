# -*- coding: utf-8 -*-
"""等価性判定結果のデータモデル"""

from typing import Optional, Dict, Any, List, Tuple
from dataclasses import dataclass, field

from ..model import FunctionSignature
from ..smt import ParallelResult, SolverStatus
from .counterexample import FormattedCounterexample
from .type_fixer import TypeFixResult
from ..transform.rewriter import RewriteResult


@dataclass
class RewriteInfo:
    """リライト情報"""
    applied: bool = False
    function1_rewrites: List[RewriteResult] = field(default_factory=list)
    function2_rewrites: List[RewriteResult] = field(default_factory=list)
    
    def get_summary(self) -> str:
        """リライトの概要を取得"""
        if not self.applied:
            return "No rewrite applied"
        
        lines = ["Rewrite applied:"]
        
        if any(r.was_rewritten for r in self.function1_rewrites):
            lines.append("  Function 1:")
            for i, r in enumerate(self.function1_rewrites):
                if r.was_rewritten:
                    for rule, before, after in r.history:
                        lines.append(f"    Return {i}: [{rule}] {before} -> {after}")
        
        if any(r.was_rewritten for r in self.function2_rewrites):
            lines.append("  Function 2:")
            for i, r in enumerate(self.function2_rewrites):
                if r.was_rewritten:
                    for rule, before, after in r.history:
                        lines.append(f"    Return {i}: [{rule}] {before} -> {after}")
        
        return "\n".join(lines)
    
    def to_dict(self) -> Dict[str, Any]:
        return {
            "applied": self.applied,
            "function1_rewrites": [
                {"was_rewritten": r.was_rewritten, "history": r.history}
                for r in self.function1_rewrites
            ],
            "function2_rewrites": [
                {"was_rewritten": r.was_rewritten, "history": r.history}
                for r in self.function2_rewrites
            ],
        }


@dataclass
class EquivalenceResult:
    """等価性判定の結果"""
    is_equivalent: Optional[bool]
    function1_name: str
    function2_name: str
    binary1_name: str
    binary2_name: str
    solver_results: ParallelResult
    counterexample: Optional[FormattedCounterexample] = None
    smt_formula: Optional[str] = None
    total_time: float = 0.0
    error_message: Optional[str] = None
    type_fix_result: Optional[TypeFixResult] = None
    retry_count: int = 0
    function1_signature: Optional[FunctionSignature] = None
    function2_signature: Optional[FunctionSignature] = None
    constrained_fragments: List[str] = field(default_factory=list)
    rewrite_info: Optional[RewriteInfo] = None
    mips64_abi_constraints: Optional[Dict[str, Tuple[str, int]]] = None  # 追加
    
    def is_timeout(self) -> bool:
        """タイムアウトで結果が不明かどうかを判定"""
        if self.is_equivalent is not None:
            return False
        if not self.solver_results or not self.solver_results.results:
            return False
        for sr in self.solver_results.results:
            if sr.status == SolverStatus.TIMEOUT:
                return True
        return False
    
    def is_unknown(self) -> bool:
        """結果が不明（タイムアウト含む）かどうかを判定"""
        return self.is_equivalent is None and self.error_message is None
    
    def has_critical_error(self) -> bool:
        """致命的なエラー（リトライ不可能）があるかどうかを判定"""
        if self.error_message is None:
            return False
        critical_keywords = ["not found", "not available", "No SMT solvers"]
        return any(kw in self.error_message for kw in critical_keywords)
    
    def to_dict(self) -> Dict[str, Any]:
        return {
            "is_equivalent": self.is_equivalent,
            "function1_name": self.function1_name,
            "function2_name": self.function2_name,
            "binary1_name": self.binary1_name,
            "binary2_name": self.binary2_name,
            "function1_signature": self.function1_signature.to_dict() if self.function1_signature else None,
            "function2_signature": self.function2_signature.to_dict() if self.function2_signature else None,
            "solver_results": self.solver_results.to_dict() if self.solver_results else None,
            "counterexample": self.counterexample.to_string("json") if self.counterexample else None,
            "total_time": self.total_time,
            "error_message": self.error_message,
            "type_fix_result": self.type_fix_result.to_dict() if self.type_fix_result else None,
            "retry_count": self.retry_count,
            "is_timeout": self.is_timeout(),
            "constrained_fragments": self.constrained_fragments,
            "rewrite_info": self.rewrite_info.to_dict() if self.rewrite_info else None,
        }
    
    def to_string(self, verbose: bool = False) -> str:
        lines = []
        lines.append("=" * 70)
        lines.append("EQUIVALENCE CHECK RESULT")
        lines.append("=" * 70)
        
        # Binary 1 の情報
        lines.append(f"Binary 1: {self.binary1_name}")
        lines.append(f"Function 1: {self.function1_name}")
        if self.function1_signature:
            lines.append(f"  Original signature: {self.function1_signature.format_full(self.function1_name)}")
        
        lines.append("")
        
        # Binary 2 の情報
        lines.append(f"Binary 2: {self.binary2_name}")
        lines.append(f"Function 2: {self.function2_name}")
        if self.function2_signature:
            lines.append(f"  Original signature: {self.function2_signature.format_full(self.function2_name)}")
        
        lines.append("")
        
        # パラメータ断片として制約された変数を表示
        if self.constrained_fragments:
            vars_str = ", ".join(self.constrained_fragments)
            lines.append(f"Derived fragments: {vars_str}")
            lines.append(f"  (upper-bits variables constrained via sign/zero extension from parameters)")
        
        if self.type_fix_result and self.type_fix_result.any_fix_applied():
            lines.append(f"Type fix applied: {self.type_fix_result}")
        if self.retry_count > 0:
            lines.append(f"Retry count: {self.retry_count}")
        
        # リライト情報
        if self.rewrite_info and self.rewrite_info.applied:
            lines.append("")
            lines.append(self.rewrite_info.get_summary())
        
        lines.append("-" * 70)
        
        if self.error_message:
            lines.append(f"ERROR: {self.error_message}")
        elif self.is_equivalent is None:
            if self.is_timeout():
                lines.append("Result: TIMEOUT (could not determine equivalence within time limit)")
            else:
                lines.append("Result: UNKNOWN (could not determine equivalence)")
        elif self.is_equivalent:
            lines.append("Result: EQUIVALENT ✓")
        else:
            lines.append("Result: NOT EQUIVALENT ✗")
            if self.counterexample:
                lines.append("")
                lines.append(self.counterexample.to_string())
            else:
                lines.append("")
                lines.append("(No counterexample available)")
        
        lines.append("-" * 70)
        lines.append(f"Total time: {self.total_time:.3f} seconds")
        
        if verbose and self.solver_results:
            lines.append("")
            lines.append("Solver Results:")
            for sr in self.solver_results.results:
                status_str = sr.status.name
                lines.append(f"  {sr.solver_name}: {status_str} ({sr.elapsed_time:.3f}s)")
                if sr.error_message:
                    lines.append(f"    Error: {sr.error_message}")
                if sr.model:
                    lines.append(f"    Model: {sr.model}")
        
        lines.append("=" * 70)
        return "\n".join(lines)

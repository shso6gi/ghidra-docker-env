# -*- coding: utf-8 -*-
"""デバッグトレース統合テスト（既存テストとの互換性確認）"""

import pytest
from scripts.function_tracer_pcode.proof.strategies.base import StrategyResult



def test_final_smt_excerpt_compatibility():
    """final_smt_excerpt 互換性が維持されていることを確認"""
    from scripts.function_tracer_pcode.checker.debug_trace import Attempt
    
    # final_smt_excerpt と final_smt の両方を持つ Attempt をシミュレート
    attempt = Attempt(
        attempt_id=0,
        retry_count=0,
        phase="P4A_MIPS64_ABI",
        stage_path=["S_PAIRWISE"],
        strategy="pairwise",
        result=True,
        transition_reason="UNSAT",
        final_smt_excerpt="(declare-fun x () (_ BitVec 64))",
        final_smt="(declare-fun x () (_ BitVec 64))\n(assert (= x #x0000000000000000))\n(check-sat)",
        elapsed_time=0.5
    )
    
    # to_dict() が両方含むこと
    attempt_dict = attempt.to_dict()
    assert "final_smt_excerpt" in attempt_dict
    assert "final_smt" in attempt_dict
    assert attempt_dict["final_smt_excerpt"] == "(declare-fun x () (_ BitVec 64))"
    assert len(attempt_dict["final_smt"]) > len(attempt_dict["final_smt_excerpt"])
    
    # final_smt_excerpt は final_smt の先頭部分であること
    assert attempt_dict["final_smt"].startswith(attempt_dict["final_smt_excerpt"][:50])
    
    print("✓ final_smt_excerpt compatibility maintained")

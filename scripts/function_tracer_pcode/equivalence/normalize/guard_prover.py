# -*- coding: utf-8 -*-
"""SMTガード条件証明器"""

from typing import List, Tuple


def prove_guard_condition(
    base_ctx,
    case1_conditions_smt: List[str],
    case2_conditions_smt: List[str],
    guard_expr_smt: str,
    solver_runner,
    timeout: int = 2,
    debug: bool = False
) -> Tuple[bool, str]:
    """
    SMTで guard_expr_smt が必ず成立するか証明
    
    証明方法：
        case1_conds ∧ case2_conds ∧ ¬guard_expr が UNSAT なら、
        guard_expr は必ず成立する
    
    Args:
        base_ctx: 共通SMT部分（param宣言・制約）
        case1_conditions_smt: case1の条件SMT式のリスト
        case2_conditions_smt: case2の条件SMT式のリスト
        guard_expr_smt: 証明したいガード条件のSMT式
        solver_runner: ソルバー実行器
        timeout: タイムアウト（秒）
        debug: デバッグ出力
    
    Returns:
        (is_proven, error_message)
        - is_proven: True if guard is proven (UNSAT = guard が必ず成立)
        - error_message: エラーがあった場合のメッセージ（""なら正常）
    """
    lines = []
    
    lines.append("; Guard condition proof")
    lines.append("(set-logic QF_BV)")
    lines.append("")
    
    # 共通部分（param宣言・制約）
    lines.extend(base_ctx['header_lines'])
    
    # case1の条件
    if case1_conditions_smt:
        lines.append("; Case1 conditions")
        for cond_smt in case1_conditions_smt:
            lines.append(f"(assert {cond_smt})")
        lines.append("")
    
    # case2の条件
    if case2_conditions_smt:
        lines.append("; Case2 conditions")
        for cond_smt in case2_conditions_smt:
            lines.append(f"(assert {cond_smt})")
        lines.append("")
    
    # guard の否定をアサート
    lines.append("; Negation of guard (UNSAT = guard is proven)")
    lines.append(f"(assert (not {guard_expr_smt}))")
    lines.append("")
    lines.append("(check-sat)")
    
    query = "\n".join(lines)
    
    if debug:
        print(f"[GuardProver] Proving guard: {guard_expr_smt[:80]}...")
    
    # ソルバー実行
    old_timeout = solver_runner.timeout
    solver_runner.timeout = timeout
    
    try:
        result = solver_runner.run_sequential(query)
        
        # エラーチェック
        if result.results:
            from ...smt import SolverStatus
            for solver_result in result.results:
                if solver_result.status == SolverStatus.ERROR:
                    error_msg = solver_result.error_message or "Unknown error"
                    
                    # パースエラーの詳細を抽出
                    if "unknown constant" in error_msg:
                        import re
                        match = re.search(r'unknown constant (\w+)', error_msg)
                        if match:
                            unknown_sym = match.group(1)
                            error_msg = f"Parse error: unknown constant '{unknown_sym}' - symbol not replaced?"
                    
                    if debug:
                        print(f"[GuardProver] ERROR: {error_msg}")
                    
                    return False, error_msg
        
        # UNSAT = guard が必ず成立
        is_proven = result.is_equivalent is True
        
        if debug:
            status_str = "PROVEN (UNSAT)" if is_proven else "NOT PROVEN (SAT/UNKNOWN)"
            print(f"[GuardProver] Result: {status_str}")
        
        return is_proven, ""
    
    finally:
        solver_runner.timeout = old_timeout
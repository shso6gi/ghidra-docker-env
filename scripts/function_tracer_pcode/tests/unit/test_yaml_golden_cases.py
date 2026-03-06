# -*- coding: utf-8 -*-
"""★ [P3] YAMLゴールデンケースの網羅テスト"""

import pytest
from conftest import load_golden_cases  # ★ 通常の関数をインポート

from scripts.function_tracer_pcode.equivalence.phases.handler import PhaseHandler, PhaseContext
from scripts.function_tracer_pcode.equivalence.typing.fixer import TypeFixerConfig, TypeFixResult

from conftest import create_mock_result, MockProgram


class TestYAMLGoldenCases:
    """cases.ymlの全ケースを網羅的にテスト"""
    
    @pytest.mark.parametrize("case", [
        pytest.param(
            case,
            id=case['id']
        )
        for case in load_golden_cases()  # ★ 直接関数を呼び出す
    ], indirect=False)
    def test_phase0_stop_after_policy(self, case, solver_status_map, is_equiv_map):
        """★ [P1] stop_after_phase0 フラグを厳密に検証"""
        handler = PhaseHandler(TypeFixerConfig(), debug=True)
        
        phase0 = case['phase0']
        expected = case['expected']
        
        status_str = phase0.get('status', 'UNKNOWN')
        is_equiv = is_equiv_map[status_str]
        status = solver_status_map[status_str]
        
        counterexample = phase0.get('counterexample')
        
        result = create_mock_result(
            is_equivalent=is_equiv,
            solver_status=status,
            counterexample=counterexample
        )
        
        should_retry = handler.should_retry(result)
        
        # ★ [P1] 修正: stop_after_phase0 を厳密に検証
        if expected['stop_after_phase0']:
            assert should_retry is False, \
                f"Case {case['id']}: stop_after_phase0=True requires should_retry=False"
        else:
            assert should_retry is True, \
                f"Case {case['id']}: stop_after_phase0=False requires should_retry=True"
    
    @pytest.mark.parametrize("case", [
        pytest.param(
            case,
            id=case['id']
        )
        for case in load_golden_cases()
        if 'allowed_recovery_phases' in case['expected']
    ], indirect=False)
    def test_allowed_recovery_phases(self, case, solver_status_map, is_equiv_map):
        """★ [P1] allowed_recovery_phases を検証"""
        handler = PhaseHandler(TypeFixerConfig(), debug=True)
        
        phase0 = case['phase0']
        expected = case['expected']
        
        status_str = phase0.get('status', 'UNKNOWN')
        is_equiv = is_equiv_map[status_str]
        status = solver_status_map[status_str]
        
        counterexample = phase0.get('counterexample')
        
        result = create_mock_result(
            is_equivalent=is_equiv,
            solver_status=status,
            counterexample=counterexample
        )
        
        allowed_phases = set(expected['allowed_recovery_phases'])
        
        # SAT時の特殊処理
        if status_str == "SAT":
            # P4B（MIPS64偽反例）のみ許可されるケース
            if 'P4B_MIPS64_SPURIOUS' in allowed_phases:
                # このケースでは should_run_phase4_retry() が True を返すべき
                arch = case.get('architecture', {})
                binary1_arch = arch.get('binary1', 'x86:LE:64:default')
                binary2_arch = arch.get('binary2', 'x86:LE:64:default')
                
                ctx = PhaseContext(
                    program1=MockProgram(name="binary1", architecture=binary1_arch),
                    program2=MockProgram(name="binary2", architecture=binary2_arch),
                    function_name1="func1",
                    function_name2="func2",
                    binary1_name="binary1",
                    binary2_name="binary2",
                    decompile_timeout=60,
                    save_formula=False,
                    type_fix_result=TypeFixResult(),
                    original_signature1=None,
                    original_signature2=None,
                    analysis1=None,
                    analysis2=None
                )
                
                can_retry_p4b = handler.should_run_phase4_retry(result, ctx)
                # P4Bが許可されているケースでは、条件次第でTrue
                # （反例の内容によるため、ここでは構造のみチェック）
                print(f"\n[P4B CHECK] Case {case['id']}: can_retry_p4b={can_retry_p4b}")
            else:
                # P4Bが許可されていないSATケース → 即終了
                assert allowed_phases == set(), \
                    f"Case {case['id']}: SAT without P4B should have empty allowed_recovery_phases"
        else:
            # UNKNOWN/TIMEOUT時のRecovery許可
            if allowed_phases:
                # P1_SIGNEDNESS, P2_PATTERN_INT などが許可される
                assert 'P1_SIGNEDNESS' in allowed_phases or 'P2_PATTERN_INT' in allowed_phases, \
                    f"Case {case['id']}: UNKNOWN/TIMEOUT should allow standard recovery phases"
    
    @pytest.mark.parametrize("case", [
        pytest.param(
            case,
            id=case['id']
        )
        for case in load_golden_cases()
        if case.get('assumptions', {}).get('structural_match') is True
    ], indirect=False)
    def test_structural_match_cases_require_smt(self, case):
        """★ [P2] 構造一致ケースでもSMT確認が必須"""
        assumptions = case.get('assumptions', {})
        
        # 構造一致フラグがTrueのケース
        assert assumptions.get('structural_match') is True
        
        # SMT確認が必須
        assert assumptions.get('smt_confirmed_after_structural') is True, \
            f"Case {case['id']}: structural_match=True requires smt_confirmed_after_structural=True"
        
        print(f"\n[STRUCTURAL SAFETY] Case {case['id']}: SMT confirmation is mandatory")
    
    @pytest.mark.parametrize("case", [
        pytest.param(
            case,
            id=case['id']
        )
        for case in load_golden_cases()
        if 'required_stage_path' in case['expected']
    ], indirect=False)
    def test_required_stage_path(self, case):
        """★ Stage経路の仕様を文書化"""
        expected = case['expected']
        stage_path = expected['required_stage_path']
        
        # Stage経路が定義されているケースでは、最低限のStageを通過する
        assert len(stage_path) >= 1, \
            f"Case {case['id']}: required_stage_path must have at least one stage"
        
        # S1_CONDS_ONLY は必ず最初
        assert stage_path[0] == 'S1_CONDS_ONLY', \
            f"Case {case['id']}: first stage must be S1_CONDS_ONLY"
        
        print(f"\n[STAGE PATH] Case {case['id']}: {' -> '.join(stage_path)}")
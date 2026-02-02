# -*- coding: utf-8 -*-
"""Z3ソルバー実装（デバッグ強化版）"""

import time
from typing import Optional, Dict, Any, Tuple, Callable

from .solver_interface import SMTSolver, SolverResult, SolverStatus


class Z3Solver(SMTSolver):
    """Z3 SMTソルバー"""
    
    def __init__(self, timeout: int = 180, debug: bool = False):
        super().__init__(timeout)
        self._z3 = None
        self._solver = None
        self._model = None
        self.debug = debug
    
    @property
    def name(self) -> str:
        return "Z3"
    
    def _debug_print(self, msg: str):
        if self.debug:
            print(f"[Z3 DEBUG] {msg}")
    
    def check_availability(self) -> Tuple[bool, str]:
        try:
            import z3
            self._z3 = z3
            version = z3.get_version_string()
            return True, f"version {version}"
        except ImportError as e:
            return False, f"Import error: {e}"
        except Exception as e:
            return False, f"Error: {e}"
    
    def check_equivalence_direct(
        self,
        smt_script: str,
        cancellation_token: Optional[Any] = None
    ) -> SolverResult:
        import sys
        self._debug_print("=== Z3 check_equivalence_direct START ===")
        print("[Z3] Method entry", flush=True)  # 強制フラッシュ
        sys.stdout.flush()
        
        if not self.is_available():
            return self._create_error_result("Z3 is not available")
        
        start_time = time.time()
        
        try:
            z3 = self._z3
            if z3 is None:
                raise RuntimeError("Z3 module not loaded")

            solver = z3.Solver()
            self._solver = solver
            self._solver.set("timeout", self.timeout * 1000)  # ミリ秒
            
            # SMT-LIBスクリプトをパース
            try:
                assertions = z3.parse_smt2_string(smt_script)
                self._solver.add(assertions)
                self._debug_print(f"Parsed {len(assertions)} assertions")
            except Exception as e:
                self._debug_print(f"Parse error: {e}")
                return self._create_error_result(f"Parse error: {e}")
            
            # キャンセルチェック
            if cancellation_token and cancellation_token.is_cancelled():
                return SolverResult(
                    solver_name=self.name,
                    status=SolverStatus.UNKNOWN,
                    elapsed_time=time.time() - start_time,
                    error_message="Cancelled before check"
                )
            
            # 検証実行
            self._debug_print("Starting check...")
            result = self._solver.check()
            elapsed = time.time() - start_time
            self._debug_print(f"Check completed: {result} ({elapsed:.3f}s)")
            
            if result == z3.sat:
                self._model = self._solver.model()
                model_dict = self._extract_model()
                self._debug_print(f"Model extracted: {model_dict}")
                return SolverResult(
                    solver_name=self.name,
                    status=SolverStatus.SAT,
                    elapsed_time=elapsed,
                    model=model_dict
                )
            elif result == z3.unsat:
                return SolverResult(
                    solver_name=self.name,
                    status=SolverStatus.UNSAT,
                    elapsed_time=elapsed
                )
            else:
                return SolverResult(
                    solver_name=self.name,
                    status=SolverStatus.UNKNOWN,
                    elapsed_time=elapsed
                )
        
        except Exception as e:
            elapsed = time.time() - start_time
            self._debug_print(f"Exception: {e}")
            if elapsed >= self.timeout:
                return self._create_timeout_result(elapsed)
            return self._create_error_result(str(e))
    
    def _extract_model(self) -> Dict[str, Any]:
        """Z3モデルから辞書を抽出"""
        if self._model is None:
            return {}
        
        result = {}
        for decl in self._model.decls():
            name = decl.name()
            value = self._model[decl]
            
            self._debug_print(f"  Model var: {name} = {value} (type: {type(value).__name__})")
            
            # ビットベクトルを整数に変換（getattr使用で型チェック問題を回避）
            as_long: Optional[Callable[[], int]] = getattr(value, 'as_long', None)
            as_signed_long: Optional[Callable[[], int]] = getattr(value, 'as_signed_long', None)
            
            if as_long is not None:
                result[name] = as_long()
            elif as_signed_long is not None:
                result[name] = as_signed_long()
            else:
                result[name] = str(value)
        
        return result
    
    def get_model(self) -> Optional[Dict[str, Any]]:
        return self._extract_model() if self._model else None
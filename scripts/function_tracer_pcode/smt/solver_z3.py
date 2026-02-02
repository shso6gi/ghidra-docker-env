# -*- coding: utf-8 -*-
# smt/solver_z3.py
"""Z3ソルバー実装（タイムアウト強化版）"""

import time
import threading
from typing import Optional, Dict, Any, Tuple

from .solver_interface import SMTSolver, SolverResult, SolverStatus
from .timeout_handler import run_with_timeout, TimeoutError as CustomTimeoutError


class Z3Solver(SMTSolver):
    """Z3 SMTソルバー"""
    
    def __init__(self, timeout: int = 180, debug: bool = False):
        super().__init__(timeout)
        self._z3 = None
        self._solver = None
        self._model = None
        self.debug = debug
        self._cancelled = threading.Event()
    
    @property
    def name(self) -> str:
        return "Z3"
    
    def _debug_print(self, msg: str):
        if self.debug:
            print(f"[Z3 DEBUG] {msg}", flush=True)
    
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
        self._debug_print("=== Z3 check_equivalence_direct START ===")
        self._cancelled.clear()
        
        if not self.is_available():
            return self._create_error_result("Z3 is not available")
        
        start_time = time.time()
        
        def do_check() -> SolverResult:
            z3 = self._z3
            
            self._solver = z3.Solver()
            # Z3内部タイムアウトも設定（バックアップ）
            self._solver.set("timeout", self.timeout * 1000)
            
            # SMT-LIBスクリプトをパース
            try:
                assertions = z3.parse_smt2_string(smt_script)
                self._solver.add(assertions)
                self._debug_print(f"Parsed {len(assertions)} assertions")
            except Exception as e:
                self._debug_print(f"Parse error: {e}")
                raise
            
            # キャンセルチェック
            if cancellation_token and cancellation_token.is_cancelled():
                raise InterruptedError("Cancelled before check")
            
            if self._cancelled.is_set():
                raise InterruptedError("Cancelled before check")
            
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
        
        # タイムアウト付きで実行
        timeout_result = run_with_timeout(do_check, self.timeout, self.debug)
        
        elapsed = time.time() - start_time
        
        if timeout_result.timed_out:
            self._debug_print(f"Timed out after {elapsed:.3f}s")
            return SolverResult(
                solver_name=self.name,
                status=SolverStatus.TIMEOUT,
                elapsed_time=elapsed,
                error_message=f"Timed out after {self.timeout} seconds"
            )
        
        if timeout_result.error:
            error_msg = str(timeout_result.error)
            if "Cancelled" in error_msg or isinstance(timeout_result.error, InterruptedError):
                return SolverResult(
                    solver_name=self.name,
                    status=SolverStatus.UNKNOWN,
                    elapsed_time=elapsed,
                    error_message="Cancelled"
                )
            return self._create_error_result(error_msg)
        
        return timeout_result.result
    
    def cancel(self):
        """実行をキャンセル"""
        self._cancelled.set()
        if self._solver and hasattr(self._solver, 'interrupt'):
            try:
                self._solver.interrupt()
            except Exception:
                pass
    
    def _extract_model(self) -> Dict[str, Any]:
        """Z3モデルから辞書を抽出"""
        if self._model is None:
            return {}
        
        result = {}
        for decl in self._model.decls():
            name = decl.name()
            value = self._model[decl]
            
            self._debug_print(f"  Model var: {name} = {value} (type: {type(value).__name__})")
            
            if hasattr(value, 'as_long'):
                result[name] = value.as_long()
            elif hasattr(value, 'as_signed_long'):
                result[name] = value.as_signed_long()
            else:
                result[name] = str(value)
        
        return result
    
    def get_model(self) -> Optional[Dict[str, Any]]:
        return self._extract_model() if self._model else None
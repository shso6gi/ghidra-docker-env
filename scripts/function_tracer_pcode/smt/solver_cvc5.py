# -*- coding: utf-8 -*-
# smt/solver_cvc5.py
"""CVC5ソルバー実装（タイムアウト強化版）"""

from __future__ import annotations

import time
import re
import threading
from typing import Optional, Dict, Any, Tuple, List, TYPE_CHECKING

from .solver_interface import SMTSolver, SolverResult, SolverStatus
from .timeout_handler import run_with_timeout, TimeoutError as CustomTimeoutError

if TYPE_CHECKING:
    import cvc5 as cvc5_module


class CVC5Solver(SMTSolver):
    """CVC5 SMTソルバー"""
    
    def __init__(self, timeout: int = 180, debug: bool = False):
        super().__init__(timeout)
        self._cvc5: Optional[Any] = None
        self._solver: Optional[Any] = None
        self._tm: Optional[Any] = None
        self._model: Optional[Dict[str, Any]] = None
        self._declared_consts: Dict[str, Any] = {}
        self.debug = debug
        self._cancelled = threading.Event()
    
    @property
    def name(self) -> str:
        return "CVC5"
    
    def _debug_print(self, msg: str) -> None:
        if self.debug:
            print(f"[CVC5 DEBUG] {msg}", flush=True)
    
    def check_availability(self) -> Tuple[bool, str]:
        try:
            import cvc5
            self._cvc5 = cvc5
            try:
                version = getattr(cvc5, 'Version', 'unknown')
            except Exception:
                version = "available"
            return True, f"cvc5 package {version}"
        except ImportError as e:
            return False, f"Import error: {e}"
        except Exception as e:
            return False, f"Error: {e}"
    
    def check_equivalence_direct(
        self,
        smt_script: str,
        cancellation_token: Optional[Any] = None
    ) -> SolverResult:
        if not self.is_available():
            return self._create_error_result("CVC5 is not available")
        
        start_time = time.time()
        self._declared_consts = {}
        self._cancelled.clear()
        
        def do_check() -> SolverResult:
            cvc5 = self._cvc5
            if cvc5 is None:
                raise RuntimeError("CVC5 module not loaded")
            
            tm = cvc5.TermManager()
            solver = cvc5.Solver(tm)
            self._solver = solver
            self._tm = tm
            
            solver.setOption("produce-models", "true")
            # CVC5内部タイムアウト（ミリ秒）
            solver.setOption("tlimit", str(self.timeout * 1000))
            solver.setLogic("QF_BV")
            
            # キャンセルチェック
            if cancellation_token and cancellation_token.is_cancelled():
                raise InterruptedError("Cancelled")
            if self._cancelled.is_set():
                raise InterruptedError("Cancelled")
            
            self._parse_declarations(smt_script)
            filtered_script = self._filter_script_minimal(smt_script)
            
            self._debug_print(f"Parsing script ({len(filtered_script)} chars)...")
            
            sm = None
            parser = cvc5.InputParser(solver)
            parser.setStringInput(
                cvc5.InputLanguage.SMT_LIB_2_6,
                filtered_script,
                "equivalence_check"
            )
            
            sm = parser.getSymbolManager()
            
            cmd_count = 0
            while True:
                # 定期的にキャンセルチェック
                if cmd_count % 100 == 0:
                    if cancellation_token and cancellation_token.is_cancelled():
                        raise InterruptedError("Cancelled during parsing")
                    if self._cancelled.is_set():
                        raise InterruptedError("Cancelled during parsing")
                
                cmd = parser.nextCommand()
                if cmd.isNull():
                    break
                cmd.invoke(solver, sm)
                cmd_count += 1
            
            self._debug_print(f"Executed {cmd_count} commands")
            self._debug_print("Starting checkSat...")
            
            result = solver.checkSat()
            elapsed = time.time() - start_time
            self._debug_print(f"Check completed: {result} ({elapsed:.3f}s)")
            
            if result.isSat():
                self._model = self._extract_model_via_declared_terms(solver, sm)
                self._debug_print(f"Final model: {self._model}")
                return SolverResult(
                    solver_name=self.name,
                    status=SolverStatus.SAT,
                    elapsed_time=elapsed,
                    model=self._model
                )
            elif result.isUnsat():
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
            if elapsed >= self.timeout:
                return self._create_timeout_result(elapsed)
            return self._create_error_result(error_msg)
        
        return timeout_result.result
    
    def cancel(self):
        """実行をキャンセル"""
        self._cancelled.set()
    
    def _filter_script_minimal(self, smt_script: str) -> str:
        """set-logic, check-sat, get-model, exit のみ除去"""
        lines = smt_script.split('\n')
        filtered = []
        for line in lines:
            stripped = line.strip()
            if stripped.startswith('(set-logic'):
                continue
            if stripped.startswith('(check-sat'):
                continue
            if stripped.startswith('(get-model'):
                continue
            if stripped.startswith('(exit'):
                continue
            filtered.append(line)
        return '\n'.join(filtered)
    
    def _parse_declarations(self, smt_script: str):
        """SMTスクリプトから declare-const を抽出"""
        pattern = r'\(declare-const\s+(\w+)\s+\(_\s*BitVec\s+(\d+)\)\)'
        matches = re.findall(pattern, smt_script)
        
        for name, size in matches:
            self._declared_consts[name] = {
                'size': int(size),
                'term': None
            }
        
        self._debug_print(f"Parsed {len(self._declared_consts)} declarations")
    
    def _extract_model_via_declared_terms(self, solver, sm) -> Dict[str, Any]:
        """getDeclaredTermsを使用してモデルを抽出"""
        result = {}
        
        self._debug_print("=== Model Extraction via getDeclaredTerms ===")
        
        try:
            if sm is not None and hasattr(sm, 'getDeclaredTerms'):
                declared_terms = sm.getDeclaredTerms()
                self._debug_print(f"getDeclaredTerms returned {len(declared_terms)} terms")
                
                for term in declared_terms:
                    try:
                        term_name = self._get_term_name(term)
                        
                        if term_name is None:
                            continue
                        
                        if term_name not in self._declared_consts:
                            continue
                        
                        value = solver.getValue(term)
                        int_val = self._bv_to_int(value)
                        
                        if int_val is not None:
                            result[term_name] = int_val
                        else:
                            result[term_name] = str(value)
                            
                    except Exception as e:
                        self._debug_print(f"    Error processing term: {e}")
                
                if result:
                    return result
        
        except Exception as e:
            self._debug_print(f"getDeclaredTerms extraction failed: {e}")
        
        return self._extract_model_from_assertions(solver)
    
    def _get_term_name(self, term) -> Optional[str]:
        """Termから名前を取得"""
        try:
            if hasattr(term, 'getSymbol'):
                sym = term.getSymbol()
                if sym:
                    return sym
            
            term_str = str(term)
            
            if term_str.isidentifier():
                return term_str
            
            match = re.match(r'(param_\d+_\d+)', term_str)
            if match:
                return match.group(1)
            
        except Exception:
            pass
        
        return None
    
    def _extract_model_from_assertions(self, solver) -> Dict[str, Any]:
        """アサーションから変数を抽出してモデルを取得"""
        result = {}
        
        try:
            assertions = solver.getAssertions()
            
            free_vars = []
            visited = set()
            for assertion in assertions:
                self._collect_bv_vars(assertion, free_vars, visited)
            
            for var in free_vars:
                try:
                    var_name = self._get_term_name(var)
                    if not var_name or var_name.startswith('return_'):
                        continue
                    
                    if var_name not in self._declared_consts:
                        continue
                    
                    value = solver.getValue(var)
                    int_val = self._bv_to_int(value)
                    if int_val is not None:
                        result[var_name] = int_val
                    else:
                        result[var_name] = str(value)
                        
                except Exception:
                    pass
        
        except Exception:
            pass
        
        return result
    
    def _collect_bv_vars(self, term, vars_list: list, visited: set):
        """ビットベクトル変数を収集"""
        term_str = str(term)
        if term_str in visited:
            return
        visited.add(term_str)
        
        try:
            kind = term.getKind()
            kind_name = kind.name if hasattr(kind, 'name') else str(kind)
            
            if kind_name == 'CONSTANT':
                sort = term.getSort()
                if sort.isBitVector():
                    vars_list.append(term)
                return
            
            for i in range(term.getNumChildren()):
                self._collect_bv_vars(term[i], vars_list, visited)
                
        except Exception:
            pass
    
    def _bv_to_int(self, value) -> Optional[int]:
        """ビットベクトル値を整数に変換"""
        try:
            val_str = str(value)
            
            if '#b' in val_str:
                match = re.search(r'#b([01]+)', val_str)
                if match:
                    return int(match.group(1), 2)
            
            if '#x' in val_str:
                match = re.search(r'#x([0-9a-fA-F]+)', val_str)
                if match:
                    return int(match.group(1), 16)
            
            bv_match = re.search(r'\(_\s*bv(\d+)\s+\d+\)', val_str)
            if bv_match:
                return int(bv_match.group(1))
            
            if hasattr(value, 'isBitVectorValue') and value.isBitVectorValue():
                if hasattr(value, 'getBitVectorValue'):
                    try:
                        bv_val = value.getBitVectorValue(10)
                        if isinstance(bv_val, int):
                            return bv_val
                        if isinstance(bv_val, str) and bv_val.isdigit():
                            return int(bv_val)
                    except Exception:
                        pass
                    
                    try:
                        bv_val = value.getBitVectorValue(2)
                        if isinstance(bv_val, str):
                            return int(bv_val, 2)
                    except Exception:
                        pass
            
            if val_str.isdigit():
                return int(val_str)
            
        except Exception:
            pass
        
        return None
    
    def get_model(self) -> Optional[Dict[str, Any]]:
        return self._model
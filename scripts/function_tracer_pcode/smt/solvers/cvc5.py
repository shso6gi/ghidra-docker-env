# -*- coding: utf-8 -*-
"""CVC5ソルバー実装（getDeclaredTerms使用版）"""

from __future__ import annotations

import time
import re
from typing import Optional, Dict, Any, Tuple, TYPE_CHECKING

from scripts.function_tracer_pcode.smt.interface import SMTSolver, SolverResult, SolverStatus

# 型チェック時のみインポート
if TYPE_CHECKING:
    pass


class CVC5Solver(SMTSolver):
    """CVC5 SMTソルバー"""
    
    def __init__(self, timeout: int = 10, debug: bool = False):
        super().__init__(timeout)
        self._cvc5: Optional[Any] = None
        self._solver: Optional[Any] = None
        self._tm: Optional[Any] = None
        self._model: Optional[Dict[str, Any]] = None
        self._declared_consts: Dict[str, Any] = {}
        self.debug = debug
    
    @property
    def name(self) -> str:
        return "CVC5"
    
    def _debug_print(self, msg: str) -> None:
        if self.debug:
            print(f"[CVC5 DEBUG] {msg}")
    
    def check_availability(self) -> Tuple[bool, str]:
        try:
            import cvc5  # type: ignore[import-untyped]
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
        
        try:
            cvc5 = self._cvc5
            if cvc5 is None:
                return self._create_error_result("CVC5 module not loaded")
            
            # type: ignore で警告を抑制
            tm = cvc5.TermManager()  # type: ignore[union-attr]
            solver = cvc5.Solver(tm)  # type: ignore[union-attr]
            self._solver = solver
            self._tm = tm
            
            solver.setOption("produce-models", "true")
            solver.setOption("tlimit", str(self.timeout * 1000))
            solver.setLogic("QF_BV")
            
            if cancellation_token and cancellation_token.is_cancelled():
                return SolverResult(
                    solver_name=self.name,
                    status=SolverStatus.UNKNOWN,
                    elapsed_time=time.time() - start_time,
                    error_message="Cancelled"
                )
            
            self._parse_declarations(smt_script)
            filtered_script = self._filter_script_minimal(smt_script)
            
            self._debug_print(f"Parsing script ({len(filtered_script)} chars)...")
            self._debug_print(f"Known constants: {list(self._declared_consts.keys())}")
            
            sm = None
            try:
                parser = cvc5.InputParser(solver)  # type: ignore[union-attr]
                parser.setStringInput(
                    cvc5.InputLanguage.SMT_LIB_2_6,  # type: ignore[union-attr]
                    filtered_script,
                    "equivalence_check"
                )
                
                sm = parser.getSymbolManager()
                
                cmd_count = 0
                while True:
                    cmd = parser.nextCommand()
                    if cmd.isNull():
                        break
                    cmd_name = cmd.getCommandName() if hasattr(cmd, 'getCommandName') else str(cmd)
                    self._debug_print(f"  Command: {cmd_name}")
                    cmd.invoke(solver, sm)
                    cmd_count += 1
                
                self._debug_print(f"Executed {cmd_count} commands")
                
            except AttributeError as e:
                self._debug_print(f"InputParser not available: {e}")
                return self._create_error_result(f"CVC5 API error: {e}")
            
            self._debug_print("Starting check...")
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
        
        except Exception as e:
            elapsed = time.time() - start_time
            self._debug_print(f"Exception: {e}")
            if self.debug:
                import traceback
                self._debug_print(traceback.format_exc())
            if elapsed >= self.timeout:
                return self._create_timeout_result(elapsed)
            return self._create_error_result(str(e))
    
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
                        # Termの名前を取得
                        term_name = self._get_term_name(term)
                        self._debug_print(f"  Processing term: {term}, name: {term_name}")
                        
                        if term_name is None:
                            continue
                        
                        # 既知の変数のみ処理
                        if term_name not in self._declared_consts:
                            self._debug_print("    Skipping (not in declared_consts)")
                            continue
                        
                        # getValue を呼び出し
                        value = solver.getValue(term)
                        self._debug_print(f"    getValue result: {value}")
                        
                        # 値を整数に変換
                        int_val = self._bv_to_int(value)
                        self._debug_print(f"    Converted to: {int_val}")
                        
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
        
        # フォールバック: アサーションから抽出
        self._debug_print("Fallback: extracting from assertions")
        return self._extract_model_from_assertions(solver)
    
    def _get_term_name(self, term) -> Optional[str]:
        """Termから名前を取得"""
        try:
            # getSymbol を試す
            if hasattr(term, 'getSymbol'):
                sym = term.getSymbol()
                if sym:
                    self._debug_print(f"      getSymbol: {sym}")
                    return sym
            
            # 文字列表現を使用
            term_str = str(term)
            self._debug_print(f"      str(term): {term_str}")
            
            # 単純な識別子の場合
            if term_str.isidentifier():
                return term_str
            
            # param_ パターン
            match = re.match(r'(param_\d+_\d+)', term_str)
            if match:
                return match.group(1)
            
        except Exception as e:
            self._debug_print(f"      Error getting name: {e}")
        
        return None
    
    def _extract_model_from_assertions(self, solver) -> Dict[str, Any]:
        """アサーションから変数を抽出してモデルを取得"""
        result = {}
        
        try:
            assertions = solver.getAssertions()
            self._debug_print(f"  Number of assertions: {len(assertions)}")
            
            free_vars = []
            visited = set()
            for assertion in assertions:
                self._collect_bv_vars(assertion, free_vars, visited)
            
            self._debug_print(f"  Found {len(free_vars)} BV variables")
            
            for var in free_vars:
                try:
                    var_name = self._get_term_name(var)
                    if not var_name or var_name.startswith('return_'):
                        continue
                    
                    if var_name not in self._declared_consts:
                        continue
                    
                    value = solver.getValue(var)
                    self._debug_print(f"  getValue({var_name}): {value}")
                    
                    int_val = self._bv_to_int(value)
                    if int_val is not None:
                        result[var_name] = int_val
                    else:
                        result[var_name] = str(value)
                        
                except Exception as e:
                    self._debug_print(f"  Error: {e}")
        
        except Exception as e:
            self._debug_print(f"  Assertion extraction failed: {e}")
        
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
            self._debug_print(f"      _bv_to_int input: {val_str}")
            
            # #b... (2進数)
            if '#b' in val_str:
                match = re.search(r'#b([01]+)', val_str)
                if match:
                    binary_str = match.group(1)
                    result = int(binary_str, 2)
                    self._debug_print(f"      Parsed binary: {result}")
                    return result
            
            # #x... (16進数)
            if '#x' in val_str:
                match = re.search(r'#x([0-9a-fA-F]+)', val_str)
                if match:
                    return int(match.group(1), 16)
            
            # (_ bvN M) 形式
            bv_match = re.search(r'\(_\s*bv(\d+)\s+\d+\)', val_str)
            if bv_match:
                return int(bv_match.group(1))
            
            # CVC5 API
            if hasattr(value, 'isBitVectorValue') and value.isBitVectorValue():
                if hasattr(value, 'getBitVectorValue'):
                    try:
                        bv_val = value.getBitVectorValue(10)
                        self._debug_print(f"      getBitVectorValue(10): {bv_val}, type: {type(bv_val)}")
                        if isinstance(bv_val, int):
                            return bv_val
                        if isinstance(bv_val, str) and bv_val.isdigit():
                            return int(bv_val)
                    except Exception as e:
                        self._debug_print(f"      getBitVectorValue(10) error: {e}")
                    
                    try:
                        bv_val = value.getBitVectorValue(2)
                        self._debug_print(f"      getBitVectorValue(2): {bv_val}")
                        if isinstance(bv_val, str):
                            return int(bv_val, 2)
                    except Exception as e:
                        self._debug_print(f"      getBitVectorValue(2) error: {e}")
            
            if val_str.isdigit():
                return int(val_str)
            
        except Exception as e:
            self._debug_print(f"      Conversion error: {e}")
        
        return None
    
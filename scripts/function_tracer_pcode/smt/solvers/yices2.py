# -*- coding: utf-8 -*-
"""Yices2ソルバー実装（モデル抽出改善版）"""

import time
import tempfile
import os
import subprocess
import shutil
import re
from typing import Optional, Dict, Any, Tuple

from ..interface import SMTSolver, SolverResult, SolverStatus


class Yices2Solver(SMTSolver):
    """Yices2 SMTソルバー"""
    
    def __init__(self, timeout: int = 180, debug: bool = False):
        super().__init__(timeout)
        self._yices = None
        self._model = None
        self._initialized = False
        self._use_subprocess = False
        self._yices_smt2_path = None
        self.debug = debug
    
    @property
    def name(self) -> str:
        return "Yices2"
    
    def _debug_print(self, msg: str):
        if self.debug:
            print(f"[Yices2 DEBUG] {msg}")
    
    def check_availability(self) -> Tuple[bool, str]:
        # まずPythonバインディングを試す
        python_available, python_msg = self._check_python_binding()
        if python_available:
            return True, python_msg
        
        # Python バインディングがない場合、コマンドラインツールを試す
        cmd_available, cmd_msg = self._check_command_line()
        if cmd_available:
            self._use_subprocess = True
            return True, cmd_msg
        
        return False, f"Python binding: {python_msg}; Command line: {cmd_msg}"
    
    def _check_python_binding(self) -> Tuple[bool, str]:
        """Pythonバインディングの利用可能性をチェック"""
        try:
            from yices import Config, Context, Status, Model, Terms, Yices
            self._yices_module = {
                'Config': Config,
                'Context': Context,
                'Status': Status,
                'Model': Model,
                'Terms': Terms,
                'Yices': Yices
            }
            
            if not self._initialized:
                Yices.init()
                self._initialized = True
            
            version = Yices.version
            
            if self.debug:
                attrs = [a for a in dir(Yices) if not a.startswith('_')]
                self._debug_print(f"Yices attributes: {attrs}")
            
            # Python APIではSMT-LIB2パースが困難なため、サブプロセスにフォールバック
            self._use_subprocess = True
            cmd_available, _ = self._check_command_line()
            if cmd_available:
                return True, f"Python binding version {version} (using subprocess)"
            
            return True, f"Python binding version {version}"
        
        except OSError as e:
            return False, f"Native library error: {e}"
        except ImportError as e:
            return False, f"Import error: {e}"
        except Exception as e:
            return False, f"Error: {e}"
    
    def _check_command_line(self) -> Tuple[bool, str]:
        """コマンドラインツールの利用可能性をチェック"""
        yices_cmd = shutil.which("yices-smt2")
        if yices_cmd:
            self._yices_smt2_path = yices_cmd
            try:
                result = subprocess.run(
                    [yices_cmd, "--version"],
                    capture_output=True,
                    text=True,
                    timeout=5
                )
                version_info = result.stdout.strip() or result.stderr.strip()
                return True, f"Command line: {version_info}"
            except Exception as e:
                return False, f"Command exists but failed: {e}"
        
        return False, "yices-smt2 command not found"
    
    def check_equivalence_direct(
        self,
        smt_script: str,
        cancellation_token: Optional[Any] = None
    ) -> SolverResult:
        if not self.is_available():
            return self._create_error_result("Yices2 is not available")
        
        if self._use_subprocess:
            return self._check_via_subprocess(smt_script, cancellation_token)
        else:
            return self._check_via_python(smt_script, cancellation_token)
    
    def _check_via_subprocess(
        self,
        smt_script: str,
        cancellation_token: Optional[Any] = None
    ) -> SolverResult:
        import sys
        print("[Yices2] _check_via_subprocess START", flush=True)
        sys.stdout.flush()
        """サブプロセス経由でyices-smt2を実行"""
        start_time = time.time()
        
        try:
            with tempfile.NamedTemporaryFile(
                mode='w', 
                suffix='.smt2', 
                delete=False
            ) as f:
                f.write(smt_script)
                temp_path = f.name
            
            if self.debug:
                self._debug_print(f"Temp file: {temp_path}")
            
            try:
                if cancellation_token and cancellation_token.is_cancelled():
                    return SolverResult(
                        solver_name=self.name,
                        status=SolverStatus.UNKNOWN,
                        elapsed_time=time.time() - start_time,
                        error_message="Cancelled"
                    )
                
                result = subprocess.run(
                    [self._yices_smt2_path, temp_path],
                    capture_output=True,
                    text=True,
                    timeout=self.timeout
                )
                
                elapsed = time.time() - start_time
                output = result.stdout.strip()
                stderr = result.stderr.strip()
                
                if self.debug:
                    self._debug_print(f"stdout: {output}")
                    self._debug_print(f"stderr: {stderr}")
                
                # 結果を解析
                if output.lower().startswith("unsat"):
                    return SolverResult(
                        solver_name=self.name,
                        status=SolverStatus.UNSAT,
                        elapsed_time=elapsed,
                        raw_output=output
                    )
                elif output.lower().startswith("sat"):
                    self._model = self._parse_model_from_output(output)
                    self._debug_print(f"Parsed model: {self._model}")
                    return SolverResult(
                        solver_name=self.name,
                        status=SolverStatus.SAT,
                        elapsed_time=elapsed,
                        model=self._model,
                        raw_output=output
                    )
                elif "error" in output.lower() or "error" in stderr.lower():
                    return self._create_error_result(f"Yices error: {stderr or output}")
                else:
                    return SolverResult(
                        solver_name=self.name,
                        status=SolverStatus.UNKNOWN,
                        elapsed_time=elapsed,
                        raw_output=output
                    )
            
            finally:
                os.unlink(temp_path)
        
        except subprocess.TimeoutExpired:
            elapsed = time.time() - start_time
            return self._create_timeout_result(elapsed)
        except Exception as e:
            elapsed = time.time() - start_time
            if self.debug:
                import traceback
                self._debug_print(f"Exception: {e}")
                self._debug_print(traceback.format_exc())
            return self._create_error_result(str(e))
    
    def _check_via_python(
        self,
        smt_script: str,
        cancellation_token: Optional[Any] = None
    ) -> SolverResult:
        """PythonバインディングAPIを使用"""
        # サブプロセスにフォールバック
        self._use_subprocess = True
        cmd_available, _ = self._check_command_line()
        if cmd_available:
            return self._check_via_subprocess(smt_script, cancellation_token)
        
        return self._create_error_result(
            "Yices Python API does not support SMT-LIB2 parsing and yices-smt2 command not found"
        )
    
    def _parse_model_from_output(self, output: str) -> Dict[str, Any]:
        """
        Yices2の出力からモデルを解析
        
        出力形式の例:
        sat
        ((define-fun param_1_1 () (_ BitVec 32) #b00000000000000000000000000000000)
         (define-fun param_2_1 () (_ BitVec 32) #b10000000000000000000000000000000)
         ...)
        """
        model = {}
        
        # define-fun パターン
        # (define-fun NAME () TYPE VALUE)
        pattern = r'\(define-fun\s+(\w+)\s*\(\)\s*\([^)]+\)\s*([^)]+)\)'
        
        matches = re.findall(pattern, output)
        
        for name, value in matches:
            value = value.strip()
            int_value = self._parse_bitvector_value(value)
            
            if int_value is not None:
                model[name] = int_value
            else:
                model[name] = value
            
            if self.debug:
                self._debug_print(f"  Parsed: {name} = {value} -> {model[name]}")
        
        return model
    
    def _parse_bitvector_value(self, value: str) -> Optional[int]:
        """ビットベクトル値を整数に変換"""
        value = value.strip()
        
        # #b... (2進数)
        if value.startswith('#b'):
            try:
                return int(value[2:], 2)
            except ValueError:
                pass
        
        # #x... (16進数)
        elif value.startswith('#x'):
            try:
                return int(value[2:], 16)
            except ValueError:
                pass
        
        # (_ bvN M) 形式
        bv_match = re.match(r'\(_\s*bv(\d+)\s+\d+\)', value)
        if bv_match:
            try:
                return int(bv_match.group(1))
            except ValueError:
                pass
        
        # 純粋な数値
        if value.isdigit():
            return int(value)
        
        return None
    
    def get_model(self) -> Optional[Dict[str, Any]]:
        return self._model
    
    def __del__(self):
        """クリーンアップ"""
        if self._initialized:
            try:
                self._yices_module['Yices'].exit()
            except:
                pass
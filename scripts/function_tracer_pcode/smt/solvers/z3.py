# -*- coding: utf-8 -*-
"""Z3ソルバー実装（タイムアウト検出修正版）"""

import time
import importlib
import re
from typing import Optional, Dict, Any, Tuple, Callable, cast

from ..interface import SMTSolver, SolverResult, SolverStatus


_DECLARATION_RE = re.compile(
    r"^\(declare-(?:const\s+([^\s()]+)|fun\s+([^\s()]+)\s+\(\))\s+(.+)\)$",
    re.DOTALL,
)


def _top_level_smt_commands(smt_script: str) -> tuple[str, ...]:
    """Split SMT-LIB into top-level commands without parsing rendered terms."""

    commands = []
    start = None
    depth = 0
    in_string = False
    in_quoted_symbol = False
    in_comment = False
    escaped = False
    for index, char in enumerate(smt_script):
        if in_comment:
            if char == "\n":
                in_comment = False
            continue
        if in_string:
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                in_string = False
            continue
        if in_quoted_symbol:
            if char == "|":
                in_quoted_symbol = False
            continue
        if char == ";":
            in_comment = True
        elif char == '"':
            in_string = True
        elif char == "|":
            in_quoted_symbol = True
        elif char == "(":
            if depth == 0:
                start = index
            depth += 1
        elif char == ")":
            depth -= 1
            if depth < 0:
                raise ValueError("SMT-LIB command parentheses are unbalanced")
            if depth == 0 and start is not None:
                commands.append(smt_script[start:index + 1])
                start = None
    if depth or in_string or in_quoted_symbol:
        raise ValueError("SMT-LIB command surface is incomplete")
    return tuple(commands)


def _existing_model_projection(model: Any) -> Dict[str, Any]:
    result: Dict[str, Any] = {}
    for declaration in model.decls():
        value = model[declaration]
        as_long = getattr(value, "as_long", None)
        as_signed_long = getattr(value, "as_signed_long", None)
        try:
            if callable(as_long):
                projected = as_long()
            elif callable(as_signed_long):
                projected = as_signed_long()
            else:
                projected = str(value)
        except (AttributeError, TypeError, ValueError):
            projected = str(value)
        result[str(declaration.name())] = projected
    return result


def extract_total_declared_model(
    z3: Any, model: Any, smt_script: str,
) -> Dict[str, Any]:
    """Materialize every supported declared input using Z3 model completion."""

    result = _existing_model_projection(model)
    model_context = getattr(model, "ctx", None)
    declared_names = set()
    for command in _top_level_smt_commands(smt_script):
        match = _DECLARATION_RE.fullmatch(command.strip())
        if match is None:
            continue
        name = match.group(1) or match.group(2)
        sort_text = match.group(3).strip()
        if name in declared_names:
            raise ValueError(f"duplicate SMT declaration: {name}")
        declared_names.add(name)
        sort_text = sort_text.strip()
        if sort_text == "Bool":
            symbol = z3.Bool(name, ctx=model_context)
        elif sort_text == "Int":
            symbol = z3.Int(name, ctx=model_context)
        else:
            bitvec = re.fullmatch(r"\(_ BitVec ([1-9][0-9]*)\)", sort_text)
            if bitvec is None:
                # Arrays, reals, floating-point values and other supported Z3
                # sorts retain Z3's existing model projection.  They are not
                # scalar replay inputs and must never turn SAT into ERROR.
                continue
            symbol = z3.BitVec(
                name, int(bitvec.group(1)), ctx=model_context
            )
        value = model.eval(symbol, model_completion=True)
        if sort_text == "Bool":
            if z3.is_true(value):
                result[name] = True
            elif z3.is_false(value):
                result[name] = False
            else:
                raise ValueError(f"completed Bool model value is not concrete: {name}")
        else:
            result[name] = value.as_long()
    return result


class Z3Solver(SMTSolver):
    """Z3 SMTソルバー"""
    
    def __init__(self, timeout: int = 10, debug: bool = False):
        super().__init__(timeout)
        self._z3 = None
        self._solver = None
        self._model = None
        self.debug = debug
    
    @property
    def name(self) -> str:
        return "Z3"
    
    def set_timeout(self, timeout: int) -> None:
        """タイムアウトを動的に設定"""
        self.timeout = timeout
        self._debug_print(f"Timeout updated to {timeout}s")
        # 既存のソルバーインスタンスがあればそちらも更新
        if self._solver is not None:
            self._solver.set("timeout", timeout * 1000)
            self._debug_print(f"Z3 solver timeout set to {timeout * 1000}ms")
    
    def _debug_print(self, msg: str):
        if self.debug:
            print(f"[Z3 DEBUG] {msg}")
    
    def check_availability(self) -> Tuple[bool, str]:
        try:
            z3_module = cast(Any, importlib.import_module("z3"))
            self._z3 = z3_module
            version = z3_module.get_version_string()
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
        self._debug_print(f"Current timeout: {self.timeout}s")
        
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
            self._debug_print(f"Z3 timeout set to {self.timeout * 1000}ms")
            
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
                model_dict = extract_total_declared_model(
                    z3, self._model, smt_script
                )
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
                # unknown の理由を取得してタイムアウトかどうかを判定
                reason = str(self._solver.reason_unknown())
                self._debug_print(f"Reason for unknown: {reason}")
                
                is_timeout = self._is_timeout_reason(reason, elapsed)
                
                if is_timeout:
                    self._debug_print("Detected as TIMEOUT")
                    return SolverResult(
                        solver_name=self.name,
                        status=SolverStatus.TIMEOUT,
                        elapsed_time=elapsed,
                        error_message=f"Timeout: {reason}"
                    )
                else:
                    return SolverResult(
                        solver_name=self.name,
                        status=SolverStatus.UNKNOWN,
                        elapsed_time=elapsed,
                        error_message=reason
                    )
        
        except Exception as e:
            elapsed = time.time() - start_time
            self._debug_print(f"Exception: {e}")
            if elapsed >= self.timeout:
                return self._create_timeout_result(elapsed)
            return self._create_error_result(str(e))
    
    def _is_timeout_reason(self, reason: str, elapsed: float) -> bool:
        """
        Z3のunknown理由がタイムアウトかどうかを判定
        
        Args:
            reason: Z3のreason_unknown()の結果
            elapsed: 経過時間（秒）
        
        Returns:
            タイムアウトならTrue
        """
        if reason == "timeout":
            return True
        
        # 経過時間がタイムアウトの90%以上ならタイムアウトとみなす
        if elapsed >= self.timeout * 0.9:
            self._debug_print(f"Elapsed time ({elapsed:.3f}s) >= 90% of timeout ({self.timeout}s)")
            return True
        
        return False
    
    def _extract_model(self) -> Dict[str, Any]:
        """Z3モデルから辞書を抽出"""
        if self._model is None:
            return {}
        
        result = {}
        for decl in self._model.decls():
            name = decl.name()
            value = self._model[decl]
            
            self._debug_print(f"  Model var: {name} = {value} (type: {type(value).__name__})")
            
            # ビットベクトルを整数に変換
            as_long: Optional[Callable[[], int]] = getattr(value, 'as_long', None)
            as_signed_long: Optional[Callable[[], int]] = getattr(value, 'as_signed_long', None)
            
            if as_long is not None:
                result[name] = as_long()
            elif as_signed_long is not None:
                result[name] = as_signed_long()
            else:
                result[name] = str(value)
        
        return result
    
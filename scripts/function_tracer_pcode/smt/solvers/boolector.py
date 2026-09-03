# -*- coding: utf-8 -*-
# pyright: reportMissingImports=false
# pyright: reportOptionalMemberAccess=false
"""Boolectorソルバー実装（API互換性対応版）"""

import time
import tempfile
import os
from typing import Optional, Dict, Any, Tuple

from scripts.function_tracer_pcode.smt.interface import SMTSolver, SolverResult, SolverStatus


class BoolectorSolver(SMTSolver):
    """Boolector SMTソルバー"""
    
    def __init__(self, timeout: int = 180, debug: bool = False):
        super().__init__(timeout)
        self._boolector: Optional[Any] = None
        self._btor: Optional[Any] = None
        self._model: Optional[Dict[str, Any]] = None
        self._api_info: Dict[str, Any] = {}  # API情報を格納
        self.debug = debug
    
    @property
    def name(self) -> str:
        return "Boolector"
    
    def _debug_print(self, msg: str) -> None:
        if self.debug:
            print(f"[Boolector DEBUG] {msg}")
    
    def check_availability(self) -> Tuple[bool, str]:
        # 最初にboolectorを試す
        try:
            import boolector  # type: ignore[import-not-found, import-untyped]
            self._boolector = boolector
            self._detect_api(boolector)
            return True, f"boolector package available (API: {self._api_info.get('type', 'unknown')})"
        except ImportError:
            pass
        
        # 次にpyboolectorを試す
        try:
            import pyboolector  # type: ignore[import-not-found, import-untyped]
            self._boolector = pyboolector
            self._detect_api(pyboolector)
            return True, f"pyboolector package available (API: {self._api_info.get('type', 'unknown')})"
        except ImportError:
            pass
        
        return False, "Neither boolector nor pyboolector is installed"
    
    def _detect_api(self, module: Any) -> None:
        """
        BoolectorのAPIバージョンを検出し、利用可能な機能を確認
        """
        self._api_info = {
            'type': 'unknown',
            'has_opt_model_gen': False,
            'has_opt_incremental': False,
            'result_sat': None,
            'result_unsat': None,
            'result_unknown': None,
        }
        
        # 利用可能な属性を列挙（デバッグ用）
        if self.debug:
            attrs = [a for a in dir(module) if not a.startswith('_')]
            self._debug_print(f"Available module attributes: {attrs[:30]}...")  # 最初の30個
        
        # オプション定数のチェック
        if hasattr(module, 'BTOR_OPT_MODEL_GEN'):
            self._api_info['has_opt_model_gen'] = True
            self._api_info['opt_model_gen'] = module.BTOR_OPT_MODEL_GEN
        
        if hasattr(module, 'BTOR_OPT_INCREMENTAL'):
            self._api_info['has_opt_incremental'] = True
            self._api_info['opt_incremental'] = module.BTOR_OPT_INCREMENTAL
        
        # 結果定数のチェック
        if hasattr(module, 'BTOR_RESULT_SAT'):
            self._api_info['result_sat'] = module.BTOR_RESULT_SAT
            self._api_info['result_unsat'] = module.BTOR_RESULT_UNSAT
            self._api_info['result_unknown'] = getattr(module, 'BTOR_RESULT_UNKNOWN', None)
            self._api_info['type'] = 'classic'
        elif hasattr(module, 'SAT'):
            # 新しいAPI
            self._api_info['result_sat'] = module.SAT
            self._api_info['result_unsat'] = module.UNSAT
            self._api_info['result_unknown'] = getattr(module, 'UNKNOWN', None)
            self._api_info['type'] = 'new'
        
        # Boolectorクラスのメソッドをチェック
        if hasattr(module, 'Boolector'):
            btor_class = module.Boolector
            if self.debug:
                methods = [m for m in dir(btor_class) if not m.startswith('_')]
                self._debug_print(f"Boolector class methods: {methods[:30]}...")
            
            # Set_opt vs set_opt
            self._api_info['set_opt_method'] = 'Set_opt' if hasattr(btor_class, 'Set_opt') else 'set_opt'
            # Parse vs parse
            self._api_info['parse_method'] = 'Parse' if hasattr(btor_class, 'Parse') else 'parse'
            # Sat vs sat
            self._api_info['sat_method'] = 'Sat' if hasattr(btor_class, 'Sat') else 'sat'
        
        if self.debug:
            self._debug_print(f"API info: {self._api_info}")
    
    def check_equivalence_direct(
        self,
        smt_script: str,
        cancellation_token: Optional[Any] = None
    ) -> SolverResult:
        if not self.is_available():
            return self._create_error_result("Boolector is not available")
        
        start_time = time.time()
        
        try:
            if self._boolector is None:
                return self._create_error_result("Boolector module not loaded")
            
            # 新しいBoolectorインスタンスを作成
            btor = self._boolector.Boolector()
            self._btor = btor
            
            # オプション設定（API互換性を考慮）
            self._set_options(btor)
            
            # 一時ファイルに書き込み
            with tempfile.NamedTemporaryFile(
                mode='w', 
                suffix='.smt2', 
                delete=False
            ) as f:
                # (check-sat) と (get-model) を除去
                filtered_script = self._filter_script(smt_script)
                f.write(filtered_script)
                temp_path = f.name
            
            if self.debug:
                self._debug_print(f"Temp file: {temp_path}")
                self._debug_print(f"Script length: {len(filtered_script)} chars")
            
            try:
                if cancellation_token and cancellation_token.is_cancelled():
                    return SolverResult(
                        solver_name=self.name,
                        status=SolverStatus.UNKNOWN,
                        elapsed_time=time.time() - start_time,
                        error_message="Cancelled"
                    )
                
                # SMT-LIB2ファイルをパース
                parse_result = self._parse_file(btor, temp_path)
                if parse_result is not None:
                    return parse_result
                
                # SAT チェック
                result = self._call_sat(btor)
                elapsed = time.time() - start_time
                
                if self.debug:
                    self._debug_print(f"SAT result: {result}")
                
                # 結果を判定
                return self._interpret_result(result, btor, elapsed)
            
            finally:
                os.unlink(temp_path)
        
        except Exception as e:
            elapsed = time.time() - start_time
            error_msg = str(e)
            if self.debug:
                import traceback
                self._debug_print(f"Exception: {error_msg}")
                self._debug_print(traceback.format_exc())
            
            if elapsed >= self.timeout:
                return self._create_timeout_result(elapsed)
            return self._create_error_result(error_msg)
    
    def _set_options(self, btor: Any) -> None:
        """オプションを設定（API互換性を考慮）"""
        try:
            set_opt = getattr(btor, self._api_info.get('set_opt_method', 'Set_opt'), None)
            
            if set_opt is None:
                # メソッドが見つからない場合、代替手段を試す
                if hasattr(btor, 'Set_opt'):
                    set_opt = btor.Set_opt
                elif hasattr(btor, 'set_opt'):
                    set_opt = btor.set_opt
                else:
                    self._debug_print("Warning: No set_opt method found")
                    return
            
            # モデル生成を有効化
            if self._api_info.get('has_opt_model_gen'):
                set_opt(self._api_info['opt_model_gen'], 1)
            else:
                # 文字列ベースのオプション設定を試す
                try:
                    if hasattr(btor, 'Set_opt') or hasattr(btor, 'set_opt'):
                        # 数値の代わりに文字列を試す（一部のバージョン）
                        pass  # 何もしない - モデル生成なしでも動作可能
                except Exception:
                    pass
            
            # インクリメンタルモードを有効化
            if self._api_info.get('has_opt_incremental'):
                set_opt(self._api_info['opt_incremental'], 1)
        
        except Exception as e:
            self._debug_print(f"Warning: Failed to set options: {e}")
    
    def _parse_file(self, btor: Any, filepath: str) -> Optional[SolverResult]:
        """ファイルをパース"""
        try:
            parse_method = getattr(btor, self._api_info.get('parse_method', 'Parse'), None)
            
            if parse_method is None:
                if hasattr(btor, 'Parse'):
                    parse_method = btor.Parse
                elif hasattr(btor, 'parse'):
                    parse_method = btor.parse
                else:
                    return self._create_error_result("No parse method found")
            
            parse_res = parse_method(filepath)
            
            # パース結果の確認（APIバージョンにより異なる）
            if isinstance(parse_res, tuple):
                if len(parse_res) >= 1 and parse_res[0] != 0:
                    error_msg = parse_res[2] if len(parse_res) > 2 else 'Parse error'
                    return self._create_error_result(f"Parse error: {error_msg}")
            elif isinstance(parse_res, int) and parse_res != 0:
                return self._create_error_result("Parse error")
            
            return None  # パース成功
        
        except Exception as e:
            return self._create_error_result(f"Parse exception: {e}")
    
    def _call_sat(self, btor: Any) -> Any:
        """SATチェックを呼び出す"""
        sat_method = getattr(btor, self._api_info.get('sat_method', 'Sat'), None)
        
        if sat_method is None:
            if hasattr(btor, 'Sat'):
                sat_method = btor.Sat
            elif hasattr(btor, 'sat'):
                sat_method = btor.sat
            else:
                raise RuntimeError("No sat method found")
        
        return sat_method()
    
    def _interpret_result(self, result: Any, btor: Any, elapsed: float) -> SolverResult:
        """結果を解釈"""
        result_sat = self._api_info.get('result_sat')
        result_unsat = self._api_info.get('result_unsat')
        
        if result_sat is not None and result == result_sat:
            self._model = self._extract_model(btor)
            return SolverResult(
                solver_name=self.name,
                status=SolverStatus.SAT,
                elapsed_time=elapsed,
                model=self._model
            )
        elif result_unsat is not None and result == result_unsat:
            return SolverResult(
                solver_name=self.name,
                status=SolverStatus.UNSAT,
                elapsed_time=elapsed
            )
        else:
            # 定数が不明な場合、結果値で判断を試みる
            if isinstance(result, int):
                if result == 10:  # 一般的にSAT
                    self._model = self._extract_model(btor)
                    return SolverResult(
                        solver_name=self.name,
                        status=SolverStatus.SAT,
                        elapsed_time=elapsed,
                        model=self._model
                    )
                elif result == 20:  # 一般的にUNSAT
                    return SolverResult(
                        solver_name=self.name,
                        status=SolverStatus.UNSAT,
                        elapsed_time=elapsed
                    )
            
            return SolverResult(
                solver_name=self.name,
                status=SolverStatus.UNKNOWN,
                elapsed_time=elapsed,
                error_message=f"Unknown result: {result}"
            )
    
    def _filter_script(self, smt_script: str) -> str:
        """check-sat, get-model, exit を除去"""
        lines = smt_script.split('\n')
        filtered = []
        for line in lines:
            stripped = line.strip()
            if stripped.startswith('(check-sat'):
                continue
            if stripped.startswith('(get-model'):
                continue
            if stripped.startswith('(exit'):
                continue
            filtered.append(line)
        return '\n'.join(filtered)
    
    def _extract_model(self, btor: Any) -> Dict[str, Any]:
        """モデルを抽出"""
        result: Dict[str, Any] = {}
        # Boolector のモデル取得は複雑なため、基本的な実装のみ
        return result
    
# -*- coding: utf-8 -*-
"""SMTソルバー並列実行管理"""

import concurrent.futures
import threading
import inspect
from typing import List, Optional, Dict, Any, Type
from dataclasses import dataclass

from .interface import SMTSolver, SolverResult, SolverStatus
from .solvers.z3 import Z3Solver
from .solvers.boolector import BoolectorSolver
from .solvers.yices2 import Yices2Solver
from .solvers.cvc5 import CVC5Solver


@dataclass
class ParallelResult:
    """並列実行の結果"""
    results: List[SolverResult]
    first_definitive: Optional[SolverResult] = None  # 最初に確定した結果
    is_equivalent: Optional[bool] = None
    
    def get_successful_results(self) -> List[SolverResult]:
        """成功した結果のみ返す"""
        return [r for r in self.results 
                if r.status in (SolverStatus.SAT, SolverStatus.UNSAT)]
    
    def get_counterexample(self) -> Optional[Dict[str, Any]]:
        """反例を取得（最初のSAT結果から）"""
        for r in self.results:
            if r.status == SolverStatus.SAT and r.model:
                return r.model
        return None
    
    def to_dict(self) -> Dict[str, Any]:
        return {
            "is_equivalent": self.is_equivalent,
            "first_definitive": self.first_definitive.to_dict() if self.first_definitive else None,
            "all_results": [r.to_dict() for r in self.results],
        }


class CancellationToken:
    """キャンセルトークン（スレッド間で共有）"""
    
    def __init__(self):
        self._cancelled = threading.Event()
    
    def cancel(self) -> None:
        """キャンセルを要求"""
        self._cancelled.set()
    
    def is_cancelled(self) -> bool:
        """キャンセルされているか確認"""
        return self._cancelled.is_set()


class ParallelSolverRunner:
    """複数のSMTソルバーを並列実行（早期終了対応）"""
    
    # デフォルトで使用するソルバークラス
    DEFAULT_SOLVERS: List[Type[SMTSolver]] = [
        Z3Solver,
        # BoolectorSolver,
        # Yices2Solver,
        # CVC5Solver,
    ]
    
    def __init__(
        self,
        timeout: int = 10,
        solver_classes: Optional[List[Type[SMTSolver]]] = None,
        debug: bool = False
    ):
        """
        Args:
            timeout: 各ソルバーのタイムアウト（秒）
            solver_classes: 使用するソルバークラスのリスト
            debug: デバッグモード
        """
        self.timeout = timeout
        self.solver_classes = solver_classes or self.DEFAULT_SOLVERS
        self.debug = debug
        self._solvers: List[SMTSolver] = []
        self._initialize_solvers()
    
    def _initialize_solvers(self) -> None:
        """利用可能なソルバーを初期化"""
        self._solvers = []
        for solver_cls in self.solver_classes:
            try:
                # ソルバーにdebugフラグを渡す（対応している場合）
                solver = self._create_solver(solver_cls)
                available, message = solver.check_availability()
                if available:
                    self._solvers.append(solver)
                    if self.debug:
                        print(f"[ParallelRunner] {solver.name}: available - {message}")
                else:
                    if self.debug:
                        print(f"[ParallelRunner] {solver.name}: not available - {message}")
            except Exception as e:
                if self.debug:
                    print(f"[ParallelRunner] Failed to initialize {solver_cls.__name__}: {e}")
    
    def _create_solver(self, solver_cls: Type[SMTSolver]) -> SMTSolver:
        """ソルバーインスタンスを作成（debugフラグを渡す）"""
        # コンストラクタのシグネチャをチェック
        sig = inspect.signature(solver_cls.__init__)
        params = sig.parameters
        
        # debugパラメータがあるかチェック
        if 'debug' in params:
            # 型チェッカーを満足させるため、明示的にキャストまたはignore
            return solver_cls(timeout=self.timeout, debug=self.debug)  # type: ignore[call-arg]
        else:
            return solver_cls(timeout=self.timeout)
    
    def get_available_solvers(self) -> List[str]:
        """利用可能なソルバー名のリストを返す"""
        return [s.name for s in self._solvers]
    
    def run_single(
        self, 
        solver: SMTSolver, 
        smt_script: str,
        cancellation_token: Optional[CancellationToken] = None
    ) -> SolverResult:
        """単一ソルバーで実行"""
        import sys
        
        # タイムアウトを動的に設定（重要：ここで反映される）
        solver.set_timeout(self.timeout)
        
        # 即座にフラッシュして出力
        if self.debug:
            print(f"[ParallelRunner] >>> Starting {solver.name} (timeout={self.timeout}s)...", flush=True)
            sys.stdout.flush()
        
        try:
            result = solver.check_equivalence_direct(smt_script, cancellation_token)
            
            if self.debug:
                print(f"[ParallelRunner] <<< {solver.name} completed: {result.status.name}", flush=True)
            
            return result
        except Exception as e:
            if self.debug:
                import traceback
                print(f"[ParallelRunner] {solver.name} exception: {e}", flush=True)
                print(traceback.format_exc(), flush=True)
            return SolverResult(
                solver_name=solver.name,
                status=SolverStatus.ERROR,
                error_message=str(e)
            )
    
    def run_parallel(self, smt_script: str) -> ParallelResult:
        """
        複数ソルバーを並列実行し、最初に確定した結果で終了
        
        Args:
            smt_script: SMT-LIBスクリプト
        
        Returns:
            ParallelResult: 並列実行の結果
        """
        if not self._solvers:
            return ParallelResult(
                results=[],
                is_equivalent=None
            )
        
        if self.debug:
            print(f"[ParallelRunner] Starting parallel execution with {len(self._solvers)} solvers")
        
        results: List[SolverResult] = []
        first_definitive: Optional[SolverResult] = None
        cancellation_token = CancellationToken()
        
        with concurrent.futures.ThreadPoolExecutor(
            max_workers=len(self._solvers)
        ) as executor:
            # 全ソルバーを並列起動
            future_to_solver: Dict[concurrent.futures.Future[SolverResult], SMTSolver] = {
                executor.submit(
                    self.run_single, 
                    solver, 
                    smt_script,
                    cancellation_token
                ): solver
                for solver in self._solvers
            }
            
            try:
                # 結果を収集（完了順）
                for future in concurrent.futures.as_completed(
                    future_to_solver, 
                    timeout=self.timeout + 10
                ):
                    solver = future_to_solver[future]
                    
                    try:
                        result = future.result(timeout=1)
                        results.append(result)
                        
                        if self.debug:
                            status_msg = result.status.name
                            if result.error_message:
                                status_msg += f" ({result.error_message})"
                            print(f"[ParallelRunner] {solver.name} completed: {status_msg} ({result.elapsed_time:.3f}s)")
                        
                        # 確定的な結果が出たら
                        if result.status in (SolverStatus.SAT, SolverStatus.UNSAT):
                            if first_definitive is None:
                                first_definitive = result
                                # 他のソルバーをキャンセル
                                cancellation_token.cancel()
                                if self.debug:
                                    print(f"[ParallelRunner] First definitive result from {solver.name}, cancelling others")
                                # 残りのfutureをキャンセル
                                for f in future_to_solver:
                                    if not f.done():
                                        f.cancel()
                                break  # ループを抜ける
                    
                    except concurrent.futures.TimeoutError:
                        if self.debug:
                            print(f"[ParallelRunner] {solver.name}: future timeout")
                        results.append(SolverResult(
                            solver_name=solver.name,
                            status=SolverStatus.TIMEOUT,
                            elapsed_time=self.timeout
                        ))
                    except concurrent.futures.CancelledError:
                        if self.debug:
                            print(f"[ParallelRunner] {solver.name}: cancelled")
                        results.append(SolverResult(
                            solver_name=solver.name,
                            status=SolverStatus.UNKNOWN,
                            error_message="Cancelled"
                        ))
                    except Exception as e:
                        if self.debug:
                            print(f"[ParallelRunner] {solver.name}: exception - {e}")
                        results.append(SolverResult(
                            solver_name=solver.name,
                            status=SolverStatus.ERROR,
                            error_message=str(e)
                        ))
            
            except concurrent.futures.TimeoutError:
                # 全体タイムアウト
                if self.debug:
                    print("[ParallelRunner] Overall timeout reached")
                cancellation_token.cancel()
                for future, solver in future_to_solver.items():
                    if not future.done():
                        results.append(SolverResult(
                            solver_name=solver.name,
                            status=SolverStatus.TIMEOUT,
                            elapsed_time=self.timeout
                        ))
        
        # 等価性を判定
        is_equivalent: Optional[bool] = None
        if first_definitive:
            is_equivalent = first_definitive.status == SolverStatus.UNSAT
        
        if self.debug:
            print(f"[ParallelRunner] Final result: is_equivalent={is_equivalent}")
        
        return ParallelResult(
            results=results,
            first_definitive=first_definitive,
            is_equivalent=is_equivalent
        )
    
    def run_sequential(self, smt_script: str) -> ParallelResult:
        """
        複数ソルバーを順次実行（デバッグ用）
        最初に確定結果が出たら終了
        """
        if self.debug:
            print(f"[ParallelRunner] Starting sequential execution with {len(self._solvers)} solvers")
        
        results: List[SolverResult] = []
        first_definitive: Optional[SolverResult] = None
        
        for solver in self._solvers:
            if first_definitive is not None:
                break
            
            if self.debug:
                print(f"[ParallelRunner] Running {solver.name}...")
            
            result = self.run_single(solver, smt_script)
            results.append(result)
            
            if self.debug:
                print(f"[ParallelRunner] {solver.name}: {result.status.name} ({result.elapsed_time:.3f}s)")
            
            if result.status in (SolverStatus.SAT, SolverStatus.UNSAT):
                first_definitive = result
        
        is_equivalent: Optional[bool] = None
        if first_definitive:
            is_equivalent = first_definitive.status == SolverStatus.UNSAT
        
        return ParallelResult(
            results=results,
            first_definitive=first_definitive,
            is_equivalent=is_equivalent
        )
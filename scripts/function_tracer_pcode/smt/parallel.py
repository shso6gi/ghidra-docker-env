# -*- coding: utf-8 -*-
"""SMTソルバー並列実行管理"""

import concurrent.futures
import threading
import time
import inspect
from contextlib import contextmanager
from contextvars import ContextVar
from typing import Any, Dict, Iterable, List, Optional, Type
from dataclasses import dataclass, field

from scripts.function_tracer_pcode.core.stage_journal import (
    journal_counter,
    journal_stage_end,
    journal_stage_start,
)
from scripts.function_tracer_pcode.core.json_encoding import each, materialize
from scripts.function_tracer_pcode.smt.interface import SMTSolver, SolverResult, SolverStatus
from scripts.function_tracer_pcode.smt.solvers.z3 import Z3Solver

# --------------------------------------------------------------------------
# Issue #124: solver counter（4 種類を混同しない）
#
#   logical_queries  論理的な問い合わせ回数。run_parallel / run_sequential の
#                    入口で 1 回、orchestration の外から直接呼ばれた run_single
#                    でも 1 回。
#   backend_runs     backend 実行回数。run_single の入口で必ず 1 回。
#   backend_seconds  backend 実行時間の合計。並列実行では実時間より大きくなる。
#   wall_seconds     orchestration と待ちを含む実時間。run_parallel /
#                    run_sequential の出口と、直接呼ばれた run_single の出口。
#                    入れ子の run_single では加算しない（二重計上しない）。
#
# worker thread は空 context で始まるので、`ContextVar` は worker へ伝わらない。
# そのため run_parallel は submit 時に `_orchestrated=True` を明示引数で渡す。
# 複数の ParallelSolverRunner（execution_authority は query ごとに 1 個作る）が
# 同じプロセスで動くので、counter は runner instance ではなく module に持つ。
# --------------------------------------------------------------------------

_IN_SOLVER_ORCHESTRATION: ContextVar[bool] = ContextVar(
    "in_solver_orchestration", default=False
)


class _SolverCounters:
    """4 counter を thread-safe に数える（診断専用、fail-open）。"""

    __slots__ = ("_lock", "logical_queries", "backend_runs", "backend_seconds", "wall_seconds")

    def __init__(self) -> None:
        self._lock = threading.Lock()
        self.logical_queries = 0
        self.backend_runs = 0
        self.backend_seconds = 0.0
        self.wall_seconds = 0.0

    def record_logical_query(self) -> int:
        """1 件数えて、その通し番号を返す（journal の対応 ID に使う）。"""
        with self._lock:
            self.logical_queries += 1
            return self.logical_queries

    def record_backend_run(self) -> int:
        """1 件数えて、その通し番号を返す（journal の対応 ID に使う）。"""
        with self._lock:
            self.backend_runs += 1
            return self.backend_runs

    def add_backend_seconds(self, seconds: float) -> None:
        with self._lock:
            self.backend_seconds += max(0.0, float(seconds))

    def add_wall_seconds(self, seconds: float) -> None:
        with self._lock:
            self.wall_seconds += max(0.0, float(seconds))

    def snapshot(self) -> Dict[str, Any]:
        with self._lock:
            return {
                "logical_queries": self.logical_queries,
                "backend_runs": self.backend_runs,
                "backend_seconds": round(self.backend_seconds, 6),
                "wall_seconds": round(self.wall_seconds, 6),
            }

    def reset(self) -> None:
        with self._lock:
            self.logical_queries = 0
            self.backend_runs = 0
            self.backend_seconds = 0.0
            self.wall_seconds = 0.0


_SOLVER_COUNTERS = _SolverCounters()


def solver_counter_snapshot() -> Dict[str, Any]:
    """このプロセスの solver counter を読む（診断専用）。"""
    return _SOLVER_COUNTERS.snapshot()


def reset_solver_counters() -> None:
    """counter を 0 に戻す（test 用。判定には関与しない）。"""
    _SOLVER_COUNTERS.reset()


@contextmanager
def _solver_orchestration(mode: str):
    """1 回の論理的な問い合わせ（並列 / 順次実行）を囲む計測 scope。

    入口で `logical_queries` を 1 回、出口で orchestration と待ちを含む
    `wall_seconds` を加算する。内側の `run_single` は backend counter だけを
    動かす（`logical_queries` / `wall_seconds` を二重計上しない）。

    Issue #124 PR-124-B: 同じ区間を journal にも出す。counter の値と意味は
    変えず、`logical_queries` の通し番号をそのまま `query_id` として使う
    （backend 側の `counter` 行がこの ID で対応づく）。
    """
    query_id = _SOLVER_COUNTERS.record_logical_query()
    started = time.perf_counter()
    token = _IN_SOLVER_ORCHESTRATION.set(True)
    journal_stage_start("solver", {"kind": mode, "query_id": query_id})
    try:
        yield query_id
    finally:
        try:
            _IN_SOLVER_ORCHESTRATION.reset(token)
        except ValueError:
            _IN_SOLVER_ORCHESTRATION.set(False)
        elapsed = time.perf_counter() - started
        _SOLVER_COUNTERS.add_wall_seconds(elapsed)
        journal_stage_end("solver", elapsed, {"kind": mode, "query_id": query_id})


@dataclass
class ParallelResult:
    """並列実行の結果"""
    results: List[SolverResult]
    first_definitive: Optional[SolverResult] = None  # 最初に確定した結果
    is_equivalent: Optional[bool] = None
    #: TIMEOUT の行があるか（作ったときに 1 度だけ数える事実。`EquivalenceResult.is_timeout` が
    #: 行を辿り直さずに読む。結果 JSON の schema・比較には入れない）。作った後に `results` へ行を
    #: 足さない（足すなら新しい `ParallelResult` を作る: この事実が行と食い違う）
    timed_out: bool = field(default=False, init=False, compare=False, repr=False)

    def __post_init__(self) -> None:
        """手動構築時も SAT/UNSAT から代表結果を補完する。"""
        self.timed_out = any(result.status == SolverStatus.TIMEOUT for result in self.results)
        if self.first_definitive is None:
            for result in self.results:
                if result.status in (SolverStatus.SAT, SolverStatus.UNSAT):
                    self.first_definitive = result
                    break

        if self.is_equivalent is None and self.first_definitive is not None:
            self.is_equivalent = self.first_definitive.status == SolverStatus.UNSAT
    
    def get_counterexample(self) -> Optional[Dict[str, Any]]:
        """反例を取得（最初のSAT結果から）"""
        for r in self.results:
            if r.status == SolverStatus.SAT and r.model:
                return r.model
        return None
    
    def json_items(self):
        """結果 JSON での表現（**唯一の schema**）。solver 行は 1 件ずつ辿る。"""

        yield "is_equivalent", self.is_equivalent
        yield "first_definitive", self.first_definitive
        yield "all_results", each(self.results)

    def to_dict(self) -> Dict[str, Any]:
        return materialize(self)


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


def _with_witness_contract(solver: SMTSolver, result: SolverResult) -> SolverResult:
    """SAT の model を `SolverResult.model` の契約に合わせる（Issue #161）。

    canonical な witness を作れない backend の model は solver の任意の選択なので採らない
    （model 無しの SAT。replay はそれを反例として受け入れない）。
    """

    if (
        result.status == SolverStatus.SAT
        and result.model is not None
        and not getattr(solver, "PROVIDES_CANONICAL_WITNESS", False)
    ):
        return SolverResult(
            solver_name=result.solver_name,
            status=result.status,
            elapsed_time=result.elapsed_time,
            model=None,
            error_message=(
                "canonical witness unavailable: backend does not provide one"
            ),
            raw_output=result.raw_output,
        )
    return result


def _decides_race(result: SolverResult, pending: Iterable[SMTSolver]) -> bool:
    """並列実行で `result` が確定結果として他を打ち切ってよいか（Issue #161）。

    UNSAT と witness 付きの SAT は確定。witness の無い SAT は、canonical な witness を
    作れる backend がまだ走っている間は確定にしない（どの backend が先に終わったかで
    反例の有無 = 判定が変わらないように）。
    """

    if result.status == SolverStatus.UNSAT:
        return True
    if result.status != SolverStatus.SAT:
        return False
    if result.model is not None:
        return True
    return not any(getattr(solver, "PROVIDES_CANONICAL_WITNESS", False) for solver in pending)


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
        cancellation_token: Optional[CancellationToken] = None,
        timeout: Optional[int] = None,
        *,
        _orchestrated: Optional[bool] = None,
        _journal_query_id: Optional[int] = None,
    ) -> SolverResult:
        """単一ソルバーで実行

        ``_orchestrated`` / ``_journal_query_id`` は計測専用の内部引数。
        run_parallel が worker thread へ submit するとき（ContextVar も
        journal の対応 ID も伝わらない）にだけ明示で渡す。判定には一切
        関与しない。
        """
        import sys

        orchestrated = (
            _IN_SOLVER_ORCHESTRATION.get() if _orchestrated is None else bool(_orchestrated)
        )
        query_id = _journal_query_id
        if not orchestrated:
            query_id = _SOLVER_COUNTERS.record_logical_query()
        backend_run_id = _SOLVER_COUNTERS.record_backend_run()
        # Issue #124 PR-124-B: orchestration の内側は backend counter と対応 ID
        # だけを残す（論理問い合わせの start / end は orchestration 側が持って
        # いるので、ここで start / end を書くと journal 上で二重になる）。
        journal_payload = {
            "kind": "run_single",
            "orchestrated": orchestrated,
            "query_id": query_id,
            "backend_run_id": backend_run_id,
            "solver": getattr(solver, "name", None),
        }
        if not orchestrated:
            journal_stage_start("solver", journal_payload)
        backend_started = time.perf_counter()
        try:
            # タイムアウトを動的に設定（重要：ここで反映される）
            runtime_timeout = self._resolve_timeout(timeout)
            solver.set_timeout(runtime_timeout)

            # 即座にフラッシュして出力
            if self.debug:
                print(f"[ParallelRunner] >>> Starting {solver.name} (timeout={runtime_timeout}s)...", flush=True)
                sys.stdout.flush()

            try:
                result = solver.check_equivalence_direct(smt_script, cancellation_token)

                if self.debug:
                    print(f"[ParallelRunner] <<< {solver.name} completed: {result.status.name}", flush=True)

                return _with_witness_contract(solver, result)
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
        finally:
            elapsed = time.perf_counter() - backend_started
            _SOLVER_COUNTERS.add_backend_seconds(elapsed)
            if not orchestrated:
                _SOLVER_COUNTERS.add_wall_seconds(elapsed)
                journal_stage_end("solver", elapsed, journal_payload)
            else:
                journal_counter("solver", journal_payload, seconds=elapsed)
    
    def run_parallel(
        self,
        smt_script: str,
        timeout: Optional[int] = None,
    ) -> ParallelResult:
        """
        複数ソルバーを並列実行し、最初に確定した結果で終了
        
        Args:
            smt_script: SMT-LIBスクリプト
        
        Returns:
            ParallelResult: 並列実行の結果
        """
        with _solver_orchestration("run_parallel") as query_id:
            if not self._solvers:
                return ParallelResult(
                    results=[],
                    is_equivalent=None
                )
        
            runtime_timeout = self._resolve_timeout(timeout)
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
                        cancellation_token,
                        runtime_timeout,
                        _orchestrated=True,
                        _journal_query_id=query_id,
                    ): solver
                    for solver in self._solvers
                }
            
                try:
                    # 結果を収集（完了順）
                    for future in concurrent.futures.as_completed(
                        future_to_solver, 
                        timeout=runtime_timeout + 10
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
                            pending = [
                                other for other_future, other in future_to_solver.items()
                                if other_future is not future and not other_future.done()
                            ]
                            if _decides_race(result, pending):
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
                                elapsed_time=runtime_timeout
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
                                elapsed_time=runtime_timeout
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
    
    def run_sequential(
        self,
        smt_script: str,
        timeout: Optional[int] = None,
    ) -> ParallelResult:
        """
        複数ソルバーを順次実行（デバッグ用）
        最初に確定結果が出たら終了
        """
        with _solver_orchestration("run_sequential") as query_id:
            runtime_timeout = self._resolve_timeout(timeout)
            if self.debug:
                print(f"[ParallelRunner] Starting sequential execution with {len(self._solvers)} solvers")
        
            results: List[SolverResult] = []
            first_definitive: Optional[SolverResult] = None
        
            for solver in self._solvers:
                if first_definitive is not None:
                    break
            
                if self.debug:
                    print(f"[ParallelRunner] Running {solver.name}...")
            
                result = self.run_single(
                    solver,
                    smt_script,
                    timeout=runtime_timeout,
                    _journal_query_id=query_id,
                )
                results.append(result)
            
                if self.debug:
                    print(f"[ParallelRunner] {solver.name}: {result.status.name} ({result.elapsed_time:.3f}s)")
            
                if result.status in (SolverStatus.SAT, SolverStatus.UNSAT):
                    first_definitive = result

            return ParallelResult(
                results=results,
                first_definitive=first_definitive,
                is_equivalent=(first_definitive.status == SolverStatus.UNSAT)
                if first_definitive is not None
                else None
            )

    def _resolve_timeout(self, timeout: Optional[int]) -> int:
        """実行に使うタイムアウトを決定する。"""
        return timeout if timeout is not None else self.timeout

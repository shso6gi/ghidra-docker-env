# -*- coding: utf-8 -*-
"""SMTソルバー並列実行管理"""

import concurrent.futures
import threading
import time
import inspect
from contextlib import contextmanager
from contextvars import ContextVar
from typing import Any, Dict, List, Optional, Type
from dataclasses import dataclass, field

from scripts.function_tracer_pcode.core.stage_journal import (
    journal_counter,
    journal_stage_end,
    journal_stage_start,
)
from scripts.function_tracer_pcode.core.json_encoding import each, materialize
from scripts.function_tracer_pcode.smt.aggregation import aggregate_backend_results
from scripts.function_tracer_pcode.smt.interface import (
    SMTSolver,
    SolverResult,
    SolverStatus,
    enforce_witness_contract,
)
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
    """1 つの query に対する backend の結果。

    `results` は設定された backend の順に 1 行ずつ（完了順ではない）。`first_definitive`
    は判定の根拠になった 1 行で、`smt.aggregation` の規則（backend の結果の集合だけで
    決まり、SAT と UNSAT が食い違えば判定しない）で決まる。名前は結果 JSON の schema
    のために残している（「最初に終わった結果」ではない）。
    """
    results: List[SolverResult]
    first_definitive: Optional[SolverResult] = None  # 判定の根拠になった結果
    is_equivalent: Optional[bool] = None
    #: TIMEOUT の行があるか（作ったときに 1 度だけ数える事実。`EquivalenceResult.is_timeout` が
    #: 行を辿り直さずに読む。結果 JSON の schema・比較には入れない）。作った後に `results` へ行を
    #: 足さない（足すなら新しい `ParallelResult` を作る: この事実が行と食い違う）
    timed_out: bool = field(default=False, init=False, compare=False, repr=False)
    #: backend の結果が SAT と UNSAT で食い違ったか（そのとき判定しない。診断用、schema 外）
    backend_conflict: bool = field(default=False, init=False, compare=False, repr=False)

    def __post_init__(self) -> None:
        """代表結果を `smt.aggregation` の規則で補完する（手動構築でも同じ規則）。"""
        self.timed_out = any(result.status == SolverStatus.TIMEOUT for result in self.results)
        aggregate = aggregate_backend_results(self.results)
        self.backend_conflict = aggregate.conflict
        if self.first_definitive is None:
            self.first_definitive = aggregate.representative

        if self.is_equivalent is None and self.first_definitive is not None:
            self.is_equivalent = self.first_definitive.status == SolverStatus.UNSAT
    
    def get_counterexample(self) -> Optional[Dict[str, Any]]:
        """反例（判定の根拠が SAT のときの canonical witness）。無ければ None。"""
        representative = self.first_definitive
        if (
            representative is not None
            and representative.status == SolverStatus.SAT
            and representative.model
        ):
            return representative.model
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


class ParallelSolverRunner:
    """1 つの query を設定された全 backend で解き、結果を `smt.aggregation` でまとめる。"""
    
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

                return enforce_witness_contract(solver, result)
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
        """全 backend を並列に実行し、全部の結果を `smt.aggregation` でまとめる。

        最初に終わった backend で打ち切らない: 打ち切ると、どの backend が先に
        終わったか（と runner がそれを受け取った順）で判定と反例が変わり、SAT / UNSAT
        の食い違いも見落とす（Issue #161）。全体の待ちは従来どおり
        `timeout + 10` 秒で、それまでに終わらない backend は TIMEOUT の行になる。
        行は設定された backend の順に並べる。
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
        
            cancellation_token = CancellationToken()
            results: List[SolverResult] = []
            with concurrent.futures.ThreadPoolExecutor(
                max_workers=len(self._solvers)
            ) as executor:
                futures = [
                    executor.submit(
                        self.run_single,
                        solver,
                        smt_script,
                        cancellation_token,
                        runtime_timeout,
                        _orchestrated=True,
                        _journal_query_id=query_id,
                    )
                    for solver in self._solvers
                ]
                _done, not_done = concurrent.futures.wait(
                    futures, timeout=runtime_timeout + 10
                )
                if not_done:
                    if self.debug:
                        print("[ParallelRunner] Overall timeout reached")
                    cancellation_token.cancel()
                    for future in not_done:
                        future.cancel()
                for solver, future in zip(self._solvers, futures):
                    if future in not_done:
                        results.append(SolverResult(
                            solver_name=solver.name,
                            status=SolverStatus.TIMEOUT,
                            elapsed_time=runtime_timeout
                        ))
                        continue
                    try:
                        results.append(future.result())
                    except Exception as e:
                        if self.debug:
                            print(f"[ParallelRunner] {solver.name}: exception - {e}")
                        results.append(SolverResult(
                            solver_name=solver.name,
                            status=SolverStatus.ERROR,
                            error_message=str(e)
                        ))
                    if self.debug:
                        row = results[-1]
                        print(f"[ParallelRunner] {solver.name} completed: {row.status.name} ({row.elapsed_time:.3f}s)")

            parallel = ParallelResult(results=results)
            if self.debug:
                print(f"[ParallelRunner] Final result: is_equivalent={parallel.is_equivalent}")
            return parallel
    
    def run_sequential(
        self,
        smt_script: str,
        timeout: Optional[int] = None,
    ) -> ParallelResult:
        """全 backend を設定順に 1 つずつ実行し、結果を `smt.aggregation` でまとめる。"""
        with _solver_orchestration("run_sequential") as query_id:
            runtime_timeout = self._resolve_timeout(timeout)
            if self.debug:
                print(f"[ParallelRunner] Starting sequential execution with {len(self._solvers)} solvers")
        
            # run_parallel と同じ規則: 全 backend を設定順に実行し、結果を集約する
            # （最初の確定結果で打ち切ると、SAT / UNSAT の食い違いを見落とす）
            results: List[SolverResult] = []
        
            for solver in self._solvers:
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

            return ParallelResult(results=results)

    def _resolve_timeout(self, timeout: Optional[int]) -> int:
        """実行に使うタイムアウトを決定する。"""
        return timeout if timeout is not None else self.timeout

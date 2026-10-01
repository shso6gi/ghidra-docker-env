# -*- coding: utf-8 -*-
"""SMTソルバー並列実行管理"""

import concurrent.futures
import dataclasses
import threading
import time
import inspect
from contextlib import contextmanager
from contextvars import ContextVar
from typing import Any, Dict, List, Optional, Type
from dataclasses import dataclass, field

from scripts.function_tracer_pcode.core.deadline import (
    UNBOUNDED,
    UNBOUNDED_WINDOW,
    ExecutionBound,
    deadline_query,
)
from scripts.function_tracer_pcode.core.stage_journal import (
    journal_counter,
    journal_note,
    journal_stage_end,
    journal_stage_start,
)
from scripts.function_tracer_pcode.core.json_encoding import each, materialize
from scripts.function_tracer_pcode.smt.aggregation import (
    BackendAggregate,
    aggregate_backend_results,
)
from scripts.function_tracer_pcode.smt.interface import (
    BackendTermination,
    SMTSolver,
    SolverResult,
    SolverStatus,
    backend_capabilities,
    enforce_witness_contract,
    execute_on_backend,
    execution_fact,
    not_started_result,
    request_backend_stop,
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

# --------------------------------------------------------------------------
# Issue #106 PR-106-A: 解析の期限と solver の実行
#
#   * 論理的な問い合わせ 1 つ（run_parallel / run_sequential / 直接の run_single /
#     run_backend_query）の owner 側の handle は `core.deadline.deadline_query`。backend の
#     **実行を 1 回始める前ごとに** owner の thread で `begin` する（逐次なら backend ごと。
#     先の backend が期限を越えて返ったら、後の backend は始めない）
#   * 実行ごとの窓（実効の終わりと「解析の期限が時間を決めたか」）は、その実行を始める
#     瞬間に `_execute_within` が `ExecutionBound.window` で求める（worker でも同じ。worker へは
#     `ExecutionBound` を引数で渡す: 期限の object も contextvar も読まない）。窓の終わりを
#     adapter の ``not_after`` に渡し、行に `deadline_limited` を付ける
#   * 返った直後に owner の thread で `settle`（行 → `interface.execution_fact`: 観測された
#     終了原因と、期限が上限を決めたか）。逐次なら **実行ごと・次の backend を始める前**。
#     結論の規則は `core.deadline.settlement` の 1 つだけ: 期限を過ぎていれば答えを採らない、
#     期限が決めた上限で止まった行は期限の限界、それ以外の終わり方（答え・通常の unknown・
#     通常の timeout・中止）は期限の無いときと同じ行のまま、backend の失敗・契約違反は期限で
#     隠さない
#   * 待つのをやめること・pending を取り消すこと・走っている実行を止めること・process が
#     終われることは別のこと（`BackendTermination`）。走っている実行は backend が止め方を
#     主張するときだけ `request_stop` を求め、`RUNNING_STOP_GRACE_SECONDS` 待っても
#     返らなければ「止められない」と記録して、自分で返るまで待つ（その間 process は
#     終われない: supervisor の TIMEOUT が最後の fallback。偽って UNKNOWN にしない）。
#     待つのを期限でやめた行は、期限が時間を決めた行として扱う
#   * 待つのをやめた実行の行は `collected_after_stop` が作る: 答え・停止による中断は採らない
#     （TIMEOUT の行）が、backend が返した **故障**（ERROR・witness の契約違反・中止に隠れた
#     独立した例外）は捨てずに行に残す（レビュー 3 巡目: 置き換えると settle にも authority にも
#     故障が届かない）
#   * backend ごとの違いは adapter（`SMTSolver.execute` / `CAPABILITIES` /
#     `request_stop`）にだけあり、ここは backend 名で分岐しない
# --------------------------------------------------------------------------

#: solver の問い合わせの checkpoint の stage（限界の site）
SOLVER_STAGE = "solver"

#: 止められない worker が残ったことを期限の限界の evidence に書く語（受理判定もこれを読む）
WORKER_NOT_STOPPABLE_EVIDENCE = "worker_stop=not_stoppable"

#: 中断を求めた実行が返るのを待つ上限（z3 の実測は最大 0.12 s）
RUNNING_STOP_GRACE_SECONDS = 1.0


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
    """solver の結果と、その判定。

    作り方は 2 通りあり、どちらで作ったかで `results` の意味が決まる（推測しない）:

    * **1 つの query を backend ごとに解いた行**: `ParallelResult.from_backend_results`
      だけが作る。判定・代表結果・反例は `smt.aggregation` の規則で決まる（backend の
      結果の集合だけで決まり、SAT / UNSAT や witness が食い違えば判定しない）。
      `backend_aggregate` にその集約を持つ。runner と単一 query の実行が使う
    * **producer が合成した結果**（複数の query / region / case の証拠、判定の無い空の
      結果、test の fixture）: 直接構築する。判定は producer が `is_equivalent` で明示し、
      明示しなければ従来どおり先頭の SAT / UNSAT 行から補う。反例は先頭の model 付きの
      SAT 行。backend の集約規則は適用しない（異なる query の SAT と UNSAT は食い違いでは
      ない）

    `first_definitive` の名前は結果 JSON の schema のために残している。
    """
    results: List[SolverResult]
    first_definitive: Optional[SolverResult] = None  # 判定の根拠になった結果
    is_equivalent: Optional[bool] = None
    #: 1 query の backend 集約（`from_backend_results` だけが設定する。結果 JSON の schema・
    #: 比較には入れない）。None なら producer が合成した結果
    backend_aggregate: Optional[BackendAggregate] = field(
        default=None, compare=False, repr=False
    )
    #: TIMEOUT の行があるか（作ったときに 1 度だけ数える事実。`EquivalenceResult.is_timeout` が
    #: 行を辿り直さずに読む。結果 JSON の schema・比較には入れない）。作った後に `results` へ行を
    #: 足さない（足すなら新しい `ParallelResult` を作る: この事実が行と食い違う）
    timed_out: bool = field(default=False, init=False, compare=False, repr=False)

    @classmethod
    def from_backend_results(cls, results: List[SolverResult]) -> "ParallelResult":
        """同じ 1 つの query を、設定された backend の順に解いた行から作る。"""

        aggregate = aggregate_backend_results(results)
        return cls(
            results=list(results),
            first_definitive=aggregate.representative,
            is_equivalent=aggregate.is_equivalent,
            backend_aggregate=aggregate,
        )

    def __post_init__(self) -> None:
        """producer が合成した結果では、判定の無い欄を先頭の SAT / UNSAT 行から補う。"""
        self.timed_out = any(result.status == SolverStatus.TIMEOUT for result in self.results)
        if self.backend_aggregate is not None:
            # 1 query の backend 集約: 判定しなかった（食い違い）ことも結果なので補わない
            return
        if self.first_definitive is None:
            for result in self.results:
                if result.status in (SolverStatus.SAT, SolverStatus.UNSAT):
                    self.first_definitive = result
                    break

        if self.is_equivalent is None and self.first_definitive is not None:
            self.is_equivalent = self.first_definitive.status == SolverStatus.UNSAT

    @property
    def backend_conflict(self) -> Optional[str]:
        """1 query の backend が食い違ったならその種類（`smt.aggregation`）。診断用。"""
        if self.backend_aggregate is None:
            return None
        return self.backend_aggregate.conflict
    
    def get_counterexample(self) -> Optional[Dict[str, Any]]:
        """反例。1 query の backend 集約なら判定の根拠の canonical witness、合成した結果なら
        先頭の model 付きの SAT 行。"""
        if self.backend_aggregate is not None:
            return self.backend_aggregate.counterexample
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
        bound: ExecutionBound = UNBOUNDED,
    ) -> SolverResult:
        """単一ソルバーで実行

        ``_orchestrated`` / ``_journal_query_id`` は計測専用の内部引数。
        run_parallel が worker thread へ submit するとき（ContextVar も
        journal の対応 ID も伝わらない）にだけ明示で渡す。判定には一切
        関与しない。

        ``bound``（Issue #106 PR-106-A）は問い合わせの owner が渡す `ExecutionBound`。
        orchestration の内側（worker を含む）はこれを引数でだけ受け取り、実行を始める瞬間に
        自分の窓を求める。orchestration の外から直接呼ばれたときは、この呼び出し自身が
        問い合わせの入口なので、ここで `begin` し、返った直後に `settle` する。
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
            query = None
            if not orchestrated:
                query = deadline_query(SOLVER_STAGE)
                if not query.begin(runtime_timeout, backend_capabilities(solver).execution_unit):
                    return not_started_result(solver.name)
                bound = query.bound

            # 即座にフラッシュして出力
            if self.debug:
                print(f"[ParallelRunner] >>> Starting {solver.name} (timeout={runtime_timeout}s)...", flush=True)
                sys.stdout.flush()

            try:
                result = _execute_within(
                    solver, smt_script, runtime_timeout, bound, cancellation_token,
                )

                if self.debug:
                    print(f"[ParallelRunner] <<< {solver.name} completed: {result.status.name}", flush=True)

                result = _keep_window(result, enforce_witness_contract(
                    result, smt_script,
                    canonical=bool(getattr(solver, "PROVIDES_CANONICAL_WITNESS", False)),
                ))
            except Exception as e:
                if self.debug:
                    import traceback
                    print(f"[ParallelRunner] {solver.name} exception: {e}", flush=True)
                    print(traceback.format_exc(), flush=True)
                result = SolverResult(
                    solver_name=solver.name,
                    status=SolverStatus.ERROR,
                    error_message=str(e)
                )
            if query is not None:
                query.settle(
                    [execution_fact(result)], evidence=_termination_evidence([result]),
                )
            return result
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
                return ParallelResult.from_backend_results([])
        
            runtime_timeout = self._resolve_timeout(timeout)
            query = deadline_query(SOLVER_STAGE)
            if not query.begin(runtime_timeout):
                return ParallelResult.from_backend_results(
                    [not_started_result(solver.name) for solver in self._solvers]
                )
            if self.debug:
                print(f"[ParallelRunner] Starting parallel execution with {len(self._solvers)} solvers")
        
            cancellation_token = CancellationToken()
            results: List[SolverResult] = []
            executor = concurrent.futures.ThreadPoolExecutor(max_workers=len(self._solvers))
            try:
                futures = [
                    executor.submit(
                        self.run_single,
                        solver,
                        smt_script,
                        cancellation_token,
                        runtime_timeout,
                        _orchestrated=True,
                        _journal_query_id=query_id,
                        bound=query.bound,
                    )
                    for solver in self._solvers
                ]
                # 待つのは従来どおり `timeout + 10` 秒、ただし解析の期限までに clamp する
                wait_seconds, wait_limited = query.wait_timeout(runtime_timeout + 10)
                _done, not_done = concurrent.futures.wait(futures, timeout=wait_seconds)
                stopped: Dict[Any, BackendTermination] = {}
                if not_done:
                    if self.debug:
                        print("[ParallelRunner] Overall timeout reached")
                    stopped = stop_unfinished(
                        list(zip(self._solvers, futures)), not_done, cancellation_token,
                        query_id=query_id,
                    )
                for solver, future in zip(self._solvers, futures):
                    if future in stopped:
                        results.append(collected_after_stop(
                            solver.name, future, stopped[future],
                            elapsed=runtime_timeout, wait_limited=wait_limited,
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
            finally:
                # 走っている実行は `stop_unfinished` が返るまで待ってある（ここで待つものは無い）
                executor.shutdown(wait=True, cancel_futures=True)

            # 停止 → 回収（止められない worker は返るまで待った）→ 確認 → 集約
            query.settle(
                [execution_fact(row) for row in results],
                evidence=_termination_evidence(results),
            )
            parallel = ParallelResult.from_backend_results(results)
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
            query = deadline_query(SOLVER_STAGE)
            if self.debug:
                print(f"[ParallelRunner] Starting sequential execution with {len(self._solvers)} solvers")
        
            # run_parallel と同じ規則: 全 backend を設定順に実行し、結果を集約する
            # （最初の確定結果で打ち切ると、SAT / UNSAT の食い違いを見落とす）
            results: List[SolverResult] = []
        
            for solver in self._solvers:
                if self.debug:
                    print(f"[ParallelRunner] Running {solver.name}...")
            
                # 開始前 → 実行 → 返却直後の確認 → 次の実行（期限で切られた backend の後の
                # backend は呼ばない: `settle` が raise する）。単位はこの backend の単位
                if not query.begin(runtime_timeout, backend_capabilities(solver).execution_unit):
                    results.append(not_started_result(solver.name))
                    continue
                result = self.run_single(
                    solver,
                    smt_script,
                    timeout=runtime_timeout,
                    _journal_query_id=query_id,
                    bound=query.bound,
                )
                results.append(result)
            
                if self.debug:
                    print(f"[ParallelRunner] {solver.name}: {result.status.name} ({result.elapsed_time:.3f}s)")
                query.settle([execution_fact(result)], evidence=_termination_evidence(results))

            return ParallelResult.from_backend_results(results)

    def _resolve_timeout(self, timeout: Optional[int]) -> int:
        """実行に使うタイムアウトを決定する。"""
        return timeout if timeout is not None else self.timeout


def run_backend_query(
    backend: SMTSolver,
    smt_script: str,
    *,
    cancellation_token: Optional[CancellationToken] = None,
) -> SolverResult:
    """backend 1 つで 1 回だけ問う（runner を通さない直接の問い合わせの入口、Issue #106 PR-106-A）。

    runner の問い合わせと同じ規則: 始める前に owner の thread で `begin`（過ぎていれば限界を
    raise）、実行の窓を始める瞬間に求めて終わりを adapter へ引数で渡し、返った直後に `settle`。時間は
    backend の設定（`backend.timeout` 秒）。counter / journal / witness の検査は従来どおり
    行わない（status だけを読む呼び出し元のため）。
    """

    timeout_seconds = backend.timeout
    query = deadline_query(SOLVER_STAGE)
    if not query.begin(timeout_seconds, backend_capabilities(backend).execution_unit):
        return not_started_result(backend.name)
    result = _execute_within(backend, smt_script, timeout_seconds, query.bound, cancellation_token)
    query.settle([execution_fact(result)], evidence=_termination_evidence([result]))
    return result


def _execute_within(
    backend: Any,
    smt_script: str,
    timeout_seconds: float,
    bound: ExecutionBound,
    cancellation_token: Optional[CancellationToken],
) -> SolverResult:
    """backend の実行 1 回（**実行を始めるこの瞬間の** 窓で。どの thread でも同じ手順）。

    窓は `core.deadline.execution_window`（backend の単位で）。始める時間が無ければ実行しない
    行、あれば窓の終わりを adapter へ渡し、行に `deadline_limited` を付ける。
    """

    if bound.not_after is None:
        window = UNBOUNDED_WINDOW
    else:
        window = bound.window(timeout_seconds, backend_capabilities(backend).execution_unit)
    if window is None:
        return not_started_result(getattr(backend, "name", type(backend).__name__))
    result = execute_on_backend(
        backend, smt_script, timeout_seconds=timeout_seconds,
        not_after=window.adapter_end, cancellation_token=cancellation_token,
    )
    result.deadline_limited = window.limited or result.deadline_limited
    return result


def _keep_window(executed: SolverResult, checked: SolverResult) -> SolverResult:
    """契約の検査で作り直した行にも、実行の窓の事実を引き継ぐ。"""

    if checked is not executed:
        checked.deadline_limited = executed.deadline_limited
        checked.termination = executed.termination
    return checked


def stop_unfinished(
    backends_and_futures: List[Any],
    not_done: Any,
    cancellation_token: CancellationToken,
    *,
    query_id: Optional[int] = None,
    grace_seconds: float = RUNNING_STOP_GRACE_SECONDS,
) -> Dict[Any, BackendTermination]:
    """待つのをやめた実行を止める（Issue #106 PR-106-A）。返す値は future → 終わり方。

    1. 中止を知らせる（cancellation token）
    2. まだ始まっていない future は取り消す（`CANCELLED_PENDING`）
    3. 走っている実行は、backend が止め方を主張するときだけ `request_stop` を求める
    4. `grace_seconds` 待って返ったものは、止めるよう求めたなら `STOPPED`、求めていない
       （止め方が無い）なら `RETURNED_LATE`（どちらも答えは採らない）
    5. 返らないものは `NOT_STOPPABLE`。journal に記録してから、**自分で返るまで待つ**
       （worker を残したまま結果を確定しない。process はそれまで終われず、supervisor の
       TIMEOUT が最後の fallback になる）

    どの手順も backend の能力（`SolverBackendCapabilities`）だけで決まり、backend 名を見ない。
    """

    cancellation_token.cancel()
    terminations: Dict[Any, BackendTermination] = {}
    running = []
    for backend, future in backends_and_futures:
        if future not in not_done:
            continue
        if future.cancel():
            terminations[future] = BackendTermination.CANCELLED_PENDING
            continue
        running.append((backend, future))
    stop_requested = {future for backend, future in running if request_backend_stop(backend)}
    if running:
        returned, still_running = concurrent.futures.wait(
            [future for _backend, future in running], timeout=grace_seconds,
        )
        for future in returned:
            # 止めるよう求めて返ったものは STOPPED。求めずに（止め方が無いのに）返ったものは
            # 待つのをやめた後で自分で返った: その答えは採らない（RETURNED_LATE）
            terminations[future] = (
                BackendTermination.STOPPED if future in stop_requested
                else BackendTermination.RETURNED_LATE
            )
        if still_running:
            stuck = [
                (backend, future) for backend, future in running if future in still_running
            ]
            for _backend, future in stuck:
                terminations[future] = BackendTermination.NOT_STOPPABLE
            journal_note("solver_worker_not_stoppable", {
                "query_id": query_id,
                "backends": [str(getattr(backend, "name", type(backend).__name__)) for backend, _f in stuck],
                "guarantee_classes": [backend_capabilities(backend).guarantee_class for backend, _f in stuck],
                "action": "wait_for_worker_to_return",
            })
            concurrent.futures.wait(still_running)
    return terminations


def collected_after_stop(
    solver_name: str,
    future: Any,
    termination: BackendTermination,
    *,
    elapsed: float,
    wait_limited: bool,
) -> SolverResult:
    """待つのをやめた実行の行（Issue #106 PR-106-A）。**backend が実際に返したものを捨てない**。

    待ちの上限で止めた実行の答え（SAT / UNSAT）・判定不能・停止による中断は採らない
    （従来どおり TIMEOUT の行。待つのを期限でやめたなら期限が時間を決めた行: ``wait_limited``）。
    ただし backend が返した行（または worker の例外）に **故障** があれば、それを結果に残す:
    ERROR の行（parse error・witness の契約違反など）はそのまま、終了原因が中止でも独立した
    故障（`SolverResult.observed_failure`）を観測していれば ERROR の行にする（ここで使う中止の
    token は runner 自身のもので、停止の手順の一部: 呼び出し側の明示の中止ではない）。
    故障を TIMEOUT に置き換えると、期限の判定（`core.deadline.settlement`）にも authority にも
    故障が届かない。
    """

    returned: Optional[SolverResult] = None
    if termination is not BackendTermination.CANCELLED_PENDING and future.done():
        raised = future.exception()  # 例外を上げずに読む（worker の例外は故障の事実）
        if raised is not None:
            returned = SolverResult(
                solver_name=solver_name, status=SolverStatus.ERROR,
                error_message=f"{type(raised).__name__}: {raised}",
            )
        else:
            returned = future.result()
    if returned is not None and execution_fact(returned).failure_observed:
        if returned.status == SolverStatus.ERROR:
            row = dataclasses.replace(returned)
        else:
            row = SolverResult(
                solver_name=solver_name,
                status=SolverStatus.ERROR,
                elapsed_time=returned.elapsed_time,
                error_message=returned.observed_failure,
            )
        row.termination = termination
        row.deadline_limited = wait_limited
        return row
    abandoned = (
        "" if returned is None
        else f"wait abandoned at its limit; the backend returned {returned.status.name}"
    )
    return SolverResult(
        solver_name=solver_name,
        status=SolverStatus.TIMEOUT,
        elapsed_time=elapsed,
        error_message=abandoned or None,
        termination=termination,
        # 待つのを期限でやめたなら、その行の時間は期限が決めた
        deadline_limited=wait_limited,
    )


def _termination_evidence(results: List[SolverResult]) -> tuple:
    """解析の期限で打ち切ったときの限界に添える、backend 実行の終わり方（診断）。"""

    rows = []
    for row in results:
        termination = getattr(row, "termination", BackendTermination.COMPLETED)
        if termination is BackendTermination.COMPLETED:
            continue
        rows.append(f"backend={row.solver_name}:{termination.value}")
        if termination is BackendTermination.NOT_STOPPABLE:
            rows.append(WORKER_NOT_STOPPABLE_EVIDENCE)
    return tuple(rows)

# -*- coding: utf-8 -*-
"""Z3ソルバー実装（タイムアウト検出修正版）"""

import time
import importlib
from dataclasses import dataclass
from typing import Optional, Dict, Any, Tuple, cast

from scripts.function_tracer_pcode.smt.execution import CANCELLED, ExecutionBudget
from scripts.function_tracer_pcode.smt.interface import (
    SMTSolver,
    SolverResult,
    SolverStatus,
    interrupted_result,
    sat_with_canonical_witness,
)
from scripts.function_tracer_pcode.smt.witness import (
    BOOL,
    INCONCLUSIVE,
    INT,
    Constraint,
    WitnessTarget,
    WitnessUnavailable,
    canonical_witness,
    witness_preferences,
    witness_targets,
)


class _Z3WitnessSession:
    """`smt.witness.WitnessSession` の z3 実装（同じ solver の上で push / pop する）。

    実行の期限と中止は、呼び出し側（backend の実行入口）が作った **1 つの**
    `ExecutionBudget` で、初回の check と共有する。各問いの前に中断を確かめ、問いには
    期限までの残りだけを与える。問いが unknown を返したら、それが中断かどうかを同じ
    `ExecutionBudget` に問う（規則は `smt.execution` の 1 箇所）。
    """

    def __init__(
        self, z3: Any, solver: Any, model: Any, targets: tuple, budget: ExecutionBudget,
        preference_terms: Optional[Dict[str, Any]] = None,
    ) -> None:
        self._z3 = z3
        self._solver = solver
        self._budget = budget
        self._preference_terms = dict(preference_terms or {})
        ctx = getattr(model, "ctx", None)
        self._terms = {}
        for target in targets:
            symbol = target.solver_symbol
            if target.sort == BOOL:
                self._terms[target.name] = z3.Bool(symbol, ctx=ctx)
            elif target.sort == INT:
                self._terms[target.name] = z3.Int(symbol, ctx=ctx)
            else:
                self._terms[target.name] = z3.BitVec(symbol, target.width, ctx=ctx)
        self._targets = targets
        self._model = model
        self._values = self._read(model)

    def _read(self, model: Any) -> Dict[str, int]:
        values: Dict[str, int] = {}
        for target in self._targets:
            value = model.eval(self._terms[target.name], model_completion=True)
            if target.sort == BOOL:
                if self._z3.is_true(value):
                    values[target.name] = 1
                elif self._z3.is_false(value):
                    values[target.name] = 0
                else:
                    raise WitnessUnavailable(
                        INCONCLUSIVE, f"Bool value is not concrete: {target.name}"
                    )
            else:
                values[target.name] = value.as_long()
        return values

    def _term(self, constraint: Constraint) -> Any:
        z3 = self._z3
        if constraint.kind == "preference":
            return self._preference_terms[constraint.preference]
        term = self._terms[constraint.target.name]
        if constraint.target.sort == INT:
            value = z3.IntVal(constraint.value, ctx=term.ctx)
            if constraint.kind == "abs_le":
                return z3.And(term <= value, term >= -value)
            return term == value
        if constraint.target.sort == BOOL:
            if constraint.kind == "low_zero":
                return z3.Not(term)
            return term if constraint.value == 1 else z3.Not(term)
        if constraint.kind == "low_zero":
            return z3.Extract(constraint.bit, 0, term) == z3.BitVecVal(
                0, constraint.bit + 1, ctx=term.ctx
            )
        return z3.Extract(constraint.bit, constraint.bit, term) == z3.BitVecVal(
            constraint.value, 1, ctx=term.ctx
        )

    def values(self) -> Dict[str, int]:
        return dict(self._values)

    def holds(self, constraint: Constraint) -> bool:
        return self._z3.is_true(self._model.eval(self._term(constraint), model_completion=True))

    def check_with(self, constraint: Constraint) -> Optional[Dict[str, int]]:
        stop = self._budget.interruption()
        if stop is not None:
            raise WitnessUnavailable(stop, "the execution stopped during the witness search")
        self._solver.push()
        try:
            self._solver.set("timeout", max(1, self._budget.remaining_ms()))
            self._solver.add(self._term(constraint))
            verdict = self._solver.check()
            if verdict == self._z3.sat:
                self._model = self._solver.model()
                self._values = self._read(self._model)
                return dict(self._values)
            if verdict == self._z3.unsat:
                return None
            reason = str(self._solver.reason_unknown())
            stop = self._budget.interruption_after_unknown(reason)
            if stop is not None:
                raise WitnessUnavailable(
                    stop, f"the execution stopped during the witness search ({reason})"
                )
            raise WitnessUnavailable(INCONCLUSIVE, f"a witness question was inconclusive: {reason}")
        finally:
            self._solver.pop()

    def fix(self, constraint: Constraint) -> None:
        self._solver.add(self._term(constraint))


@dataclass(frozen=True)
class PreparedWitnessQuery:
    """1 つの query を z3 で解くために、実行の最初に 1 回だけ用意するもの。

    `assertions` は query の本体、`preference_terms` は witness の優先の項（script の
    `define-fun |witness-preference:<k>|` を同じ parse で取り出したもの）、`targets` は
    witness の成分。witness の探索はここにあるものだけを使い、script を読み直さない
    （実行の期限の外で parse しない）。
    """

    assertions: Tuple[Any, ...]
    preference_terms: Tuple[Tuple[str, Any], ...]
    targets: Tuple[WitnessTarget, ...]


def prepare_witness_query(z3: Any, smt_script: str, ctx: Any) -> PreparedWitnessQuery:
    """`smt_script` を `ctx` に 1 回だけ parse して、本体と witness の優先の項を分ける。

    preference は assert しないので、本体の後ろに `(assert <name>)` を足して 1 回で parse
    し、末尾の k 個を preference の項として切り出す（本体には入れない）。
    """

    preferences = witness_preferences(smt_script)
    appended = "".join(f"\n(assert {name})" for name in preferences)
    parsed = tuple(z3.parse_smt2_string(smt_script + appended, ctx=ctx))
    split = len(parsed) - len(preferences)
    return PreparedWitnessQuery(
        assertions=parsed[:split],
        preference_terms=tuple(zip(preferences, parsed[split:])),
        targets=witness_targets(smt_script),
    )


def canonical_declared_model(
    z3: Any, solver: Any, prepared: PreparedWitnessQuery, *, budget: ExecutionBudget,
) -> Dict[str, Any]:
    """SAT の solver から、query の scalar 入力の canonical な witness を作る。

    `solver` は直前の `check()` が SAT だったもの。値は `smt.witness.canonical_witness`
    の規則で決まり、solver の履歴にも最初の model にも依らない。`budget` はその check と
    共有する実行の予算で、探索の問いは残りの時間だけを使い、中断されたら問わない。
    script は読み直さない（`prepared` を使う）。探索で足した制約は push で囲むので、
    返ったあとの `solver` は元の assertion のまま。決められなければ `WitnessUnavailable`。
    """

    # model は push より前に読む（push すると直前の check の model は使えなくなる）
    model = solver.model()
    session = _Z3WitnessSession(
        z3, solver, model, prepared.targets, budget,
        preference_terms=dict(prepared.preference_terms),
    )
    solver.push()
    try:
        return canonical_witness(
            session, prepared.targets, [name for name, _term in prepared.preference_terms]
        )
    finally:
        solver.pop()


def sat_result_with_witness(
    z3: Any, solver: Any, prepared: PreparedWitnessQuery, *, solver_name: str, started: float,
    budget: ExecutionBudget,
) -> SolverResult:
    """直前の `check()` が SAT だった z3 の solver の結果。

    確定の手順（witness の生成の前後の中断確認を含む）は
    `smt.interface.sat_with_canonical_witness` が持ち、ここは z3 の canonicalize だけを渡す。
    """

    return sat_with_canonical_witness(
        solver_name,
        started=started,
        budget=budget,
        canonicalize=lambda: canonical_declared_model(z3, solver, prepared, budget=budget),
    )


def isolated_solver(z3: Any, smt_script: str, timeout_ms: int) -> Any:
    """script を専用の z3 context に parse した solver を作る（status だけを使う問い合わせ用）。

    同じ context を共有すると、先に parse した式（別の query）が後の solver の探索に
    影響し得る（Issue #161）。query ごとに context を分けて、解く対象を script だけにする。
    SAT の witness を返す実行（`Z3Solver`）は `prepare_witness_query` を使う。
    """

    context = z3.Context()
    solver = z3.Solver(ctx=context)
    solver.set("timeout", int(timeout_ms))
    solver.add(z3.parse_smt2_string(smt_script, ctx=context))
    return solver


class Z3Solver(SMTSolver):
    """Z3 SMTソルバー"""

    PROVIDES_CANONICAL_WITNESS = True
    
    def __init__(self, timeout: int = 10, debug: bool = False):
        super().__init__(timeout)
        self._z3 = None
        self._solver = None
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
        # Issue #161: 実行の状態（期限と中止）は 1 回の実行に 1 つの `ExecutionBudget`。
        # 入口で作り、query の準備・初回の check・canonical witness の生成と SAT の確定の
        # すべてがこれに問う（初回の check には残りだけを与える）。
        budget = ExecutionBudget.starting_now(self.timeout, cancellation_token)
        
        try:
            z3 = self._z3
            if z3 is None:
                raise RuntimeError("Z3 module not loaded")

            # query ごとに専用の context（先に解いた query の影響を受けない）。parse は
            # この 1 回だけで、witness の探索は script を読み直さない。
            try:
                context = z3.Context()
                prepared = prepare_witness_query(z3, smt_script, context)
                self._solver = z3.Solver(ctx=context)
                self._solver.add(*prepared.assertions)
            except Exception as e:
                self._debug_print(f"Parse error: {e}")
                return self._create_error_result(f"Parse error: {e}")

            # 準備のあと: 中止・期限切れなら check をしない
            stop = budget.interruption()
            if stop is not None:
                return interrupted_result(
                    self.name, stop, "the execution stopped before the check",
                    time.time() - start_time,
                )
            remaining_ms = max(1, budget.remaining_ms())
            self._solver.set("timeout", remaining_ms)
            self._debug_print(f"Z3 timeout set to {remaining_ms}ms")
            
            self._debug_print("Starting check...")
            result = self._solver.check()
            elapsed = time.time() - start_time
            self._debug_print(f"Check completed: {result} ({elapsed:.3f}s)")
            
            if result == z3.sat:
                # 返す model は script の意味だけで決まる canonical witness（solver が
                # 最初に見つけた model ではない）。確定の手順は interface が持つ。
                sat_result = sat_result_with_witness(
                    z3, self._solver, prepared, solver_name=self.name,
                    started=start_time, budget=budget,
                )
                self._debug_print(f"Model extracted: {sat_result.model}")
                return sat_result
            elif result == z3.unsat:
                # UNSAT は初回の check だけで完結する（後段の仕事が無い）。明示の中止だけは
                # 全経路で優先する（中止された実行の確定結果を返さない）。期限は従来どおり
                # z3 の timeout が強制する
                if budget.interruption() == CANCELLED:
                    return interrupted_result(
                        self.name, CANCELLED, "the execution was cancelled during the check",
                        elapsed,
                    )
                return SolverResult(
                    solver_name=self.name,
                    status=SolverStatus.UNSAT,
                    elapsed_time=elapsed
                )
            else:
                # unknown: 中断（中止・期限切れ）かどうかは実行の予算に問う（全経路で同じ
                # 規則）。中断でなければ従来の判定（経過が予算の 90% 以上なら TIMEOUT）
                reason = str(self._solver.reason_unknown())
                self._debug_print(f"Reason for unknown: {reason}")
                stop = budget.interruption_after_unknown(reason)
                if stop is not None:
                    return interrupted_result(self.name, stop, reason, elapsed)
                
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
    

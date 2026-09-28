# -*- coding: utf-8 -*-
"""Z3ソルバー実装（タイムアウト検出修正版）"""

import time
import importlib
import re
from typing import Optional, Dict, Any, Tuple, cast

from scripts.function_tracer_pcode.smt.interface import (
    SMTSolver,
    SolverResult,
    SolverStatus,
    witness_failure_result,
)
from scripts.function_tracer_pcode.smt.witness import (
    BOOL,
    BUDGET_EXHAUSTED,
    CANCELLED,
    INCONCLUSIVE,
    INT,
    WITNESS_PREFERENCE_PREFIX,
    Constraint,
    WitnessUnavailable,
    canonical_witness,
    targets_in_declaration_order,
)


#: SMT-LIB の symbol（quoted symbol `|...|` は空白を含み得るので 1 つの名前として読む）
_SYMBOL = r"(?:\|[^|]*\||[^\s()|]+)"
_DECLARATION_RE = re.compile(
    r"^\(declare-(?:const\s+(" + _SYMBOL + r")|fun\s+(" + _SYMBOL + r")\s+\(\))\s+(.+)\)$",
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


def _declared_sorts(smt_script: str) -> tuple:
    """script の定数宣言を宣言順に ``(name, sort text)`` で返す（重複は拒否）。"""

    declarations = []
    declared_names = set()
    for command in _top_level_smt_commands(smt_script):
        match = _DECLARATION_RE.fullmatch(command.strip())
        if match is None:
            continue
        name = match.group(1) or match.group(2)
        if name in declared_names:
            raise ValueError(f"duplicate SMT declaration: {name}")
        declared_names.add(name)
        declarations.append((name, match.group(3).strip()))
    return tuple(declarations)


_PREFERENCE_RE = re.compile(
    r"^\(define-fun\s+(\|" + re.escape(WITNESS_PREFERENCE_PREFIX) + r"([0-9]+)\|)\s+\(\)\s+Bool\s",
    re.DOTALL,
)


def _declared_preferences(smt_script: str) -> tuple:
    """script が宣言する witness の preference の名前（優先順）。"""

    found = []
    for command in _top_level_smt_commands(smt_script):
        match = _PREFERENCE_RE.match(command.strip())
        if match is not None:
            found.append((int(match.group(2)), match.group(1)))
    return tuple(name for _order, name in sorted(found))


class _Z3WitnessSession:
    """`smt.witness.WitnessSession` の z3 実装（同じ solver の上で push / pop する）。

    時間予算は呼び出し側（backend の実行入口）が決めた **1 つの** 期限 `deadline`
    （`time.monotonic()` の値）で、初回の check と共有する。各問いには期限までの残りだけを
    与え、期限を過ぎたら問わない。`cancellation_token` が中止されたら問わない。
    """

    def __init__(
        self, z3: Any, solver: Any, model: Any, targets: tuple, deadline: float,
        preference_terms: Optional[Dict[str, Any]] = None,
        cancellation_token: Optional[Any] = None,
    ) -> None:
        self._z3 = z3
        self._solver = solver
        self._deadline = deadline
        self._cancellation_token = cancellation_token
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
        if self._cancellation_token is not None and self._cancellation_token.is_cancelled():
            raise WitnessUnavailable(CANCELLED, "the solver execution was cancelled")
        remaining_ms = int((self._deadline - time.monotonic()) * 1000)
        if remaining_ms <= 0:
            raise WitnessUnavailable(
                BUDGET_EXHAUSTED, "the execution budget ran out during the witness search"
            )
        self._solver.push()
        try:
            self._solver.set("timeout", remaining_ms)
            self._solver.add(self._term(constraint))
            verdict = self._solver.check()
            if verdict == self._z3.sat:
                self._model = self._solver.model()
                self._values = self._read(self._model)
                return dict(self._values)
            if verdict == self._z3.unsat:
                return None
            reason = str(self._solver.reason_unknown())
            if reason in ("timeout", "canceled") or time.monotonic() >= self._deadline:
                raise WitnessUnavailable(
                    BUDGET_EXHAUSTED,
                    f"the execution budget ran out during the witness search ({reason})",
                )
            raise WitnessUnavailable(INCONCLUSIVE, f"a witness question was inconclusive: {reason}")
        finally:
            self._solver.pop()

    def fix(self, constraint: Constraint) -> None:
        self._solver.add(self._term(constraint))


def canonical_declared_model(
    z3: Any, solver: Any, smt_script: str, *, deadline: float,
    cancellation_token: Optional[Any] = None,
) -> Dict[str, Any]:
    """SAT の solver から、script が宣言する scalar 入力の canonical な witness を作る。

    `solver` は直前の `check()` が SAT だったもの。値は `smt.witness.canonical_witness`
    の規則で決まり、solver の履歴にも最初の model にも依らない。`deadline` はその
    check と共有する実行の期限（`time.monotonic()` の値）で、探索は残りの時間だけを使う。
    探索で足した制約は push で囲むので、返ったあとの `solver` は元の assertion のまま。
    決められなければ `WitnessUnavailable`。
    """

    targets = targets_in_declaration_order(_declared_sorts(smt_script))
    preferences = _declared_preferences(smt_script)
    # model は push より前に読む（push すると直前の check の model は使えなくなる）
    model = solver.model()
    preference_terms = {}
    for name in preferences:
        # preference の本体は script の define-fun。同じ context に script ごと parse し
        # 直して、末尾に足した `(assert name)` の項を取り出す（宣言は同じ項になる）。
        preference_terms[name] = z3.parse_smt2_string(
            smt_script + f"\n(assert {name})", ctx=model.ctx
        )[-1]
    session = _Z3WitnessSession(
        z3, solver, model, targets, deadline,
        preference_terms=preference_terms, cancellation_token=cancellation_token,
    )
    solver.push()
    try:
        return canonical_witness(session, targets, preferences)
    finally:
        solver.pop()


def sat_result_with_witness(
    z3: Any, solver: Any, smt_script: str, *, solver_name: str, started: float,
    deadline: float, cancellation_token: Optional[Any] = None,
) -> SolverResult:
    """直前の `check()` が SAT だった solver の結果（`SolverResult.model` の契約どおり）。

    canonical witness を決められたら SAT とその witness、決められなければ
    `witness_failure_result`（SAT にはしない）。`started` は `time.time()` での実行開始
    （elapsed の起点）、`deadline` は実行の期限（`time.monotonic()`）。
    """

    try:
        model = canonical_declared_model(
            z3, solver, smt_script, deadline=deadline, cancellation_token=cancellation_token,
        )
    except WitnessUnavailable as failure:
        return witness_failure_result(solver_name, failure, time.time() - started)
    return SolverResult(
        solver_name=solver_name,
        status=SolverStatus.SAT,
        elapsed_time=time.time() - started,
        model=model,
    )


def isolated_solver(z3: Any, smt_script: str, timeout_ms: int) -> Any:
    """script を専用の z3 context に parse した solver を作る。

    同じ context を共有すると、先に parse した式（別の query）が後の solver の探索に
    影響し得る（Issue #161）。query ごとに context を分けて、解く対象を script だけにする。
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
        
        try:
            z3 = self._z3
            if z3 is None:
                raise RuntimeError("Z3 module not loaded")

            # Issue #161: query ごとに専用の context（先に解いた query の影響を受けない）
            try:
                self._solver = isolated_solver(z3, smt_script, self.timeout * 1000)
                self._debug_print(f"Z3 timeout set to {self.timeout * 1000}ms")
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
            
            # 検証実行。時間予算は 1 回の実行に 1 つ（Issue #161）: 初回の check と
            # canonical witness の探索が同じ期限を共有し、探索は残りの時間だけを使う。
            self._debug_print("Starting check...")
            deadline = time.monotonic() + self.timeout
            result = self._solver.check()
            elapsed = time.time() - start_time
            self._debug_print(f"Check completed: {result} ({elapsed:.3f}s)")
            
            if result == z3.sat:
                # 返す model は script の意味だけで決まる canonical witness（solver が
                # 最初に見つけた model ではない）。決められなければ SAT にしない。
                sat_result = sat_result_with_witness(
                    z3, self._solver, smt_script, solver_name=self.name,
                    started=start_time, deadline=deadline,
                    cancellation_token=cancellation_token,
                )
                self._debug_print(f"Model extracted: {sat_result.model}")
                return sat_result
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
    

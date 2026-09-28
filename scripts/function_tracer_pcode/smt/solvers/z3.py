# -*- coding: utf-8 -*-
"""Z3ソルバー実装（タイムアウト検出修正版）"""

import time
import importlib
import re
from typing import Optional, Dict, Any, Tuple, Callable, cast

from scripts.function_tracer_pcode.smt.interface import SMTSolver, SolverResult, SolverStatus
from scripts.function_tracer_pcode.smt.witness import (
    BOOL,
    WITNESS_PREFERENCE_PREFIX,
    Constraint,
    WitnessUnavailable,
    canonical_witness,
    targets_in_declaration_order,
)


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
    """`smt.witness.WitnessSession` の z3 実装（同じ solver の上で push / pop する）。"""

    def __init__(
        self, z3: Any, solver: Any, model: Any, targets: tuple, deadline: float,
        preference_terms: Optional[Dict[str, Any]] = None,
    ) -> None:
        self._z3 = z3
        self._solver = solver
        self._deadline = deadline
        self._preference_terms = dict(preference_terms or {})
        ctx = getattr(model, "ctx", None)
        self._terms = {}
        for target in targets:
            if target.sort == BOOL:
                self._terms[target.name] = z3.Bool(target.name, ctx=ctx)
            else:
                self._terms[target.name] = z3.BitVec(target.name, target.width, ctx=ctx)
        self._targets = targets
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
                    raise WitnessUnavailable(f"Bool value is not concrete: {target.name}")
            else:
                values[target.name] = value.as_long()
        return values

    def _term(self, constraint: Constraint) -> Any:
        z3 = self._z3
        if constraint.kind == "preference":
            return self._preference_terms[constraint.preference]
        term = self._terms[constraint.target.name]
        if constraint.target.sort == BOOL:
            if constraint.kind == "ne":
                return term if constraint.value == 0 else z3.Not(term)
            return term if constraint.value == 1 else z3.Not(term)
        width = constraint.target.width
        if constraint.kind == "bit":
            return z3.Extract(constraint.bit, constraint.bit, term) == z3.BitVecVal(
                constraint.value, 1, ctx=term.ctx
            )
        value = z3.BitVecVal(constraint.value, width, ctx=term.ctx)
        return term != value if constraint.kind == "ne" else term == value

    def values(self) -> Dict[str, int]:
        return dict(self._values)

    def check_with(self, constraint: Constraint) -> Optional[Dict[str, int]]:
        remaining_ms = int((self._deadline - time.monotonic()) * 1000)
        if remaining_ms <= 0:
            raise WitnessUnavailable("canonical witness search exceeded its time budget")
        self._solver.push()
        try:
            self._solver.set("timeout", remaining_ms)
            self._solver.add(self._term(constraint))
            verdict = self._solver.check()
            if verdict == self._z3.sat:
                return self._read(self._solver.model())
            if verdict == self._z3.unsat:
                return None
            raise WitnessUnavailable(
                f"canonical witness search was inconclusive: {self._solver.reason_unknown()}"
            )
        finally:
            self._solver.pop()

    def fix(self, constraint: Constraint) -> None:
        self._solver.add(self._term(constraint))


def canonical_declared_model(
    z3: Any, solver: Any, smt_script: str, *, budget_seconds: float,
) -> Dict[str, int]:
    """SAT の solver から、script が宣言する scalar 入力の canonical な witness を作る。

    `solver` は直前の `check()` が SAT だったもの。値は `smt.witness.canonical_witness`
    の規則（宣言順・unsigned の辞書式最小）で決まり、solver の履歴にも最初の model にも
    依らない。配列・関数などの解釈は含めない（最小が定まらず、replay も使わない）。
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
        z3, solver, model, targets, time.monotonic() + max(0.001, budget_seconds),
        preference_terms=preference_terms,
    )
    solver.push()
    try:
        return canonical_witness(session, targets, preferences)
    finally:
        solver.pop()


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
            
            # 検証実行
            self._debug_print("Starting check...")
            result = self._solver.check()
            elapsed = time.time() - start_time
            self._debug_print(f"Check completed: {result} ({elapsed:.3f}s)")
            
            if result == z3.sat:
                self._model = self._solver.model()
                # Issue #161: 返す model は script の意味だけで決まる canonical な
                # witness（solver が最初に見つけた model ではない）。決められなければ
                # model 無しの SAT（replay はそれを反例として受け入れない）。
                try:
                    model_dict = canonical_declared_model(
                        z3, self._solver, smt_script, budget_seconds=self.timeout
                    )
                    witness_note = None
                except WitnessUnavailable as exc:
                    model_dict = None
                    witness_note = f"canonical witness unavailable: {exc}"
                self._debug_print(f"Model extracted: {model_dict}")
                return SolverResult(
                    solver_name=self.name,
                    status=SolverStatus.SAT,
                    elapsed_time=time.time() - start_time,
                    model=model_dict,
                    error_message=witness_note,
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
    
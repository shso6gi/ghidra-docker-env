# -*- coding: utf-8 -*-
"""SMTソルバーの抽象インターフェース（修正版）"""

from abc import ABC, abstractmethod
from enum import Enum, auto
from typing import Callable, ClassVar, Optional, Dict, Any, Tuple
from dataclasses import dataclass
import time


# Re-exports kept for callers that import these names from this module.
from typing import List  # noqa: F401
from scripts.function_tracer_pcode.core import live_values
from scripts.function_tracer_pcode.core.deadline import TimeUnit, bounded_timeout
from scripts.function_tracer_pcode.core.json_encoding import materialize
from scripts.function_tracer_pcode.smt.execution import (
    BUDGET_EXHAUSTED,
    CANCELLED,
    ExecutionBudget,
)
from scripts.function_tracer_pcode.smt.witness import (
    INCONCLUSIVE,
    WitnessUnavailable,
    witness_contract_violation,
    witness_targets,
)


class SolverStatus(Enum):
    """ソルバーの結果ステータス"""
    SAT = auto()        # 充足可能（反例あり = 等価でない）
    UNSAT = auto()      # 充足不可能（等価）
    UNKNOWN = auto()    # 判定不能
    TIMEOUT = auto()    # タイムアウト
    ERROR = auto()      # エラー発生


class BackendTermination(Enum):
    """1 つの backend 実行がどう終わったか（Issue #106 PR-106-A）。

    status（何が分かったか）とは別の軸で、「待つのをやめた」「実行を止めた」「止められ
    なかった」を 1 つの timeout に潰さないためにある。結果 JSON の schema には入れない。
    """

    #: backend が自分で返った（答え・自分の timeout・unknown のどれでも）
    COMPLETED = "completed"
    #: 期限までの時間が無いので始めなかった
    NOT_STARTED = "not_started"
    #: 始まる前に取り消した（pending の future）
    CANCELLED_PENDING = "cancelled_pending"
    #: 走っていた実行を中断の要求で止めた（待ちの上限の中で返った）
    INTERRUPTED = "interrupted"
    #: 走っていた実行を止められなかった（要求しても返らない・止める手段が無い）。runner は
    #: その実行が自分で返るまで待つ（process はそれまで終われない: supervisor の TIMEOUT が
    #: 最後の fallback）
    NOT_STOPPABLE = "not_stoppable"


@dataclass(frozen=True)
class SolverBackendCapabilities:
    """backend adapter が **実測の根拠をもって** 主張できる時間制御の能力（既定は主張なし）。

    ``native_timeout``    backend 自身が timeout で実行を打ち切る（``timeout_unit`` の単位）
    ``absolute_deadline`` `SMTSolver.execute` が ``not_after``（absolute monotonic）を守る
    ``interrupt``         別 thread からの `request_interrupt()` で走っている実行が返る
    ``cancel``            cancellation token を実行の段の間で確かめる
    ``hard_stop``         実行を強制終了できる（外部 process の kill など）

    主張しない能力は無いものとして扱う（runner はそれを前提に止め方を選ぶ）。
    """

    native_timeout: bool = False
    timeout_unit: Optional[TimeUnit] = None
    absolute_deadline: bool = False
    interrupt: bool = False
    cancel: bool = False
    hard_stop: bool = False

    @property
    def cooperative(self) -> bool:
        """期限の中で自分で止まることを保証できるか（Class A / B の区別）。"""

        return self.native_timeout and self.absolute_deadline

    @property
    def stoppable_while_running(self) -> bool:
        """走っている実行を外から止められるか。"""

        return self.interrupt or self.hard_stop

    @property
    def guarantee_class(self) -> str:
        """``"A"``: 期限の中で止まる。``"B"``: 保証しない（supervisor の TIMEOUT が fallback）。"""

        return "A" if self.cooperative else "B"


#: 何も主張しない backend（能力を宣言していない backend・duck-typed な test double）
NO_CAPABILITIES = SolverBackendCapabilities()


@dataclass
class SolverResult:
    """ソルバーの実行結果"""
    solver_name: str
    status: SolverStatus
    elapsed_time: float = 0.0
    #: SAT の witness（Issue #161）。契約:
    #:
    #: * canonical witness を作れる backend（`SMTSolver.PROVIDES_CANONICAL_WITNESS`）の
    #:   SAT は、**必ず** script が宣言する scalar 入力の canonical witness を持つ
    #:   （`smt.witness`: 宣言順・辞書式最小、値は sort の Python 型）。solver の履歴や
    #:   最初に見つけた model に依らない。決められなかったときは SAT を返さない
    #:   （`interrupted_result`: 予算切れは TIMEOUT、判定不能・中止は UNKNOWN）。SAT は
    #:   `sat_with_canonical_witness` の手順でだけ確定する（witness の生成の前後で実行の
    #:   中断を確かめる。実行の状態の owner は `smt.execution.ExecutionBudget`）
    #: * 作れない backend の SAT は `None`
    #: * どちらも backend の境界（`enforce_witness_contract`）で強制する。canonical
    #:   provider の witness が無い・形が違う SAT は契約違反として ERROR にし
    #:   （`witness_contract_violation`）、その query は判定しない（自己申告を信じない）
    model: Optional[Dict[str, Any]] = None
    error_message: Optional[str] = None
    raw_output: Optional[str] = None
    #: backend が `SolverResult.model` の契約を破った（canonical provider の witness が
    #: 無い・形が違う SAT）ときの理由。`enforce_witness_contract` だけが設定し、その行の
    #: status は ERROR になる。集約（`smt.aggregation`）は、この行がある query を判定しない
    #: （SAT を主張した backend がいたことを黙って捨てない）。結果 JSON の schema には入れない
    witness_contract_violation: Optional[str] = None
    #: この実行がどう終わったか（`BackendTermination`。結果 JSON の schema には入れない）
    termination: BackendTermination = BackendTermination.COMPLETED
    
    def is_equivalent(self) -> bool:
        """等価かどうか"""
        return self.status == SolverStatus.UNSAT
    
    def json_items(self):
        yield "solver_name", self.solver_name
        # enum の名前は member の `_name_`（`name` の property を呼ばない）
        yield "status", live_values.enum_name(self.status)
        yield "elapsed_time", self.elapsed_time
        yield "model", self.model
        yield "error_message", self.error_message

    def to_dict(self) -> Dict[str, Any]:
        return materialize(self)


class SMTSolver(ABC):
    """SMTソルバーの抽象基底クラス"""

    #: SAT の model が `SolverResult.model` の契約（canonical witness、`smt.witness`）を
    #: 満たすと宣言するか。宣言は `enforce_witness_contract` が結果ごとに検査する（宣言した
    #: backend の witness の無い・形の違う SAT は ERROR、宣言しない backend の model は落とす）。
    #: 宣言する backend は、SAT を `sat_with_canonical_witness` でだけ返す。
    PROVIDES_CANONICAL_WITNESS = False

    #: この backend の時間制御の能力（Issue #106 PR-106-A）。既定は **主張なし**
    #: （non-cooperative: Class B）。主張する backend は実測の根拠と backend の test を持つ。
    CAPABILITIES: ClassVar[SolverBackendCapabilities] = NO_CAPABILITIES

    def __init__(self, timeout: int = 10):
        """
        Args:
            timeout: タイムアウト（秒）
        """
        self.timeout = timeout
        self._is_available: Optional[bool] = None
        self._availability_message: str = ""
    
    @property
    @abstractmethod
    def name(self) -> str:
        """ソルバー名を返す"""
        pass
    
    def set_timeout(self, timeout: int) -> None:
        """
        タイムアウトを動的に設定
        
        Args:
            timeout: タイムアウト（秒）
        
        Note:
            サブクラスでオーバーライドして、ソルバー固有の設定も更新すること
        """
        self.timeout = timeout
    
    @abstractmethod
    def check_availability(self) -> Tuple[bool, str]:
        """
        ソルバーが利用可能かチェック
        
        Returns:
            Tuple[bool, str]: (利用可能か, メッセージ)
        """
        pass
    
    def is_available(self) -> bool:
        """ソルバーが利用可能かどうか"""
        if self._is_available is None:
            self._is_available, self._availability_message = self.check_availability()
        return self._is_available
    
    @abstractmethod
    def check_equivalence_direct(
        self,
        smt_script: str,
        cancellation_token: Optional[Any] = None
    ) -> SolverResult:
        """
        SMT-LIBスクリプトを直接実行
        
        Args:
            smt_script: SMT-LIBスクリプト
            cancellation_token: キャンセルトークン（早期終了用）
        
        Returns:
            SolverResult: 検証結果
        """
        pass
    
    # -- adapter contract（Issue #106 PR-106-A） -------------------------------

    def capabilities(self) -> SolverBackendCapabilities:
        return type(self).CAPABILITIES

    def execute(
        self,
        smt_script: str,
        *,
        timeout_seconds: float,
        not_after: Optional[float] = None,
        cancellation_token: Optional[Any] = None,
    ) -> SolverResult:
        """1 回の実行。``not_after`` は owner が求めた absolute monotonic の終わり（無ければ従来）。

        既定の実装は ``absolute_deadline`` を主張しない backend 用: 期限を秒の timeout に
        直して（`core.deadline.bounded_timeout`）`set_timeout` し、`check_equivalence_direct`
        を呼ぶ。秒に直して 0 になるなら始めない。期限を自分で守る backend は override する。
        """

        return _default_execute(
            self, smt_script, timeout_seconds=timeout_seconds, not_after=not_after,
            cancellation_token=cancellation_token,
        )

    def request_interrupt(self) -> bool:
        """走っている実行を止めるよう求める（別 thread から呼ぶ）。求められたら真。

        既定は何もできない（``interrupt`` を主張しない）。
        """

        return False

    def _create_error_result(self, error_msg: str) -> SolverResult:
        """エラー結果を作成"""
        return SolverResult(
            solver_name=self.name,
            status=SolverStatus.ERROR,
            error_message=error_msg
        )
    
    def _create_timeout_result(self, elapsed: float) -> SolverResult:
        """タイムアウト結果を作成"""
        return SolverResult(
            solver_name=self.name,
            status=SolverStatus.TIMEOUT,
            elapsed_time=elapsed
        )

def enforce_witness_contract(
    result: SolverResult, smt_script: str, *, canonical: bool,
) -> SolverResult:
    """backend の結果を `SolverResult.model` の契約に合わせる（backend の境界で 1 回）。

    * `canonical`（canonical witness を作れると宣言した backend）の SAT は、witness の
      形（`smt.witness.witness_contract_violation`）を検査する。witness が無い・形が
      違うなら契約違反で、SAT を受理せず ERROR にする（反例にも判定にもしない）
    * それ以外の backend の SAT の model は solver の任意の選択なので採らない
      （model 無しの SAT）

    呼ぶのは、backend の結果が model を読む consumer へ渡る境界（runner の `run_single` と
    monolithic の共有 session の `execute`）。`Z3Solver` を直接呼ぶ解析側の箇所は status
    だけを読み、model を使わない。
    """

    if result.status != SolverStatus.SAT:
        return result
    if canonical:
        violation = witness_contract_violation(witness_targets(smt_script), result.model)
        if violation is None:
            return result
        return SolverResult(
            solver_name=result.solver_name,
            status=SolverStatus.ERROR,
            elapsed_time=result.elapsed_time,
            error_message=f"canonical witness contract violated: {violation}",
            raw_output=result.raw_output,
            witness_contract_violation=violation,
        )
    if result.model is None:
        return result
    return SolverResult(
        solver_name=result.solver_name,
        status=result.status,
        elapsed_time=result.elapsed_time,
        model=None,
        error_message="canonical witness unavailable: backend does not provide one",
        raw_output=result.raw_output,
    )


#: 中断・witness 失敗の種類 → 結果の status（全経路で同じ写し方）
_INTERRUPTION_STATUS = {
    CANCELLED: SolverStatus.UNKNOWN,
    BUDGET_EXHAUSTED: SolverStatus.TIMEOUT,
    INCONCLUSIVE: SolverStatus.UNKNOWN,
}


def interrupted_result(
    solver_name: str, kind: str, detail: str, elapsed_time: float,
) -> SolverResult:
    """実行が中断された（または canonical witness を決められなかった）ときの結果。

    明示の中止は UNKNOWN、実行の期限切れは TIMEOUT（初回の check が予算内に終わらな
    かったときと同じ扱い）、witness の探索の判定不能は UNKNOWN。どれも既存の「判定
    できなかった」経路（登録済みの理由付きの不明）へ流れ、反例にも証明にもならない。
    """

    status = _INTERRUPTION_STATUS[kind]
    return SolverResult(
        solver_name=solver_name,
        status=status,
        elapsed_time=elapsed_time,
        error_message=f"{kind}: {detail}",
    )


def witness_failure_result(
    solver_name: str, failure: "WitnessUnavailable", elapsed_time: float,
) -> SolverResult:
    """canonical witness を決められなかった SAT の結果（SAT にはしない）。"""

    return interrupted_result(
        solver_name, failure.kind, f"SAT without canonical witness: {failure.detail}", elapsed_time,
    )


def sat_with_canonical_witness(
    solver_name: str,
    *,
    started: float,
    budget: ExecutionBudget,
    canonicalize: Callable[[], Dict[str, Any]],
) -> SolverResult:
    """初回の check が SAT だった実行を、`SolverResult.model` の契約どおりに確定する。

    canonical witness を作る backend は、SAT をこの手順でだけ返す（backend 固有なのは
    `canonicalize` の中身だけ）。手順:

    1. witness の生成の前に実行の中断を確かめる（初回の check が期限を越えた・その間に
       中止された SAT を、witness を作らずに TIMEOUT / UNKNOWN にする）
    2. `canonicalize()` で canonical witness を作る（探索の問いごとの中断確認は
       backend の session が同じ `budget` で行う）。決められなければ `witness_failure_result`
    3. SAT を確定する直前にもう一度中断を確かめる

    1 と 3 は探索の問いの回数に依らない（問いが 0 回の witness・成分が 0 個の witness でも
    中断をすり抜けない）。`started` は `time.time()` での実行開始（elapsed の起点）。
    """

    stop = budget.interruption()
    if stop is not None:
        return interrupted_result(
            solver_name, stop, "the execution stopped before the canonical witness",
            time.time() - started,
        )
    try:
        model = canonicalize()
    except WitnessUnavailable as failure:
        return witness_failure_result(solver_name, failure, time.time() - started)
    stop = budget.interruption()
    if stop is not None:
        return interrupted_result(
            solver_name, stop, "the execution stopped before the SAT was finalized",
            time.time() - started,
        )
    return SolverResult(
        solver_name=solver_name,
        status=SolverStatus.SAT,
        elapsed_time=time.time() - started,
        model=model,
    )


def not_started_result(solver_name: str, detail: str = "no time left before the analysis deadline") -> SolverResult:
    """期限までの時間が無くて実行しなかった backend の行（TIMEOUT。判定の根拠にならない）。"""

    return SolverResult(
        solver_name=solver_name,
        status=SolverStatus.TIMEOUT,
        elapsed_time=0.0,
        error_message=f"not_started: {detail}",
        termination=BackendTermination.NOT_STARTED,
    )


def result_was_answered(result: SolverResult) -> bool:
    """期限で切られていない行か（自分で返り、TIMEOUT ではない）。"""

    return (
        result.termination is BackendTermination.COMPLETED
        and result.status != SolverStatus.TIMEOUT
    )


def _default_execute(
    backend: Any,
    smt_script: str,
    *,
    timeout_seconds: float,
    not_after: Optional[float],
    cancellation_token: Optional[Any],
) -> SolverResult:
    if not_after is None:
        backend.set_timeout(timeout_seconds)
        return backend.check_equivalence_direct(smt_script, cancellation_token)
    seconds = bounded_timeout(
        timeout_seconds, not_after, TimeUnit.SECONDS, now=time.monotonic(),
    )
    if seconds is None:
        return not_started_result(backend.name)
    backend.set_timeout(seconds)
    return backend.check_equivalence_direct(smt_script, cancellation_token)


def backend_capabilities(backend: Any) -> SolverBackendCapabilities:
    """backend の能力（adapter でない duck-typed な object は主張なし）。"""

    if isinstance(backend, SMTSolver):
        return backend.capabilities()
    return NO_CAPABILITIES


def execute_on_backend(
    backend: Any,
    smt_script: str,
    *,
    timeout_seconds: float,
    not_after: Optional[float] = None,
    cancellation_token: Optional[Any] = None,
) -> SolverResult:
    """backend 1 つで 1 回実行する（adapter の `execute`。duck-typed な object は既定の手順）。"""

    if isinstance(backend, SMTSolver):
        return backend.execute(
            smt_script, timeout_seconds=timeout_seconds, not_after=not_after,
            cancellation_token=cancellation_token,
        )
    return _default_execute(
        backend, smt_script, timeout_seconds=timeout_seconds, not_after=not_after,
        cancellation_token=cancellation_token,
    )


def request_backend_interrupt(backend: Any) -> bool:
    if isinstance(backend, SMTSolver) and backend.capabilities().interrupt:
        return bool(backend.request_interrupt())
    return False


SolverInterface = SMTSolver  # 後方互換性のためのエイリアス
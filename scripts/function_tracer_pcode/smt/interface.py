# -*- coding: utf-8 -*-
"""SMTソルバーの抽象インターフェース（修正版）"""

from abc import ABC, abstractmethod
from enum import Enum, auto
from typing import Callable, ClassVar, Optional, Dict, Any, Tuple
import dataclasses
from dataclasses import dataclass
import time


# Re-exports kept for callers that import these names from this module.
from typing import List  # noqa: F401
from scripts.function_tracer_pcode.core import live_values
from scripts.function_tracer_pcode.core.deadline import (
    Adoption,
    ExecutionEnd,
    ExecutionFact,
    TimeUnit,
    bounded_timeout,
)
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
    #: 走っていた実行を adapter の停止操作（`SMTSolver.request_stop`）で止めた（待ちの上限の中で返った）
    STOPPED = "stopped"
    #: 待つのをやめた後、止めるよう求めずに（止め方が無いのに）自分で返った。答えは採らない
    RETURNED_LATE = "returned_late"
    #: 走っていた実行を止められなかった（止める手段が無い・求めても返らない）。runner は
    #: その実行が自分で返るまで待つ（process はそれまで終われない: supervisor の TIMEOUT が
    #: 最後の fallback）
    NOT_STOPPABLE = "not_stoppable"


class StopMethod(Enum):
    """走っている実行を外から止める方法（adapter の `request_stop` が実装する）。"""

    #: 止められない（自分で返るのを待つしかない）
    NONE = "none"
    #: in-process の中断要求（z3 の `Context.interrupt` など）。実行は unknown で返る
    INTERRUPT = "interrupt"
    #: 実行の強制終了（外部 process の kill など）
    HARD_STOP = "hard_stop"


@dataclass(frozen=True)
class SolverBackendCapabilities:
    """backend adapter が **実測の根拠をもって** 主張できる時間制御の能力（既定は主張なし）。

    ``native_timeout``    backend 自身が timeout で実行を打ち切る（``timeout_unit`` の単位）
    ``absolute_deadline`` `SMTSolver.execute` が ``not_after``（その実行の absolute monotonic の
                          終わり）を守る
    ``running_stop``      走っている実行を `SMTSolver.request_stop()` で止める方法

    主張しない能力は無いものとして扱う（runner はそれを前提に止め方を選ぶ）。宣言と実装の
    食い違い（止め方を主張して `request_stop` を実装しない等）は class を定義した時点で拒む
    （`SMTSolver.__init_subclass__` → `validate_backend_contract`）。
    """

    native_timeout: bool = False
    timeout_unit: Optional[TimeUnit] = None
    absolute_deadline: bool = False
    running_stop: StopMethod = StopMethod.NONE

    @property
    def cooperative(self) -> bool:
        """期限の中で自分で止まることを保証できるか（Class A / B の区別）。"""

        return self.native_timeout and self.absolute_deadline

    @property
    def stoppable_while_running(self) -> bool:
        """走っている実行を外から止められるか（runner はこのときだけ `request_stop` を呼ぶ）。"""

        return self.running_stop is not StopMethod.NONE

    @property
    def execution_unit(self) -> TimeUnit:
        """実行の窓を求める単位（主張が無ければ既定の実行の手順と同じ秒）。"""

        return self.timeout_unit or TimeUnit.SECONDS

    @property
    def guarantee_class(self) -> str:
        """``"A"``: 期限の中で止まる。``"B"``: 保証しない（supervisor の TIMEOUT が fallback）。"""

        return "A" if self.cooperative else "B"


#: 何も主張しない backend（能力を宣言していない backend・duck-typed な test double）
NO_CAPABILITIES = SolverBackendCapabilities()


#: status ごとに取り得る終了原因（`SolverResult.cause` の検査と `execution_end` の表）
_CAUSES_BY_STATUS = {
    SolverStatus.SAT: frozenset({ExecutionEnd.ANSWERED}),
    SolverStatus.UNSAT: frozenset({ExecutionEnd.ANSWERED}),
    # UNKNOWN の TIME_LIMIT: 時間の上限で止まったが backend が timeout と報告しなかった
    # （z3 の incremental の "canceled"。`ExecutionBudget.unknown_end`）。status は期限なしの
    # 結果の互換のため UNKNOWN のまま
    SolverStatus.UNKNOWN: frozenset({
        ExecutionEnd.INCONCLUSIVE, ExecutionEnd.CANCELLED, ExecutionEnd.TIME_LIMIT,
    }),
    # TIMEOUT の INCONCLUSIVE: z3 の adapter の「経過が設定の 90% 以上なら TIMEOUT」の規則（#209）で
    # TIMEOUT と報告したが、与えた時間は使い切っていない unknown
    SolverStatus.TIMEOUT: frozenset({
        ExecutionEnd.TIME_LIMIT, ExecutionEnd.NOT_STARTED, ExecutionEnd.INCONCLUSIVE,
    }),
    SolverStatus.ERROR: frozenset({ExecutionEnd.FAILED, ExecutionEnd.CONTRACT_VIOLATION}),
}


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
    #: この実行の時間を解析の期限が決めたか（`core.deadline.ExecutionWindow.limited`。runner が
    #: 実行を始める瞬間に求めて付ける。結果 JSON の schema には入れない）
    deadline_limited: bool = False
    #: 観測された終了原因（`core.deadline.ExecutionEnd`）を **status だけでは決まらないときに**
    #: 明示する（中止の UNKNOWN など）。``None`` なら status から決まる（`execution_end` の表）。
    #: status と両立しない値は作った時点で拒む。結果 JSON の schema には入れない
    cause: Optional[ExecutionEnd] = None
    #: 終了原因とは独立に観測した backend の故障（例外の要約）。終了原因が中止などでも故障を
    #: 落とさない（`execution_fact` が `ExecutionFact.failed` に写す）。作るのは
    #: `interrupted_result(failure=...)`（中止の行）だけで、答え（SAT / UNSAT）とは同居しない
    #: （`__post_init__` が拒む）。結果 JSON の schema には入れない
    observed_failure: Optional[str] = None
    #: 採用しなかった答え（backend が返した SAT / UNSAT の status。`without_answer` だけが設定する:
    #: 期限が打ち切った問いの答えと、待つのをやめた後に返った答え。行の status は TIMEOUT）。
    #: 診断用で、判定にも結果 JSON の schema にも入れない
    withheld_status: Optional["SolverStatus"] = None

    def __post_init__(self) -> None:
        """行の状態の契約（作った時点で、`derive_row` で変えた時点でも検査する）。

        * ``cause`` は status と両立する値だけ（`_CAUSES_BY_STATUS`）
        * ``observed_failure``（独立した故障）は答え（SAT / UNSAT）と同居しない。故障を観測した
          実行の答えは信頼できない: 故障を伝える backend は ERROR を返すか、中断の行
          （`interrupted_result(failure=...)`、status は UNKNOWN / TIMEOUT）に載せる。答えに付けると
          採否・集約が故障を見落とす（Issue #106 PR-106-A レビュー 5 巡目）
        * ``witness_contract_violation`` は ERROR の行だけ（`enforce_witness_contract` が作る）
        * ``withheld_status``（採用しなかった答え）は SAT / UNSAT で、行の status は TIMEOUT
        """
        if self.cause is not None:
            if type(self.cause) is not ExecutionEnd:
                raise TypeError("SolverResult.cause must be an ExecutionEnd")
            allowed = _CAUSES_BY_STATUS.get(self.status, frozenset())
            if self.cause not in allowed:
                raise ValueError(
                    f"SolverResult.cause {self.cause.value} contradicts status "
                    f"{live_values.enum_name(self.status)}"
                )
        answered = self.status in (SolverStatus.SAT, SolverStatus.UNSAT)
        if self.observed_failure is not None and answered:
            raise ValueError("an observed failure cannot accompany a SAT / UNSAT answer")
        if self.witness_contract_violation is not None and self.status != SolverStatus.ERROR:
            raise ValueError("a witness contract violation is reported only by an ERROR row")
        if self.withheld_status is not None and (
            self.withheld_status not in (SolverStatus.SAT, SolverStatus.UNSAT)
            or self.status != SolverStatus.TIMEOUT
        ):
            raise ValueError("a withheld answer is a SAT / UNSAT kept on a TIMEOUT row")
    
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

    def __init_subclass__(cls, **kwargs: Any) -> None:
        super().__init_subclass__(**kwargs)
        validate_backend_contract(cls)

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
        """1 回の実行。``not_after`` は **この実行の** absolute monotonic の終わり（runner が実行を
        始める瞬間に `core.deadline.execution_window` で求めた値。無ければ従来）。

        既定の実装は秒の native timeout の backend 用: 終わりまでを秒の timeout に直して
        （`core.deadline.bounded_timeout`）`set_timeout` し、`check_equivalence_direct` を呼ぶ。
        秒に直して 0 になるなら始めない。別の単位・方法で終わりを守る backend は override する。
        """

        return _default_execute(
            self, smt_script, timeout_seconds=timeout_seconds, not_after=not_after,
            cancellation_token=cancellation_token,
        )

    def request_stop(self) -> bool:
        """走っている実行を止めるよう求める（別 thread から呼ぶ）。求めたら真。

        ``CAPABILITIES.running_stop`` が `StopMethod.NONE` 以外の backend は必ず実装する
        （実装しないと class の定義が拒まれる）。既定は何もできない。
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
        return derive_row(
            result,
            status=SolverStatus.ERROR,
            model=None,
            error_message=f"canonical witness contract violated: {violation}",
            witness_contract_violation=violation,
            cause=ExecutionEnd.CONTRACT_VIOLATION,
        )
    if result.model is None:
        return result
    return derive_row(
        result,
        model=None,
        error_message="canonical witness unavailable: backend does not provide one",
    )


#: 中断・witness 失敗の種類 → 結果の status と終了原因（全経路で同じ写し方）
_INTERRUPTION_STATUS = {
    CANCELLED: (SolverStatus.UNKNOWN, ExecutionEnd.CANCELLED),
    BUDGET_EXHAUSTED: (SolverStatus.TIMEOUT, ExecutionEnd.TIME_LIMIT),
    INCONCLUSIVE: (SolverStatus.UNKNOWN, ExecutionEnd.INCONCLUSIVE),
}


def interrupted_result(
    solver_name: str, kind: str, detail: str, elapsed_time: float,
    *, cause: Optional[ExecutionEnd] = None, failure: Optional[str] = None,
) -> SolverResult:
    """実行が中断された（または canonical witness を決められなかった）ときの結果。

    明示の中止は UNKNOWN、実行の期限切れは TIMEOUT（初回の check が予算内に終わらな
    かったときと同じ扱い）、witness の探索の判定不能は UNKNOWN。どれも既存の「判定
    できなかった」経路（登録済みの理由付きの不明）へ流れ、反例にも証明にもならない。
    """

    status, default_cause = _INTERRUPTION_STATUS[kind]
    return SolverResult(
        solver_name=solver_name,
        status=status,
        elapsed_time=elapsed_time,
        error_message=f"{kind}: {detail}",
        cause=default_cause if cause is None else cause,
        observed_failure=failure,
    )


def witness_failure_result(
    solver_name: str, failure: "WitnessUnavailable", elapsed_time: float,
) -> SolverResult:
    """canonical witness を決められなかった SAT の結果（SAT にはしない）。"""

    return interrupted_result(
        solver_name, failure.kind, f"SAT without canonical witness: {failure.detail}", elapsed_time,
        cause=failure.end,
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
        deadline_limited=True,
        cause=ExecutionEnd.NOT_STARTED,
    )


def execution_end(result: SolverResult) -> ExecutionEnd:
    """**solver の行 → 観測された終了原因の唯一の写像**（backend に依らない語彙へ）。

    明示の `SolverResult.cause` があればそれ（status との両立は作った時点で検査済み）。無ければ
    status から: SAT / UNSAT → ANSWERED、UNKNOWN → INCONCLUSIVE、TIMEOUT → TIME_LIMIT
    （始めなかった行は NOT_STARTED）、ERROR → FAILED（witness の契約違反は
    CONTRACT_VIOLATION）。中止の UNKNOWN は status では区別できないので、作る側
    （`interrupted_result`）が明示する。error_message の文字列は読まない。
    """

    cause = getattr(result, "cause", None)
    if cause is not None:
        return cause
    status = result.status
    if status in (SolverStatus.SAT, SolverStatus.UNSAT):
        return ExecutionEnd.ANSWERED
    if status == SolverStatus.UNKNOWN:
        return ExecutionEnd.INCONCLUSIVE
    if status == SolverStatus.TIMEOUT:
        if getattr(result, "termination", None) is BackendTermination.NOT_STARTED:
            return ExecutionEnd.NOT_STARTED
        return ExecutionEnd.TIME_LIMIT
    if getattr(result, "witness_contract_violation", None) is not None:
        return ExecutionEnd.CONTRACT_VIOLATION
    return ExecutionEnd.FAILED


def execution_fact(result: SolverResult) -> ExecutionFact:
    """solver の行を `settle` が読む事実へ写す（終了原因 + 期限が上限を決めたか）。"""

    return ExecutionFact(
        end=execution_end(result),
        limited=bool(getattr(result, "deadline_limited", False)),
        failed=getattr(result, "observed_failure", None) is not None,
    )


def apply_adoption(results: Any, adoption: Adoption) -> List[SolverResult]:
    """**問いの採否を行へ適用する唯一の場所**（Issue #106 PR-106-A レビュー 4 巡目）。

    ``adoption`` は `core.deadline.DeadlineQuery.adoption`。WITHHELD（解析の期限がこの問いを
    打ち切った）なら、答えの行（SAT / UNSAT。終了原因 ANSWERED）を、採用できない行（TIMEOUT・
    期限が時間を決めた・反例なし）に置き換え、返した status を `withheld_status` に残す。故障
    （ERROR・witness の契約違反）・判定不能・中止・未開始の行はそのまま残す（故障を消さない）。

    runner・共有 session の結果は、集約（`smt.aggregation`）・execution authority の query
    receipt・proof の cache・producer の再集約のどれもが行を読むので、行から答えを外す（結果の
    判定だけを None にしても、行の UNSAT から採用し直せてしまう）。
    """

    rows = list(results)
    if adoption is Adoption.ADOPTABLE:
        return rows
    return [_withheld(row) if execution_end(row) is ExecutionEnd.ANSWERED else row for row in rows]


def _withheld(row: SolverResult) -> SolverResult:
    return without_answer(
        row,
        detail=(
            f"answer withheld: the analysis deadline cut this query "
            f"(the backend returned {live_values.enum_name(row.status)})"
        ),
        deadline_limited=True,
    )


def derive_row(row: SolverResult, **changes: Any) -> SolverResult:
    """**行を変える唯一の手段**（Issue #106 PR-106-A レビュー 5 巡目）。

    変える field だけを指定し、他の field（故障・契約違反・終わり方・期限の事実・診断）は
    すべて元の行から引き継ぐ（`dataclasses.replace`。行の状態の契約は新しい行の
    `__post_init__` が検査する）。field を 1 つずつ写して作り直すと、後から足した field
    （`observed_failure` など）を黙って落とす。
    """

    return dataclasses.replace(row, **changes)


def without_answer(
    row: SolverResult,
    *,
    detail: str,
    deadline_limited: bool,
    termination: Optional[BackendTermination] = None,
    elapsed_time: Optional[float] = None,
) -> SolverResult:
    """採用しない行（TIMEOUT・時間の上限・反例なし）。**答えを外す唯一の規則**。

    答え（SAT / UNSAT）だった行は、その status を `withheld_status` に残し、model と
    raw_output（答えの中身）を外す。故障は運ばない（故障のある行はこの関数に渡さない:
    呼び出し側が先に故障の行として残す）。期限が打ち切った問いの答え（`apply_adoption`）と、
    待つのをやめた実行が後から返した行（`smt.parallel.collected_after_stop`）が使う。
    """

    answered = execution_end(row) is ExecutionEnd.ANSWERED
    return derive_row(
        row,
        status=SolverStatus.TIMEOUT,
        cause=ExecutionEnd.TIME_LIMIT,
        model=None,
        raw_output=None,
        error_message=detail,
        deadline_limited=deadline_limited,
        termination=row.termination if termination is None else termination,
        elapsed_time=row.elapsed_time if elapsed_time is None else elapsed_time,
        withheld_status=row.status if answered else None,
    )


def validate_backend_contract(backend_class: type) -> None:
    """能力の宣言と adapter の実装が食い違っていないか（class の定義時に 1 回）。

    * 止め方を主張するなら `request_stop` を実装する
    * ``absolute_deadline`` を主張するなら ``native_timeout`` と単位を主張する
    * 既定の実行の手順（秒）のまま秒以外の単位を主張しない
    """

    capabilities = getattr(backend_class, "CAPABILITIES", NO_CAPABILITIES)
    if type(capabilities) is not SolverBackendCapabilities:
        raise TypeError(f"{backend_class.__name__}.CAPABILITIES must be SolverBackendCapabilities")
    if capabilities.stoppable_while_running and backend_class.request_stop is SMTSolver.request_stop:
        raise TypeError(
            f"{backend_class.__name__} claims {capabilities.running_stop.value} but does not "
            "implement request_stop"
        )
    if capabilities.absolute_deadline and not (capabilities.native_timeout and capabilities.timeout_unit):
        raise TypeError(
            f"{backend_class.__name__} claims absolute_deadline without a native timeout and its unit"
        )
    if capabilities.native_timeout and capabilities.timeout_unit is None:
        raise TypeError(f"{backend_class.__name__} claims native_timeout without its unit")
    if (
        capabilities.timeout_unit not in (None, TimeUnit.SECONDS)
        and backend_class.execute is SMTSolver.execute
    ):
        raise TypeError(
            f"{backend_class.__name__} claims {capabilities.timeout_unit.value} but uses the "
            "default whole-second execute"
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


def request_backend_stop(backend: Any) -> bool:
    """走っている実行を止めるよう adapter に求める（止め方を主張する backend だけ）。"""

    if isinstance(backend, SMTSolver) and backend.capabilities().stoppable_while_running:
        return bool(backend.request_stop())
    return False


SolverInterface = SMTSolver  # 後方互換性のためのエイリアス
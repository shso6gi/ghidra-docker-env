# -*- coding: utf-8 -*-
"""SMTソルバーの抽象インターフェース（修正版）"""

from abc import ABC, abstractmethod
from enum import Enum, auto
from typing import Optional, Dict, Any, Tuple
from dataclasses import dataclass


# Re-exports kept for callers that import these names from this module.
from typing import List  # noqa: F401
from scripts.function_tracer_pcode.core import live_values
from scripts.function_tracer_pcode.core.json_encoding import materialize
from scripts.function_tracer_pcode.smt.witness import (
    BUDGET_EXHAUSTED,
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
    #:   （`witness_failure_result`: 予算切れは TIMEOUT、判定不能・中止は UNKNOWN）
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
    #: 宣言する backend は、witness を決められない SAT を `witness_failure_result` で返す。
    PROVIDES_CANONICAL_WITNESS = False

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


def witness_failure_result(
    solver_name: str, failure: "WitnessUnavailable", elapsed_time: float,
) -> SolverResult:
    """canonical witness を決められなかった SAT の結果（SAT にはしない）。

    実行の時間予算を使い切ったなら TIMEOUT（初回の check が予算内に終わらなかった
    ときと同じ扱い）、探索の問いが判定不能・実行が中止されたなら UNKNOWN。どちらも
    既存の「判定できなかった」経路（登録済みの理由付きの不明）へ流れ、反例にも
    証明にもならない。
    """

    status = (
        SolverStatus.TIMEOUT if failure.kind == BUDGET_EXHAUSTED else SolverStatus.UNKNOWN
    )
    return SolverResult(
        solver_name=solver_name,
        status=status,
        elapsed_time=elapsed_time,
        error_message=f"SAT without canonical witness: {failure}",
    )


SolverInterface = SMTSolver  # 後方互換性のためのエイリアス
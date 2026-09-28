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
    #: SAT の witness。script が宣言する scalar 入力の canonical な値（宣言順・unsigned の
    #: 辞書式最小、`smt.witness`）で、solver の履歴や最初に見つけた model に依らない。
    #: 決められなかった SAT は `None`（replay は反例として受け入れない）。
    model: Optional[Dict[str, Any]] = None
    error_message: Optional[str] = None
    raw_output: Optional[str] = None
    
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

    #: SAT の model が `SolverResult.model` の契約（canonical な witness、`smt.witness`）を
    #: 満たすか。満たさない backend の SAT の model は runner が採らない（model 無しの SAT）。
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

SolverInterface = SMTSolver  # 後方互換性のためのエイリアス
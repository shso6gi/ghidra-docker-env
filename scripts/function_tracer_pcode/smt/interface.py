# -*- coding: utf-8 -*-
"""SMTソルバーの抽象インターフェース（修正版）"""

from abc import ABC, abstractmethod
from enum import Enum, auto
from typing import Optional, Dict, Any, List, Tuple
from dataclasses import dataclass, field


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
    model: Optional[Dict[str, Any]] = None  # 反例（SATの場合）
    error_message: Optional[str] = None
    raw_output: Optional[str] = None
    
    def is_equivalent(self) -> bool:
        """等価かどうか"""
        return self.status == SolverStatus.UNSAT
    
    def has_counterexample(self) -> bool:
        """反例があるか"""
        return self.status == SolverStatus.SAT and self.model is not None
    
    def to_dict(self) -> Dict[str, Any]:
        return {
            "solver_name": self.solver_name,
            "status": self.status.name,
            "elapsed_time": self.elapsed_time,
            "model": self.model,
            "error_message": self.error_message,
        }


class SMTSolver(ABC):
    """SMTソルバーの抽象基底クラス"""
    
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
    
    def check_equivalence(
        self,
        smt_script: str,
        return_var1: str,
        return_var2: str
    ) -> SolverResult:
        """
        2つのreturn値の等価性を検証（後方互換性のため）
        """
        return self.check_equivalence_direct(smt_script)
    
    @abstractmethod
    def get_model(self) -> Optional[Dict[str, Any]]:
        """反例（モデル）を取得"""
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
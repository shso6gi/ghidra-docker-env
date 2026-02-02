# -*- coding: utf-8 -*-
# smt/timeout_handler.py
"""タイムアウトハンドラー"""

import signal
import threading
import sys
from typing import Optional, Callable, TypeVar, Any
from functools import wraps
from dataclasses import dataclass

T = TypeVar('T')


class TimeoutError(Exception):
    """タイムアウト例外"""
    pass


@dataclass
class TimeoutResult:
    """タイムアウト実行の結果"""
    success: bool
    result: Any = None
    error: Optional[Exception] = None
    timed_out: bool = False


def _is_main_thread() -> bool:
    """メインスレッドかどうかを判定"""
    return threading.current_thread() is threading.main_thread()


def _signal_available() -> bool:
    """シグナルベースのタイムアウトが使用可能か"""
    return hasattr(signal, 'SIGALRM') and _is_main_thread()


class TimeoutHandler:
    """
    タイムアウトを強制するハンドラー
    
    Unix系でメインスレッドの場合: シグナルベース（確実に中断）
    それ以外: スレッドベース（協調的中断）
    """
    
    def __init__(self, timeout_seconds: int, debug: bool = False):
        self.timeout = timeout_seconds
        self.debug = debug
        self._use_signal = _signal_available()
        self._timer: Optional[threading.Timer] = None
        self._timed_out = False
        self._original_handler = None
    
    def _debug_print(self, msg: str):
        if self.debug:
            print(f"[TimeoutHandler] {msg}", flush=True)
    
    def _signal_handler(self, signum, frame):
        """シグナルハンドラー（SIGALRM）"""
        self._timed_out = True
        self._debug_print(f"SIGALRM received - raising TimeoutError")
        raise TimeoutError(f"Operation timed out after {self.timeout} seconds")
    
    def __enter__(self):
        self._timed_out = False
        
        if self._use_signal:
            self._debug_print(f"Using signal-based timeout ({self.timeout}s)")
            self._original_handler = signal.signal(signal.SIGALRM, self._signal_handler)
            signal.alarm(self.timeout)
        else:
            self._debug_print(f"Signal not available (not main thread or not Unix)")
        
        return self
    
    def __exit__(self, exc_type, exc_val, exc_tb):
        if self._use_signal:
            signal.alarm(0)  # アラームをキャンセル
            if self._original_handler is not None:
                signal.signal(signal.SIGALRM, self._original_handler)
        
        if self._timer:
            self._timer.cancel()
            self._timer = None
        
        # TimeoutError は伝播させる
        return False
    
    def is_timed_out(self) -> bool:
        return self._timed_out


def run_with_timeout(
    func: Callable[[], T],
    timeout_seconds: int,
    debug: bool = False
) -> TimeoutResult:
    """
    関数をタイムアウト付きで実行
    
    Args:
        func: 実行する関数
        timeout_seconds: タイムアウト秒数
        debug: デバッグモード
    
    Returns:
        TimeoutResult: 実行結果
    """
    if _signal_available():
        # シグナルベース
        try:
            with TimeoutHandler(timeout_seconds, debug):
                result = func()
                return TimeoutResult(success=True, result=result)
        except TimeoutError as e:
            return TimeoutResult(success=False, timed_out=True, error=e)
        except Exception as e:
            return TimeoutResult(success=False, error=e)
    else:
        # スレッドベース（フォールバック）
        return _run_with_thread_timeout(func, timeout_seconds, debug)


def _run_with_thread_timeout(
    func: Callable[[], T],
    timeout_seconds: int,
    debug: bool = False
) -> TimeoutResult:
    """スレッドベースのタイムアウト実行"""
    result_container: dict = {'result': None, 'error': None, 'completed': False}
    
    def wrapper():
        try:
            result_container['result'] = func()
            result_container['completed'] = True
        except Exception as e:
            result_container['error'] = e
            result_container['completed'] = True
    
    thread = threading.Thread(target=wrapper, daemon=True)
    thread.start()
    thread.join(timeout=timeout_seconds)
    
    if thread.is_alive():
        if debug:
            print(f"[TimeoutHandler] Thread still alive after {timeout_seconds}s", flush=True)
        return TimeoutResult(
            success=False,
            timed_out=True,
            error=TimeoutError(f"Operation timed out after {timeout_seconds} seconds")
        )
    
    if result_container['error']:
        return TimeoutResult(success=False, error=result_container['error'])
    
    return TimeoutResult(success=True, result=result_container['result'])
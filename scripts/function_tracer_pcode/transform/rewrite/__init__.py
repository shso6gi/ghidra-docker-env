# -*- coding: utf-8 -*-
"""式変換・リライトサブモジュール"""

from .engine import ExpressionRewriter, rewrite_analysis_returns
from .magic_division import (
    MagicDivisionCalculator,
    MagicConstants,
    is_power_of_two,
    log2_exact,
)

__all__ = [
    'ExpressionRewriter',
    'rewrite_analysis_returns',
    'MagicDivisionCalculator',
    'MagicConstants',
    'is_power_of_two',
    'log2_exact',
]
# -*- coding: utf-8 -*-
"""式リライトルール

このパッケージには、SMTソルバーの負荷を軽減するための
各種リライトルールが含まれています。

ルール分類:
- base: 基底クラスとデータ構造
- modulo: 剰余演算の正規化
- division: 除算の最適化（magic number変換、power-of-two最適化）
- simplification: 式の簡約
- normalization: 構文の正規化（可換演算のソート、型統一）
"""

from .base import RewriteResult, RewriteRule
from .modulo import ModuloExpansionRule, ModuloToExpansionRule
from .division import (
    DivByConstantRuleBase,
    SignedDivBy3Rule,
    UnsignedDivBy3Rule,
    DivByPowerOfTwoUnsignedRule,
    DivByPowerOfTwoSignedRule,
    RemByPowerOfTwoUnsignedRule,
    RemByPowerOfTwoSignedRule,
)
from .simplification import DivSimplificationRule
from .normalization import (
    CommutativeNormalizationRule,
    ShiftConstantNormalizationRule,
)

__all__ = [
    # Base
    'RewriteResult',
    'RewriteRule',
    # Modulo
    'ModuloExpansionRule',
    'ModuloToExpansionRule',
    # Division
    'DivByConstantRuleBase',
    'SignedDivBy3Rule',
    'UnsignedDivBy3Rule',
    'DivByPowerOfTwoUnsignedRule',
    'DivByPowerOfTwoSignedRule',
    'RemByPowerOfTwoUnsignedRule',
    'RemByPowerOfTwoSignedRule',
    # Simplification
    'DivSimplificationRule',
    # Normalization
    'CommutativeNormalizationRule',
    'ShiftConstantNormalizationRule',
]
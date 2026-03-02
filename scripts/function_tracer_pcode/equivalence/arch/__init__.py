# -*- coding: utf-8 -*-
"""アーキテクチャ検出・ABI処理サブパッケージ"""

from .detector import ArchitectureDetector
from .mips64 import MIPS64Handler

__all__ = [
    "ArchitectureDetector",
    "MIPS64Handler",
]
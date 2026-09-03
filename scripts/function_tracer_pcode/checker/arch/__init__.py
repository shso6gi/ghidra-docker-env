# -*- coding: utf-8 -*-
"""アーキテクチャ検出・ABI処理サブパッケージ"""

from scripts.function_tracer_pcode.checker.arch.detector import ArchitectureDetector
from scripts.function_tracer_pcode.checker.arch.mips64 import MIPS64Handler

__all__ = [
    "ArchitectureDetector",
    "MIPS64Handler",
]
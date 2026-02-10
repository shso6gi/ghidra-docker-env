# -*- coding: utf-8 -*-
"""設定ファイル"""

import os

# Ghidra内で実行されているかどうかを検出
try:
    from ghidra.program.model.listing import Program # type: ignore[import]
    IN_GHIDRA = True
except ImportError:
    IN_GHIDRA = False

# PyGhidra用設定
GHIDRA_INSTALL_DIR = os.environ.get(
    "GHIDRA_INSTALL_DIR",
    "/opt/ghidra/"
)

# デフォルトの解析対象関数
TARGET_FUNCTIONS = ["add", "subtract", "multiply", "divide", "modulo", "combined_arithmetic"]
# TARGET_FUNCTIONS = ["bitwise_and", "bitwise_or", "bitwise_xor", "bitwise_not", "left_shift", "right_shift_logical", "right_shift_arithmetic", "xor_shift", "extract_bits", "flip_bits"]

# デフォルトの出力ファイル
OUTPUT_FILE = "/mnt/nas/research/highpcode/cate2_branch_return_trace_output.txt"

# 出力形式: "text", "json", "smt", "detailed"
OUTPUT_FORMAT = "text"

# トレースの最大深度（無限ループ防止）
MAX_TRACE_DEPTH = 100

# デバッグモード
DEBUG_MODE = False  # Trueにするとデバッグ出力が有効になる
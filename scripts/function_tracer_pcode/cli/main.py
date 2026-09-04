# -*- coding: utf-8 -*-
#!/usr/bin/env python3
#@category Analysis
#@author ReturnTracer
#@runtime PyGhidra
"""Return Tracer CLI entrypoint."""

from scripts.function_tracer_pcode.config import IN_GHIDRA
from scripts.function_tracer_pcode.cli.args import parse_arguments
from scripts.function_tracer_pcode.cli.commands.analyze import (
    analyze_and_output,
    get_target_functions,
    list_all_functions,
)
from scripts.function_tracer_pcode.cli.commands.equivalence import run_equivalence_check
from scripts.function_tracer_pcode.ghidra.ghidra_runtime import run_ghidra_mode
from scripts.function_tracer_pcode.ghidra.pyghidra_runtime import run_pyghidra_mode

__all__ = [
    "analyze_and_output",
    "get_target_functions",
    "list_all_functions",
    "parse_arguments",
    "run_equivalence_check",
    "run_ghidra_mode",
    "run_pyghidra_mode",
    "main",
]


def _line_buffer_stdio() -> None:
    """ログへリダイレクトされた stdout/stderr を行バッファにする（Issue #14）。

    ブロックバッファのままだと、ペアプロセスが wall-clock timeout で SIGTERM
    される際に未 flush の進捗（ヘッダや解析ログ）が失われ、JVM のバナーしか
    残らない「出力ゼロ」のログになる。
    """
    import sys

    for stream in (sys.stdout, sys.stderr):
        reconfigure = getattr(stream, "reconfigure", None)
        if reconfigure is None:
            continue
        try:
            if not stream.isatty():
                reconfigure(line_buffering=True)
        except Exception:
            continue


def main():
    """メインエントリーポイント。"""
    if IN_GHIDRA:
        run_ghidra_mode()
        return

    _line_buffer_stdio()
    args = parse_arguments()
    run_pyghidra_mode(args)


if __name__ == "__main__":
    main()

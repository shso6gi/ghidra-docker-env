# -*- coding: utf-8 -*-
#!/usr/bin/env python3
#@category Analysis
#@author ReturnTracer
#@runtime PyGhidra
"""Return Tracer CLI entrypoint."""

from ..config import IN_GHIDRA
from .args import parse_arguments
from .commands.analyze import analyze_and_output, get_target_functions, list_all_functions
from .commands.equivalence import run_equivalence_check
from .runtime.ghidra import run_ghidra_mode
from .runtime.pyghidra import run_pyghidra_mode

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


def main():
    """メインエントリーポイント。"""
    if IN_GHIDRA:
        run_ghidra_mode()
        return

    args = parse_arguments()
    run_pyghidra_mode(args)


if __name__ == "__main__":
    main()

# -*- coding: utf-8 -*-
"""CLI package boundary.

Internal responsibilities are split across:
- ``cli.args`` for parser construction
- ``cli.commands`` for analysis / equivalence execution
- ``cli.runtime`` for Ghidra vs PyGhidra entry helpers

We intentionally avoid re-exporting ``main`` here because the submodule name
and attribute name would collide during import.
"""

__all__ = []

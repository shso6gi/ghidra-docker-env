#!/usr/bin/env bash
# Recreate the repo-local host Python environment used for non-container runs.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"

PYTHON_BIN="${PYTHON_BIN:-python3}"
VENV_DIR="${HOST_PYGHIDRA_VENV:-$REPO_ROOT/.venv-pyghidra}"
USE_SYSTEM_SITE="${HOST_VENV_SYSTEM_SITE_PACKAGES:-1}"

if ! command -v "$PYTHON_BIN" >/dev/null 2>&1; then
    echo "Error: PYTHON_BIN was not found: $PYTHON_BIN" >&2
    exit 1
fi

VENV_ARGS=()
if [[ "$USE_SYSTEM_SITE" != "0" ]]; then
    VENV_ARGS+=(--system-site-packages)
fi

if [[ ! -x "$VENV_DIR/bin/python" ]]; then
    "$PYTHON_BIN" -m venv "${VENV_ARGS[@]}" "$VENV_DIR"
fi

"$VENV_DIR/bin/python" -m pip install --upgrade pip
"$VENV_DIR/bin/python" -m pip install -r "$REPO_ROOT/requirements-test.txt"

if [[ -e "$REPO_ROOT/.venv" && ! -L "$REPO_ROOT/.venv" ]]; then
    echo "Warning: $REPO_ROOT/.venv exists and is not a symlink; leaving it unchanged." >&2
elif [[ "$VENV_DIR" == "$REPO_ROOT/.venv-pyghidra" ]]; then
    ln -sfn .venv-pyghidra "$REPO_ROOT/.venv"
fi

"$VENV_DIR/bin/python" - <<'PY'
import shutil

import pyghidra  # noqa: F401
import z3  # noqa: F401

from scripts.function_tracer_pcode.config.settings import GHIDRA_INSTALL_DIR, JAVA_HOME

print("Python PyGhidra environment: ok")
print(f"GHIDRA_INSTALL_DIR={GHIDRA_INSTALL_DIR}")
print(f"JAVA_HOME={JAVA_HOME}")
if not GHIDRA_INSTALL_DIR:
    print("Warning: Ghidra was not discovered; set GHIDRA_INSTALL_DIR or install .local-ghidra-extract/ghidra_12.0.1_PUBLIC.")
if not JAVA_HOME:
    print("Warning: Java was not discovered; set JAVA_HOME or install .local-jdk.")
if shutil.which("z3") is None:
    print("Warning: z3 CLI is not on PATH; Python z3 is installed, but CLI-based tests may skip.")
PY

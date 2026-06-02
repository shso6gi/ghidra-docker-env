#!/usr/bin/env bash
# Remove ignored local outputs after they are no longer needed.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"

CONFIRM="${CLEAN_LOCAL_GENERATED_CONFIRM:-0}"
INCLUDE_UNUSED_RUNTIME="${CLEAN_UNUSED_HOST_RUNTIME:-1}"
INCLUDE_REQUIRED_HOST_RUNTIME="${CLEAN_REQUIRED_HOST_RUNTIME:-0}"

paths=(
    "$REPO_ROOT/logs"
    "$REPO_ROOT/tmp"
    "$REPO_ROOT/output"
    "$REPO_ROOT/artifacts/baselines/observed-v0@0a53352/raw/logs"
)

if [[ "$INCLUDE_UNUSED_RUNTIME" == "1" ]]; then
    paths+=(
        "$REPO_ROOT/.local-ghidra"
    )
fi

if [[ "$INCLUDE_REQUIRED_HOST_RUNTIME" == "1" ]]; then
    paths+=(
        "$REPO_ROOT/.venv"
        "$REPO_ROOT/.venv-pyghidra"
        "$REPO_ROOT/.local-ghidra-extract"
        "$REPO_ROOT/.local-jdk"
    )
fi

echo "Local generated paths:"
for path in "${paths[@]}"; do
    if [[ -e "$path" || -L "$path" ]]; then
        du -sh "$path" 2>/dev/null || printf 'exists\t%s\n' "$path"
    fi
done

if [[ "$CONFIRM" != "1" ]]; then
    echo ""
    echo "Dry run only. Set CLEAN_LOCAL_GENERATED_CONFIRM=1 to delete these paths."
    echo "By default this includes only generated outputs and the unused .local-ghidra cache."
    echo "Set CLEAN_REQUIRED_HOST_RUNTIME=1 as well to remove host venv/Ghidra/JDK runtime caches."
    exit 0
fi

for path in "${paths[@]}"; do
    if [[ -e "$path" || -L "$path" ]]; then
        rm -rf "$path"
    fi
done

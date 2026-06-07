#!/usr/bin/env bash
# Validate frozen Phase 1 concrete manifests without regenerating baseline artifacts.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

PYTHON_BIN="${PYTHON_BIN:-./.venv-pyghidra/bin/python}"
if [[ ! -x "$PYTHON_BIN" ]]; then
  PYTHON_BIN="${PYTHON_FALLBACK_BIN:-python3}"
fi

BASELINE_ROOT="${BASELINE_ROOT:-$SCRIPT_DIR/artifacts/baselines/observed-v0@0a53352}"
PHASE1_DIR="${PHASE1_DIR:-$BASELINE_ROOT/phase1}"
BASELINE_RAW_DIR="${BASELINE_RAW_DIR:-$BASELINE_ROOT/raw}"
OUTPUT_DIR="${OUTPUT_DIR:-$SCRIPT_DIR/logs/equivalence_all/phase1_concrete_manifest_gate}"

"$PYTHON_BIN" -m scripts.function_tracer_pcode.validation.phase1_concrete_manifest_gate \
  --phase1-dir "$PHASE1_DIR" \
  --baseline-raw-dir "$BASELINE_RAW_DIR" \
  --output-dir "$OUTPUT_DIR" \
  --require-ready

echo ""
echo "Phase 1 concrete manifest gate finished."
echo "Output directory: $OUTPUT_DIR"

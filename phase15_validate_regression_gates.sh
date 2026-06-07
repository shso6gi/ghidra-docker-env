#!/usr/bin/env bash
# Validate Phase 1.5 pre-semantic-fix regression gates from existing logs.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

PYTHON_BIN="${PYTHON_BIN:-./.venv-pyghidra/bin/python}"
if [[ ! -x "$PYTHON_BIN" ]]; then
  PYTHON_BIN="${PYTHON_FALLBACK_BIN:-python3}"
fi

BASELINE_ROOT="${BASELINE_ROOT:-$SCRIPT_DIR/artifacts/baselines/observed-v0@0a53352}"
BASELINE_RAW_DIR="${BASELINE_RAW_DIR:-$BASELINE_ROOT/raw}"
PHASE1_DIR="${PHASE1_DIR:-$BASELINE_ROOT/phase1}"
FUNCTION_CALL_CURRENT_LOG_ROOT="${FUNCTION_CALL_CURRENT_LOG_ROOT:-$BASELINE_RAW_DIR/logs/function_call}"
LOOP_CURRENT_LOG_ROOT="${LOOP_CURRENT_LOG_ROOT:-$BASELINE_RAW_DIR/logs/loop}"
OUTPUT_DIR="${OUTPUT_DIR:-$SCRIPT_DIR/logs/equivalence_all/phase1_5_regression_gates}"

"$PYTHON_BIN" -m scripts.function_tracer_pcode.validation.phase15_regression_gates \
  --baseline-raw-dir "$BASELINE_RAW_DIR" \
  --phase1-dir "$PHASE1_DIR" \
  --output-dir "$OUTPUT_DIR" \
  --current-log-root "function_call=$FUNCTION_CALL_CURRENT_LOG_ROOT" \
  --current-log-root "loop=$LOOP_CURRENT_LOG_ROOT" \
  --require-ready

echo ""
echo "Phase 1.5 regression gates finished."
echo "Output directory: $OUTPUT_DIR"

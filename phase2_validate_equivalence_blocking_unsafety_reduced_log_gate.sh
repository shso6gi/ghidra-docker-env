#!/usr/bin/env bash
# Validate Phase 2 equivalence_blocking_unsafety expected movement from reduced existing logs.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

PYTHON_BIN="${PYTHON_BIN:-./.venv-pyghidra/bin/python}"
if [[ ! -x "$PYTHON_BIN" ]]; then
  PYTHON_BIN="${PYTHON_FALLBACK_BIN:-python3}"
fi

BASELINE_ROOT="${BASELINE_ROOT:-$SCRIPT_DIR/artifacts/baselines/observed-v0@0a53352}"
PHASE1_DIR="${PHASE1_DIR:-$BASELINE_ROOT/phase1}"
BASELINE_FUNCTION_CALL_LOG_ROOT="${BASELINE_FUNCTION_CALL_LOG_ROOT:-$BASELINE_ROOT/raw/logs/function_call}"
PHASE2_FUNCTION_CALL_LOG_ROOT="${PHASE2_FUNCTION_CALL_LOG_ROOT:-$SCRIPT_DIR/logs/equivalence_all/function_call_test_phase2_gate_reduced_pre_producer}"
OUTPUT_DIR="${OUTPUT_DIR:-$SCRIPT_DIR/logs/equivalence_all/phase2_equivalence_blocking_unsafety_reduced_log_gate}"

"$PYTHON_BIN" -m scripts.function_tracer_pcode.validation.phase2_equivalence_blocking_unsafety \
  --phase1-dir "$PHASE1_DIR" \
  --output-dir "$OUTPUT_DIR" \
  --current-log-root "function_call=$PHASE2_FUNCTION_CALL_LOG_ROOT" \
  --baseline-log-root "function_call=$BASELINE_FUNCTION_CALL_LOG_ROOT" \
  --baseline-match-scope after-pairs \
  --require-ready

echo ""
echo "Phase 2 equivalence_blocking_unsafety reduced log gate finished."
echo "Output directory: $OUTPUT_DIR"

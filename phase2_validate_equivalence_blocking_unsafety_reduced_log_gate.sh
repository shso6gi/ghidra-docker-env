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

if [[ "${PHASE2_GENERATE_REDUCED_PRE_PRODUCER_LOGS:-0}" == "1" ]]; then
  echo "Generating Phase 2 reduced pre-producer logs before validation."
  OUTPUT_BASE_DIR="${OUTPUT_BASE_DIR:-$PHASE2_FUNCTION_CALL_LOG_ROOT}" \
    PARALLEL_JOBS="${PARALLEL_JOBS:-8}" \
    ./phase2_run_function_call_pre_producer_gate_reduced_matrix.sh
fi

echo "Preflight: checking Phase 2 reduced pre-producer logs use the current object-key schema."
preflight_failed=0
required_logs=(
  "$PHASE2_FUNCTION_CALL_LOG_ROOT/fc_apply_indirect/fc_apply_indirect_B10_B11.log"
  "$PHASE2_FUNCTION_CALL_LOG_ROOT/fc_dispatch_indirect/fc_dispatch_indirect_B10_B11.log"
  "$PHASE2_FUNCTION_CALL_LOG_ROOT/fc_recursive_sum/fc_recursive_sum_B10_B14.log"
)
for log_path in "${required_logs[@]}"; do
  if ! reuse_failure="$("$PYTHON_BIN" -m scripts.function_tracer_pcode.validation.log_reuse_gate \
    --log "$log_path" \
    --require-phase2-object-keys 2>&1)"; then
    preflight_failed=1
    echo "Error: stale or incomplete Phase 2 reduced pre-producer log."
    echo "  log: $log_path"
    echo "  failures:"
    while IFS= read -r failure; do
      [[ -z "$failure" ]] && continue
      echo "    - $failure"
    done <<< "$reuse_failure"
  fi
done

if [[ "$preflight_failed" != "0" ]]; then
  echo ""
  echo "The reduced log gate cannot be used as commit acceptance until these logs are regenerated with the current producer."
  echo "Generate them on the analysis host, then copy the logs back:"
  echo "  PARALLEL_JOBS=8 ./phase2_run_function_call_pre_producer_gate_reduced_matrix.sh"
  echo ""
  echo "Or let this wrapper generate them before validation:"
  echo "  PHASE2_GENERATE_REDUCED_PRE_PRODUCER_LOGS=1 ./phase2_validate_equivalence_blocking_unsafety_reduced_log_gate.sh"
  exit 1
fi

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

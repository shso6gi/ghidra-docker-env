#!/usr/bin/env bash
# Build and validate the Phase 0C observed-baseline census gate from frozen raw logs.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

DEFAULT_PYTHON_BIN="python3"
if [[ -x "$SCRIPT_DIR/.venv/bin/python" ]]; then
    DEFAULT_PYTHON_BIN="$SCRIPT_DIR/.venv/bin/python"
fi

PYTHON_BIN="${PYTHON_BIN:-$DEFAULT_PYTHON_BIN}"
BASELINE_ROOT="${BASELINE_ROOT:-$SCRIPT_DIR/artifacts/baselines/observed-v0@0a53352}"
OUTPUT_DIR="${OUTPUT_DIR:-$SCRIPT_DIR/logs/equivalence_all/phase0c_observed_baseline_census_gate}"

mkdir -p "$OUTPUT_DIR"

"$PYTHON_BIN" -m scripts.function_tracer_pcode.validation.phase0c_observed_baseline_census_gate \
    --baseline-raw-dir "$BASELINE_ROOT/raw" \
    --output-dir "$OUTPUT_DIR" \
    --require-ready

echo ""
echo "Phase 0C observed-baseline census gate finished."
echo "Output directory: $OUTPUT_DIR"

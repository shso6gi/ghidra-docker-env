#!/usr/bin/env bash
# Build and validate the Phase 0A observed-baseline raw artifact integrity gate.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

DEFAULT_PYTHON_BIN="python3"
if [[ -x "$SCRIPT_DIR/.venv/bin/python" ]]; then
    DEFAULT_PYTHON_BIN="$SCRIPT_DIR/.venv/bin/python"
fi

PYTHON_BIN="${PYTHON_BIN:-$DEFAULT_PYTHON_BIN}"
BASELINE_ROOT="${BASELINE_ROOT:-$SCRIPT_DIR/artifacts/baselines/observed-v0@0a53352}"
OUTPUT_DIR="${OUTPUT_DIR:-$SCRIPT_DIR/logs/equivalence_all/phase0a_observed_baseline_integrity_gate}"
PHASE0A_VALIDATE_FILE_CONTENT_HASHES="${PHASE0A_VALIDATE_FILE_CONTENT_HASHES:-1}"

mkdir -p "$OUTPUT_DIR"

ARGS=(
    --baseline-raw-dir "$BASELINE_ROOT/raw"
    --output-dir "$OUTPUT_DIR"
    --require-ready
)

if [[ "$PHASE0A_VALIDATE_FILE_CONTENT_HASHES" == "0" ]]; then
    ARGS+=(--skip-file-content-hashes)
fi

"$PYTHON_BIN" -m scripts.function_tracer_pcode.validation.phase0a_observed_baseline_integrity_gate "${ARGS[@]}"

echo ""
echo "Phase 0A observed-baseline integrity gate finished."
echo "Output directory: $OUTPUT_DIR"

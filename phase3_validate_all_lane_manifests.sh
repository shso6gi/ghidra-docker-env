#!/usr/bin/env bash
# Build and validate a lightweight index over the frozen Phase 3 lane manifests.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

DEFAULT_PYTHON_BIN="python3"
if [[ -x "$SCRIPT_DIR/.venv/bin/python" ]]; then
    DEFAULT_PYTHON_BIN="$SCRIPT_DIR/.venv/bin/python"
fi

export PYTHON_BIN="${PYTHON_BIN:-$DEFAULT_PYTHON_BIN}"
BASELINE_ROOT="${BASELINE_ROOT:-$SCRIPT_DIR/artifacts/baselines/observed-v0@0a53352}"
OUTPUT_DIR="${OUTPUT_DIR:-$SCRIPT_DIR/logs/equivalence_all/phase3_lane_index}"
PHASE3_REQUIRE_READY="${PHASE3_REQUIRE_READY:-1}"

mkdir -p "$OUTPUT_DIR"

ARGS=(
    --baseline-root "$BASELINE_ROOT"
    --output-dir "$OUTPUT_DIR"
)

if [[ "$PHASE3_REQUIRE_READY" != "0" ]]; then
    ARGS+=(--require-ready)
fi

"$PYTHON_BIN" -m scripts.function_tracer_pcode.validation.phase3_lane_index "${ARGS[@]}"

echo ""
echo "Phase 3 lane manifest index finished."
echo "Output directory: $OUTPUT_DIR"

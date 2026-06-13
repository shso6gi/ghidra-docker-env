#!/usr/bin/env bash
# Build and validate a lightweight index over generated Phase 3 post-fix gates.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

DEFAULT_PYTHON_BIN="python3"
if [[ -x "$SCRIPT_DIR/.venv/bin/python" ]]; then
    DEFAULT_PYTHON_BIN="$SCRIPT_DIR/.venv/bin/python"
fi

export PYTHON_BIN="${PYTHON_BIN:-$DEFAULT_PYTHON_BIN}"
OUTPUT_DIR="${OUTPUT_DIR:-$SCRIPT_DIR/logs/equivalence_all/phase3_post_fix_gate_index}"
PHASE3_REQUIRE_READY="${PHASE3_REQUIRE_READY:-1}"
PHASE3_PRINT_SUMMARY="${PHASE3_PRINT_SUMMARY:-1}"

mkdir -p "$OUTPUT_DIR"

ARGS=(
    --repo-root "$SCRIPT_DIR"
    --output-dir "$OUTPUT_DIR"
)

if [[ "$PHASE3_REQUIRE_READY" != "0" ]]; then
    ARGS+=(--require-ready)
fi
if [[ "$PHASE3_PRINT_SUMMARY" != "0" ]]; then
    ARGS+=(--print-summary)
fi

"$PYTHON_BIN" -m scripts.function_tracer_pcode.validation.phase3_post_fix_gate_index "${ARGS[@]}"

echo ""
echo "Phase 3 post-fix gate index finished."
echo "Output directory: $OUTPUT_DIR"

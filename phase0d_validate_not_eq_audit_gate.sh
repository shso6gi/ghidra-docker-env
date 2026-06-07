#!/usr/bin/env bash
# Build and validate the Phase 0D NOT_EQ audit gate from frozen artifacts.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

DEFAULT_PYTHON_BIN="python3"
if [[ -x "$SCRIPT_DIR/.venv/bin/python" ]]; then
    DEFAULT_PYTHON_BIN="$SCRIPT_DIR/.venv/bin/python"
fi

PYTHON_BIN="${PYTHON_BIN:-$DEFAULT_PYTHON_BIN}"
BASELINE_ROOT="${BASELINE_ROOT:-$SCRIPT_DIR/artifacts/baselines/observed-v0@0a53352}"
OUTPUT_DIR="${OUTPUT_DIR:-$SCRIPT_DIR/logs/equivalence_all/phase0d_not_eq_audit_gate}"

mkdir -p "$OUTPUT_DIR"

"$PYTHON_BIN" -m scripts.function_tracer_pcode.validation.phase0d_not_eq_audit_gate \
    --baseline-raw-dir "$BASELINE_ROOT/raw" \
    --audit-manifest "$BASELINE_ROOT/audit/not_eq_audit_manifest.json" \
    --oracle-manifest "$BASELINE_ROOT/derived_oracle/oracle_manifest_draft.json" \
    --output-dir "$OUTPUT_DIR" \
    --require-ready

echo ""
echo "Phase 0D NOT_EQ audit gate finished."
echo "Output directory: $OUTPUT_DIR"

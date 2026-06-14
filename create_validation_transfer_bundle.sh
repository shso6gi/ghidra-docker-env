#!/usr/bin/env bash
set -euo pipefail

SOURCE_ROOT="${SOURCE_ROOT:-logs/equivalence_all}"
STDOUT_ROOT="${STDOUT_ROOT:-.}"
OUTPUT="${1:-${VALIDATION_TRANSFER_BUNDLE_OUTPUT:-logs/validation_transfer_bundle.tar.gz}}"
MAX_STDOUT_TAIL_LINES="${MAX_STDOUT_TAIL_LINES:-200}"
MAX_DIRECT_FILE_BYTES="${MAX_DIRECT_FILE_BYTES:-2000000}"

python3 -m scripts.function_tracer_pcode.validation.validation_transfer_bundle \
  --source-root "$SOURCE_ROOT" \
  --stdout-root "$STDOUT_ROOT" \
  --output "$OUTPUT" \
  --max-stdout-tail-lines "$MAX_STDOUT_TAIL_LINES" \
  --max-direct-file-bytes "$MAX_DIRECT_FILE_BYTES"

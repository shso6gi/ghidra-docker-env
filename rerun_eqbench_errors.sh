#!/usr/bin/env bash
# Re-run only ERROR pairs through the production Eq/Neq runners.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

PYTHON_BIN="${PYTHON_BIN:-$SCRIPT_DIR/.venv-pyghidra/bin/python}"
EQ_OUTPUT_BASE_DIR="${EQ_OUTPUT_BASE_DIR:-$SCRIPT_DIR/logs/EqBench/all_eq_matrix_current}"
NEQ_OUTPUT_BASE_DIR="${NEQ_OUTPUT_BASE_DIR:-$SCRIPT_DIR/logs/EqBench/all_neq_same_isa_closure_current}"
ERROR_RERUN_MANIFEST="${ERROR_RERUN_MANIFEST:-$SCRIPT_DIR/logs/EqBench/error_rerun_manifest.tsv}"
PARALLEL_JOBS="${PARALLEL_JOBS:-32}"
EQBENCH_BUILD_POLICY="${EQBENCH_BUILD_POLICY:-PREBUILT_ONLY}"
NEQ_BUILD_POLICY="${NEQ_BUILD_POLICY:-REUSE_OR_COMPILE}"
ERROR_RERUN_RUN_ID="${ERROR_RERUN_RUN_ID:-$(date -u +%Y%m%dT%H%M%SZ)-$$-$RANDOM}"

[[ -x "$PYTHON_BIN" ]] || { echo "Python is not executable: $PYTHON_BIN" >&2; exit 1; }

"$PYTHON_BIN" -m scripts.eqbench.error_rerun_manifest \
    --eq-root "$EQ_OUTPUT_BASE_DIR" \
    --neq-root "$NEQ_OUTPUT_BASE_DIR" \
    --output "$ERROR_RERUN_MANIFEST"

eq_count="$(awk -F '\t' '$1 == "EQ" {count++} END {print count+0}' "$ERROR_RERUN_MANIFEST")"
neq_count="$(awk -F '\t' '$1 == "NEQ" {count++} END {print count+0}' "$ERROR_RERUN_MANIFEST")"
target_count=$((eq_count + neq_count))
(( target_count > 0 )) || { echo "No ERROR logs were found."; exit 0; }

sample_regex() {
    local lane="$1"
    "$PYTHON_BIN" - "$ERROR_RERUN_MANIFEST" "$lane" <<'PY'
import sys
from pathlib import Path
from scripts.eqbench.error_rerun_manifest import read_manifest, sample_filter_regex

path, lane = sys.argv[1:]
print(sample_filter_regex(read_manifest(Path(path)), lane))
PY
}

pair_filter() {
    local lane="$1"
    awk -F '\t' -v lane="$lane" '$1 == lane {print $4}' "$ERROR_RERUN_MANIFEST" \
        | sort -u | paste -sd, -
}

if (( eq_count > 0 )); then
    env \
        OUTPUT_BASE_DIR="$EQ_OUTPUT_BASE_DIR" \
        EQBENCH_RUN_SCOPE=REPRESENTATIVE \
        EQBENCH_BUILD_POLICY="$EQBENCH_BUILD_POLICY" \
        EQBENCH_SAMPLE_FILTER="$(sample_regex EQ)" \
        EQBENCH_PAIR_FILTER="$(pair_filter EQ)" \
        EQBENCH_RERUN_MANIFEST="$ERROR_RERUN_MANIFEST" \
        ERROR_RERUN_RUN_ID="$ERROR_RERUN_RUN_ID" \
        SKIP_COMPLETED_RESULTS=0 \
        PARALLEL_JOBS="$PARALLEL_JOBS" \
        "$SCRIPT_DIR/eqbench_run_all_32jobs.sh"
fi

if (( neq_count > 0 )); then
    env \
        OUTPUT_BASE_DIR="$NEQ_OUTPUT_BASE_DIR" \
        NEQ_RUN_SCOPE=REPRESENTATIVE \
        NEQ_BUILD_POLICY="$NEQ_BUILD_POLICY" \
        NEQ_SAMPLE_FILTER="$(sample_regex NEQ)" \
        NEQ_PAIR_FILTER="$(pair_filter NEQ)" \
        NEQ_RERUN_MANIFEST="$ERROR_RERUN_MANIFEST" \
        ERROR_RERUN_RUN_ID="$ERROR_RERUN_RUN_ID" \
        SKIP_COMPLETED_RESULTS=0 \
        PARALLEL_JOBS="$PARALLEL_JOBS" \
        "$SCRIPT_DIR/neqbench_run_all_32jobs.sh"
fi

"$PYTHON_BIN" -m scripts.eqbench.error_rerun_manifest \
    --eq-root "$EQ_OUTPUT_BASE_DIR" \
    --neq-root "$NEQ_OUTPUT_BASE_DIR" \
    --verify "$ERROR_RERUN_MANIFEST" \
    --run-id "$ERROR_RERUN_RUN_ID"

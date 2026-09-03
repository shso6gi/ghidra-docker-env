#!/usr/bin/env bash
# Run the fixed measurement subset described by
# scripts/function_tracer_pcode/reporting/eqbench_subset.json.
#
# Eq results go to $OUTPUT_BASE_DIR/eq and Neq results to $OUTPUT_BASE_DIR/neq;
# the runner console output of each half is kept in $OUTPUT_BASE_DIR/<half>.log.
# All settings come from the manifest; override individual ones through the
# environment (PARALLEL_JOBS, PAIR_PROCESS_TIMEOUT, EQBENCH_RESOURCE_ADMISSION,
# EQBENCH_BUILD_POLICY). SUBSET_SCOPE=eq|neq|all selects the halves to run.
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
MANIFEST="${SUBSET_MANIFEST:-$SCRIPT_DIR/scripts/function_tracer_pcode/reporting/eqbench_subset.json}"
OUTPUT_BASE_DIR="${OUTPUT_BASE_DIR:-$SCRIPT_DIR/logs/EqBench/subset_current}"
SUBSET_SCOPE="${SUBSET_SCOPE:-all}"

if [[ "$SUBSET_SCOPE" != "eq" && "$SUBSET_SCOPE" != "neq" && "$SUBSET_SCOPE" != "all" ]]; then
    echo "Error: SUBSET_SCOPE must be eq, neq or all" >&2
    exit 1
fi

manifest_value() {
    python3 - "$MANIFEST" "$@" <<'PY'
import json, sys
manifest = json.load(open(sys.argv[1]))
kind, key = sys.argv[2], sys.argv[3]
if kind == "setting":
    print(manifest["run_settings"][key])
elif kind == "sample_filter":
    sources = manifest[key]["sources"]
    if key == "eq":
        # Eq sources are matched against the source file path (.../<sample>.c).
        print("/(" + "|".join(s.replace(".", r"\.") for s in sources) + r")\.c$")
    else:
        # Neq sources are matched against the sample label.
        print("^(" + "|".join(s.replace(".", r"\.") for s in sources) + ")$")
elif kind == "pair_filter":
    print(",".join(manifest[key]["pair_ids"]))
PY
}

export PARALLEL_JOBS="${PARALLEL_JOBS:-$(manifest_value setting PARALLEL_JOBS)}"
export PAIR_PROCESS_TIMEOUT="${PAIR_PROCESS_TIMEOUT:-$(manifest_value setting PAIR_PROCESS_TIMEOUT)}"
export EQBENCH_RESOURCE_ADMISSION="${EQBENCH_RESOURCE_ADMISSION:-$(manifest_value setting EQBENCH_RESOURCE_ADMISSION)}"
export EQBENCH_BUILD_POLICY="${EQBENCH_BUILD_POLICY:-$(manifest_value setting EQBENCH_BUILD_POLICY)}"

mkdir -p "$OUTPUT_BASE_DIR"
OUTPUT_BASE_DIR="$(realpath -m "$OUTPUT_BASE_DIR")"
START_EPOCH="$(date +%s)"
echo "Subset manifest: $MANIFEST"
echo "Output base: $OUTPUT_BASE_DIR"
echo "PARALLEL_JOBS=$PARALLEL_JOBS PAIR_PROCESS_TIMEOUT=$PAIR_PROCESS_TIMEOUT EQBENCH_RESOURCE_ADMISSION=$EQBENCH_RESOURCE_ADMISSION EQBENCH_BUILD_POLICY=$EQBENCH_BUILD_POLICY"

run_half() {
    local half="$1" start ec=0
    start="$(date +%s)"
    if [[ "$half" == "eq" ]]; then
        EQBENCH_RUN_SCOPE=REPRESENTATIVE \
        EQBENCH_SAMPLE_FILTER="$(manifest_value sample_filter eq)" \
        EQBENCH_PAIR_FILTER="$(manifest_value pair_filter eq)" \
        OUTPUT_BASE_DIR="$OUTPUT_BASE_DIR/eq" \
            "$SCRIPT_DIR/eqbench_run_all_32jobs.sh" || ec=$?
    else
        NEQ_RUN_SCOPE=REPRESENTATIVE \
        NEQ_SAMPLE_FILTER="$(manifest_value sample_filter neq)" \
        NEQ_PAIR_FILTER="$(manifest_value pair_filter neq)" \
        OUTPUT_BASE_DIR="$OUTPUT_BASE_DIR/neq" \
            "$SCRIPT_DIR/neqbench_run_all_32jobs.sh" || ec=$?
    fi
    echo "$(( $(date +%s) - start ))" > "$OUTPUT_BASE_DIR/$half.elapsed"
    return "$ec"
}

# Each production runner keeps at most 8 pairs (one function) in flight at a
# time, so the two halves run concurrently (8 + 8 slots <= PARALLEL_JOBS=20)
# and their console output goes to $OUTPUT_BASE_DIR/<half>.log.
status=0
halves=()
[[ "$SUBSET_SCOPE" == "eq" || "$SUBSET_SCOPE" == "all" ]] && halves+=(eq)
[[ "$SUBSET_SCOPE" == "neq" || "$SUBSET_SCOPE" == "all" ]] && halves+=(neq)
declare -A half_pid=()
for half in "${halves[@]}"; do
    run_half "$half" > "$OUTPUT_BASE_DIR/$half.log" 2>&1 &
    half_pid["$half"]=$!
done
for half in "${halves[@]}"; do
    half_status=0
    wait "${half_pid[$half]}" || half_status=$?
    echo "Subset $half elapsed: $(cat "$OUTPUT_BASE_DIR/$half.elapsed")s (exit $half_status, log: $OUTPUT_BASE_DIR/$half.log)"
    (( half_status == 0 )) || status=$half_status
done

ELAPSED=$(( $(date +%s) - START_EPOCH ))
{
    echo "manifest=$MANIFEST"
    echo "manifest_sha256=$(sha256sum "$MANIFEST" | awk '{print $1}')"
    echo "scope=$SUBSET_SCOPE"
    echo "parallel_jobs=$PARALLEL_JOBS"
    echo "pair_process_timeout=$PAIR_PROCESS_TIMEOUT"
    echo "resource_admission=$EQBENCH_RESOURCE_ADMISSION"
    echo "build_policy=$EQBENCH_BUILD_POLICY"
    for half in "${halves[@]}"; do echo "${half}_elapsed_seconds=$(cat "$OUTPUT_BASE_DIR/$half.elapsed")"; done
    echo "elapsed_seconds=$ELAPSED"
    echo "exit_status=$status"
} > "$OUTPUT_BASE_DIR/subset_manifest.txt"
echo "Subset total elapsed: ${ELAPSED}s"
exit "$status"

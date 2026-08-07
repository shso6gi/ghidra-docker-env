#!/usr/bin/env bash
# NeqBench cross-source matrix: 16 new-side builds x 16 old-side builds.

set -euo pipefail
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
cd "$SCRIPT_DIR"
source "$SCRIPT_DIR/scripts/validation_matrix_common.sh"

default_value() {
    local name="$1" value="$2"
    if [[ ! -v "$name" ]]; then printf -v "$name" '%s' "$value"; fi
}
if [[ -x "$SCRIPT_DIR/.venv-pyghidra/bin/python" ]]; then PYTHON_BIN="$SCRIPT_DIR/.venv-pyghidra/bin/python"; else default_value PYTHON_BIN python3; fi
default_value NEQ_ROOT "$SCRIPT_DIR/targets/EqBench/benchmarks"
default_value OUTPUT_BASE_DIR "$SCRIPT_DIR/logs/EqBench/all_neq_matrix_current"
default_value NEQ_RUN_SCOPE FULL_NEQ
default_value NEQ_BUILD_POLICY REUSE_OR_COMPILE
default_value NEQ_SAMPLE_FILTER ""
default_value NEQ_MAX_SAMPLES 0
default_value NEQ_PAIR_FILTER ""
default_value PARALLEL_JOBS 32
default_value EQBENCH_RESOURCE_ADMISSION 1
default_value EQBENCH_CPU_TOKENS "$(getconf _NPROCESSORS_ONLN 2>/dev/null || nproc 2>/dev/null || printf 1)"
default_value EQBENCH_PAIR_CPU_TOKENS 8
default_value EQBENCH_DEBUG 0
default_value SKIP_COMPLETED_RESULTS 1
default_value DRY_RUN 0
default_value EQUIV_TIMEOUT 10
default_value DECOMPILE_TIMEOUT 60
default_value PAIRWISE_TIMEOUT 5
default_value PAIRWISE_TIMEOUT_HARD 30
default_value PAIR_PROCESS_TIMEOUT 600s
default_value PAIR_PROCESS_KILL_AFTER 30s
default_value VALIDATION_SUMMARY_LEVEL compact
if [[ ! -v EQBENCH_TMPDIR ]]; then
    if [[ -d /workspace && -w /workspace ]]; then EQBENCH_TMPDIR=/workspace/tmp; else EQBENCH_TMPDIR="$SCRIPT_DIR/tmp"; fi
fi
default_value EQBENCH_PRIVATE_AUTHORITY_ROOT "$EQBENCH_TMPDIR/eqbench-private-authority-neq"
COMPILE_TEMPLATE="$SCRIPT_DIR/scripts/eqbench/compile_all_arm_mips.sh"
FUNCTION_LISTER="$SCRIPT_DIR/scripts/eqbench/list_c_functions.py"

[[ "$NEQ_RUN_SCOPE" == FULL_NEQ || "$NEQ_RUN_SCOPE" == REPRESENTATIVE ]] || exit 1
[[ "$NEQ_BUILD_POLICY" == REUSE_OR_COMPILE || "$NEQ_BUILD_POLICY" == FRESH_ONLY ]] || exit 1
[[ "$NEQ_MAX_SAMPLES" =~ ^[0-9]+$ && "$PARALLEL_JOBS" =~ ^[1-9][0-9]*$ ]] || exit 1
[[ -f "$COMPILE_TEMPLATE" && -f "$FUNCTION_LISTER" ]] || exit 1
NEQ_ROOT="$(realpath -m "$NEQ_ROOT")"
case "$NEQ_ROOT" in "$SCRIPT_DIR"/*) ;; *) echo "NEQ_ROOT must be inside repository" >&2; exit 1 ;; esac
[[ -d "$NEQ_ROOT" ]] || exit 1
if [[ "$NEQ_RUN_SCOPE" == FULL_NEQ && "$NEQ_MAX_SAMPLES" != 0 ]]; then exit 1; fi
if [[ "$NEQ_RUN_SCOPE" == FULL_NEQ && ( -n "$NEQ_SAMPLE_FILTER" || -n "$NEQ_PAIR_FILTER" ) ]]; then exit 1; fi
PAIR_PROCESS_TIMEOUT_SECONDS="$(printf '%s' "$PAIR_PROCESS_TIMEOUT" | sed 's/s$//')"
PAIR_PROCESS_KILL_AFTER_SECONDS="$(printf '%s' "$PAIR_PROCESS_KILL_AFTER" | sed 's/s$//')"

RESOURCE_ADMISSION_JOBS="$EQBENCH_CPU_TOKENS"
if (( EQBENCH_RESOURCE_ADMISSION == 1 )); then
    RESOURCE_ADMISSION_JOBS=$((EQBENCH_CPU_TOKENS / EQBENCH_PAIR_CPU_TOKENS))
    (( RESOURCE_ADMISSION_JOBS > 0 )) || RESOURCE_ADMISSION_JOBS=1
    (( PARALLEL_JOBS <= RESOURCE_ADMISSION_JOBS )) || PARALLEL_JOBS="$RESOURCE_ADMISSION_JOBS"
fi

IDS="B1 B2 B3 B4 B5 B6 B7 B8 B9 B10 B11 B12 B13 B14 B15 B16"
BINARY_ID_ARGS=()
for id in $IDS; do BINARY_ID_ARGS+=(--binary-id "$id"); done
binary_name() {
    local variant="$1" id="$2" arch compiler opt
    case "$id" in
        B1) arch=arm64; compiler=clang; opt=O0 ;; B2) arch=arm64; compiler=clang; opt=O1 ;;
        B3) arch=arm64; compiler=clang; opt=O2 ;; B4) arch=arm64; compiler=clang; opt=O3 ;;
        B5) arch=arm64; compiler=gcc; opt=O0 ;; B6) arch=arm64; compiler=gcc; opt=O1 ;;
        B7) arch=arm64; compiler=gcc; opt=O2 ;; B8) arch=arm64; compiler=gcc; opt=O3 ;;
        B9) arch=mips64; compiler=clang; opt=O0 ;; B10) arch=mips64; compiler=clang; opt=O1 ;;
        B11) arch=mips64; compiler=clang; opt=O2 ;; B12) arch=mips64; compiler=clang; opt=O3 ;;
        B13) arch=mips64; compiler=gcc; opt=O0 ;; B14) arch=mips64; compiler=gcc; opt=O1 ;;
        B15) arch=mips64; compiler=gcc; opt=O2 ;; B16) arch=mips64; compiler=gcc; opt=O3 ;;
        *) return 1 ;;
    esac
    printf '%s-%s-%s-%s' "$variant" "$arch" "$compiler" "$opt"
}
pair_selected() { [[ -z "$NEQ_PAIR_FILTER" || ",$NEQ_PAIR_FILTER," == *",$1,"* ]]; }
pair_count() {
    local count=0 a b
    for a in $IDS; do for b in $IDS; do pair_selected "N_${a}_O_${b}" && count=$((count + 1)); done; done
    printf '%s\n' "$count"
}

function_summary_is_complete() {
    local function_dir="$1" expected_pairs="$2" log_count status_count
    [[ -s "$function_dir/results_summary.txt" ]] || return 1
    log_count="$(find "$function_dir" -maxdepth 1 -type f -name '*.log' | wc -l)"
    status_count="$(find "$function_dir" -maxdepth 1 -type f -name '*.pair-status.json' | wc -l)"
    [[ "$log_count" == "$expected_pairs" && "$status_count" == "$expected_pairs" ]]
}

EXPECTED_PAIRS_PER_FUNCTION="$(pair_count)"

mkdir -p "$EQBENCH_TMPDIR"; chmod 1777 "$EQBENCH_TMPDIR" 2>/dev/null || true
probe="$(mktemp "$EQBENCH_TMPDIR/neqbench-tmp.XXXXXX")"; rm -f "$probe"
export TMPDIR="$EQBENCH_TMPDIR" TEMP="$EQBENCH_TMPDIR" TMP="$EQBENCH_TMPDIR"
RUN_TMP="$(mktemp -d "$EQBENCH_TMPDIR/neqbench-run.XXXXXX")"
cleanup() { [[ -d "$RUN_TMP" ]] && rm -rf -- "$RUN_TMP"; }
trap cleanup EXIT
trap 'exit 129' HUP; trap 'exit 130' INT; trap 'exit 143' TERM

mkdir -p "$OUTPUT_BASE_DIR"; OUTPUT_BASE_DIR="$(realpath -m "$OUTPUT_BASE_DIR")"
declare -A COMPLETED_FUNCTION_SUMMARY_DIRS=()
if [[ "$SKIP_COMPLETED_RESULTS" != 0 ]]; then
    while IFS= read -r -d '' summary_file; do
        function_dir="${summary_file%/results_summary.txt}"
        if function_summary_is_complete "$function_dir" "$EXPECTED_PAIRS_PER_FUNCTION"; then
            COMPLETED_FUNCTION_SUMMARY_DIRS["$function_dir"]=1
        fi
    done < <(find "$OUTPUT_BASE_DIR" -type f -name 'results_summary.txt' -print0)
fi
if [[ "$EQBENCH_PRIVATE_AUTHORITY_ROOT" == "$OUTPUT_BASE_DIR" || "$EQBENCH_PRIVATE_AUTHORITY_ROOT" == "$OUTPUT_BASE_DIR/"* ]]; then exit 1; fi
CENSUS="$OUTPUT_BASE_DIR/neq_source_pairs.tsv"; : > "$CENSUS"
SOURCE_PAIR_COUNT=0
while IFS= read -r dir; do
    [[ -n "$dir" ]] || continue
    rel="$(printf '%s' "$dir" | sed "s#^$NEQ_ROOT/##")"
    if [[ -f "$dir/newV.c" && -f "$dir/oldV.c" ]]; then new=newV; old=oldV
    elif [[ -f "$dir/new.c" && -f "$dir/old.c" ]]; then new=new; old=old
    else echo "Incomplete Neq pair: $dir" >&2; exit 1; fi
    label="$rel/$new-$old"
    [[ -z "$NEQ_SAMPLE_FILTER" || "$label" =~ $NEQ_SAMPLE_FILTER ]] || continue
    SOURCE_PAIR_COUNT=$((SOURCE_PAIR_COUNT + 1))
    printf '%s\t%s\t%s\n' "$label" "$dir/$new.c" "$dir/$old.c" >> "$CENSUS"
    if (( NEQ_MAX_SAMPLES > 0 && SOURCE_PAIR_COUNT >= NEQ_MAX_SAMPLES )); then break; fi
done < <(find "$NEQ_ROOT" -type d -name Neq -print | sort)
(( SOURCE_PAIR_COUNT > 0 )) || exit 1
CENSUS_DIGEST="$(sha256sum "$CENSUS" | awk '{print $1}')"
PREFILTER_SOURCE_CENSUS_FILE="$OUTPUT_BASE_DIR/prefilter_source_paths.txt"
cut -f1 "$CENSUS" > "$PREFILTER_SOURCE_CENSUS_FILE"
PREFILTER_SOURCE_CENSUS_DIGEST="$(sha256sum "$PREFILTER_SOURCE_CENSUS_FILE" | awk '{print $1}')"
if (( DRY_RUN == 1 )); then
    cp "$CENSUS" "$OUTPUT_BASE_DIR/dry_run_sources.txt"
    echo "selected=$SOURCE_PAIR_COUNT"
    exit 0
fi

KEYSET="$(printf '%s' "$OUTPUT_BASE_DIR" | sha256sum | awk '{print $1}')"
AUTHORITY_ROOT="$EQBENCH_PRIVATE_AUTHORITY_ROOT/$KEYSET"
SUPERVISOR_KEY_ID=eqbench-neq-supervisor-v1; WORKER_KEY_ID=eqbench-neq-worker-v1
SUPERVISOR_KEY="$AUTHORITY_ROOT/supervisor.key"; WORKER_KEY="$AUTHORITY_ROOT/worker.key"
PAIR_PRIVATE_KEY="$AUTHORITY_ROOT/pair-status-ed25519.key"; PAIR_PUBLIC_KEY="$OUTPUT_BASE_DIR/pair-status-verification-key.json"
existing_status="$(find "$OUTPUT_BASE_DIR" -type f -name '*.pair-status.json' -print -quit)"
if [[ -n "$existing_status" && ( ! -s "$SUPERVISOR_KEY" || ! -s "$WORKER_KEY" || ! -s "$PAIR_PRIVATE_KEY" || ! -s "$PAIR_PUBLIC_KEY" ) ]]; then
    echo "Existing Neq authority evidence has no complete retained keyset" >&2
    exit 1
fi
mkdir -p "$AUTHORITY_ROOT"; chmod 700 "$AUTHORITY_ROOT"
[[ -s "$SUPERVISOR_KEY" ]] || { umask 077; head -c 32 /dev/urandom > "$SUPERVISOR_KEY"; }
[[ -s "$WORKER_KEY" ]] || { umask 077; head -c 32 /dev/urandom > "$WORKER_KEY"; }
if [[ ! -s "$PAIR_PRIVATE_KEY" ]]; then
    "$PYTHON_BIN" -m scripts.function_tracer_pcode.equivalence.v2.pair_status_authority --generate-private-key "$PAIR_PRIVATE_KEY" --write-public-key "$PAIR_PUBLIC_KEY" >/dev/null
fi
"$PYTHON_BIN" -m scripts.function_tracer_pcode.equivalence.v2.pair_status_authority --validate-private-key "$PAIR_PRIVATE_KEY" --public-key "$PAIR_PUBLIC_KEY" >/dev/null
while IFS= read -r existing_status; do
    [[ -n "$existing_status" ]] || continue
    existing_function_dir="$(dirname "$existing_status")"
    if [[ "$SKIP_COMPLETED_RESULTS" != 0 \
        && -n "${COMPLETED_FUNCTION_SUMMARY_DIRS[$existing_function_dir]:-}" ]]; then
        continue
    fi
    "$PYTHON_BIN" -m scripts.function_tracer_pcode.equivalence.v2.pair_status_authority --validate-pair-status "$existing_status" --public-key "$PAIR_PUBLIC_KEY" >/dev/null
done < <(find "$OUTPUT_BASE_DIR" -type f -name '*.pair-status.json' -print)

PROCESS_CLEANUP_FAILURES="$OUTPUT_BASE_DIR/process_authority_cleanup_failures.txt"; : > "$PROCESS_CLEANUP_FAILURES"
EXPECTED_STATUS="$OUTPUT_BASE_DIR/expected_pair_status_paths.txt"; : > "$EXPECTED_STATUS"
VERIFIED_SKIPPED_STATUS="$OUTPUT_BASE_DIR/verified_skipped_pair_status_paths.txt"; : > "$VERIFIED_SKIPPED_STATUS"
COMPILE_FAILURE_SAMPLES_FILE="$OUTPUT_BASE_DIR/compile_failure_samples.txt"; : > "$COMPILE_FAILURE_SAMPLES_FILE"
MISSING_BINARY_AXES_FILE="$OUTPUT_BASE_DIR/missing_binary_axes.txt"; : > "$MISSING_BINARY_AXES_FILE"
FUNCTION_CENSUS_FAILURES_FILE="$OUTPUT_BASE_DIR/function_census_failures.txt"; : > "$FUNCTION_CENSUS_FAILURES_FILE"
USED_BUILD_RECEIPTS_FILE="$OUTPUT_BASE_DIR/used_build_receipts.jsonl"; : > "$USED_BUILD_RECEIPTS_FILE"

write_source_manifest() {
    local out="$1" new_source="$2" old_source="$3" tmp="$1.tmp.$$"
    "$PYTHON_BIN" - "$tmp" "$out" "$SCRIPT_DIR" "$new_source" "$old_source" <<'PY'
import hashlib, json, os, sys
from pathlib import Path
tmp, out, repo, new_path, old_path = sys.argv[1:]
root = Path(repo).resolve()
def item(kind, raw):
    path = Path(raw).resolve(strict=True)
    return {"variant": kind, "path": path.relative_to(root).as_posix(), "sha256": hashlib.sha256(path.read_bytes()).hexdigest()}
data = {"schema": "neq-source-pair-manifest-v1", "sources": [item("new", new_path), item("old", old_path)]}
with open(tmp, "w", encoding="utf-8") as f:
    json.dump(data, f, indent=2, sort_keys=True); f.write("\n"); f.flush(); os.fsync(f.fileno())
os.replace(tmp, out)
PY
}
record_missing_variant_axes() {
    local sample="$1" variant="$2" source_dir="$3" id name
    for id in $IDS; do
        name="$(binary_name "$variant" "$id")"
        if [[ ! -f "$source_dir/$name" ]]; then
            printf '%s/%s/%s\n' "$sample" "$variant" "$id" >> "$MISSING_BINARY_AXES_FILE"
            MISSING_BINARY_COUNT=$((MISSING_BINARY_COUNT + 1))
        fi
    done
}

prepare_variant() {
    local source="$1" variant="$2" source_dir="$3" sample="$4"
    local build_dir build_receipt_file receipt_json id name install_failed
    local require_fresh_args=()
    VARIANT_BUILD_RECEIPT_JSON=""
    VARIANT_BUILD_RESOLUTION=""
    build_receipt_file="$source_dir/.$variant.eqbench-build-receipt.json"
    if [[ "$NEQ_RUN_SCOPE" == FULL_NEQ ]]; then
        require_fresh_args+=(--require-fresh)
    fi

    if [[ "$NEQ_BUILD_POLICY" != FRESH_ONLY && -s "$build_receipt_file" ]]; then
        if receipt_json="$("$PYTHON_BIN" -m scripts.function_tracer_pcode.validation.eqbench_build_receipt \
            --repo-root "$SCRIPT_DIR" --receipt "$build_receipt_file" --validate \
            "${require_fresh_args[@]}" "${BINARY_ID_ARGS[@]}" 2>/dev/null)"; then
            VARIANT_BUILD_RECEIPT_JSON="$receipt_json"
            VARIANT_BUILD_RESOLUTION=VERIFIED_RECEIPT_REUSE
            return 0
        fi
    fi

    if [[ "$NEQ_BUILD_POLICY" != FRESH_ONLY && "$NEQ_RUN_SCOPE" == REPRESENTATIVE ]]; then
        install_failed=0
        for id in $IDS; do
            name="$(binary_name "$variant" "$id")"
            [[ -f "$source_dir/$name" ]] || { install_failed=1; break; }
        done
        if (( install_failed == 0 )); then
            if receipt_json="$("$PYTHON_BIN" -m scripts.function_tracer_pcode.validation.eqbench_build_receipt \
                --repo-root "$SCRIPT_DIR" --receipt "$build_receipt_file" --materialize \
                --provenance-kind ADOPTED_PREBUILT --sample-identity "$sample/$variant" \
                --source "$source" --compile-script "$COMPILE_TEMPLATE" \
                --binary-root "$source_dir" --target-binary-root "$source_dir" \
                "${BINARY_ID_ARGS[@]}")"; then
                VARIANT_BUILD_RECEIPT_JSON="$receipt_json"
                VARIANT_BUILD_RESOLUTION=ADOPTED_PREBUILT
                return 0
            fi
        fi
    fi

    build_dir="$RUN_TMP/build/$CURRENT_PAIR_INDEX/$variant"
    mkdir -p "$build_dir"
    cp "$source" "$build_dir/$variant.c"
    cp "$COMPILE_TEMPLATE" "$build_dir/compile_all.sh"
    chmod +x "$build_dir/compile_all.sh"
    if ! (cd "$build_dir" && ./compile_all.sh "$variant.c") > "$OUTPUT_SAMPLE/compile_$variant.log" 2>&1; then
        return 1
    fi
    for id in $IDS; do
        name="$(binary_name "$variant" "$id")"
        cp "$build_dir/$name" "$source_dir/.$name.new"
        mv -f "$source_dir/.$name.new" "$source_dir/$name"
    done
    if ! receipt_json="$("$PYTHON_BIN" -m scripts.function_tracer_pcode.validation.eqbench_build_receipt \
        --repo-root "$SCRIPT_DIR" --receipt "$build_receipt_file" --materialize \
        --provenance-kind FRESH_COMPILE --sample-identity "$sample/$variant" \
        --source "$source" --compile-script "$COMPILE_TEMPLATE" \
        --binary-root "$build_dir" --target-binary-root "$source_dir" \
        "${BINARY_ID_ARGS[@]}")"; then
        return 1
    fi
    VARIANT_BUILD_RECEIPT_JSON="$receipt_json"
    VARIANT_BUILD_RESOLUTION=FRESH_COMPILE
}

pair_status_is_terminal_result() {
    local log="$1" target="$2" status
    status="$(printf '%s' "$log" | sed 's/\.log$/.pair-status.json/')"
    [[ -s "$log" && -s "$status" ]] || return 1
    "$PYTHON_BIN" -m scripts.function_tracer_pcode.equivalence.v2.pair_status_authority --validate-pair-status "$status" --public-key "$PAIR_PUBLIC_KEY" --expected-pair-target "$target" 2>/dev/null | grep -Eq '^(EQUIVALENT|NOT_EQ|UNKNOWN|TIMEOUT|ERROR)$'
}
run_pair() {
    local sample="$1" function="$2" left_id="$3" right_id="$4" left="$5" right="$6" out="$7" count="$8" total="$9" target="${10}"
    local log="$out/$function"_"$left_id"_"$right_id.log" pair_tmp="$(mktemp -d "$RUN_TMP/pair.XXXXXX")"
    local nonce identity result_id source_fp stream exec_nonce checkpoint authority status_file detail ec=0
    nonce="$("$PYTHON_BIN" -c 'import secrets; print(secrets.token_hex(24))')"
    identity="$(PYTHONWARNINGS=ignore::RuntimeWarning "$PYTHON_BIN" -m scripts.function_tracer_pcode.equivalence.v2.phase8_cutover --print-production-execution-identity --binary1-path "$left" --binary2-path "$right" --binary1-id "$left_id" --binary2-id "$right_id" --function-name1 "$function" --function-name2 "$function" --result-entry-occurrence-nonce "$nonce")"
    IFS=$'\t' read -r result_id source_fp stream <<< "$identity"
    exec_nonce="$(printf '%s' "$result_id" | sed 's/^production-pilot-//')"; checkpoint="$RUN_TMP/process-authority"; authority="$checkpoint/$exec_nonce/supervisor-projection.json"; mkdir -p "$checkpoint"
    "$PYTHON_BIN" -m scripts.function_tracer_pcode.equivalence.v2.process_supervisor_command --checkpoint-root "$checkpoint" --authority-output "$authority" --working-directory "$SCRIPT_DIR" --execution-nonce "$exec_nonce" --result-occurrence-id "$result_id" --source-snapshot-fingerprint "$source_fp" --stream-id "$stream" --deadline-policy-digest "$(printf 'neq:%s:%s' "$PAIR_PROCESS_TIMEOUT_SECONDS" "$PAIR_PROCESS_KILL_AFTER_SECONDS" | sha256sum | awk '{print $1}')" --supervisor-signing-key-id "$SUPERVISOR_KEY_ID" --supervisor-signing-key-file "$SUPERVISOR_KEY" --worker-signing-key-id "$WORKER_KEY_ID" --worker-signing-key-file "$WORKER_KEY" --timeout-seconds "$PAIR_PROCESS_TIMEOUT_SECONDS" --kill-grace-seconds "$PAIR_PROCESS_KILL_AFTER_SECONDS" --allow-child-exit-resolution -- env TMPDIR="$pair_tmp" TEMP="$pair_tmp" TMP="$pair_tmp" UNKNOWN_TAXONOMY_V2_RESULT_ENTRY_OCCURRENCE_NONCE="$nonce" "$PYTHON_BIN" -m scripts.function_tracer_pcode.cli.main --equiv "$left" "$right" --binary-ids "$left_id" "$right_id" -f "$function" --emit-result-json --equiv-timeout "$EQUIV_TIMEOUT" --timeout "$DECOMPILE_TIMEOUT" --pairwise-timeout "$PAIRWISE_TIMEOUT" --pairwise-timeout-hard "$PAIRWISE_TIMEOUT_HARD" > "$log" 2>&1 || ec=$?
    status_file="$out/$function"_"$left_id"_"$right_id.pair-status.json"
    "$PYTHON_BIN" -m scripts.function_tracer_pcode.equivalence.v2.canonical_result --classify-pair-log "$log" --supervisor-projection "$authority" --checkpoint-root "$checkpoint" --execution-nonce "$exec_nonce" --supervisor-signing-key-id "$SUPERVISOR_KEY_ID" --supervisor-signing-key-file "$SUPERVISOR_KEY" --worker-signing-key-id "$WORKER_KEY_ID" --worker-signing-key-file "$WORKER_KEY" --pair-status-signing-private-key-file "$PAIR_PRIVATE_KEY" --pair-status-verification-key-file "$PAIR_PUBLIC_KEY" --pair-execution-target-file "$target" --classification-diagnostic-log "$log" > "$status_file" || ec=1
    if detail="$("$PYTHON_BIN" -m scripts.function_tracer_pcode.equivalence.v2.pair_status_authority --validate-pair-status "$status_file" --public-key "$PAIR_PUBLIC_KEY" --expected-pair-target "$target" --allow-operational-diagnostic 2>&1)"; then status="$detail"; else status=ERROR; ec=1; fi
    "$PYTHON_BIN" -m scripts.function_tracer_pcode.validation.process_authority_cleanup --tmp-root "$EQBENCH_TMPDIR" --run-tmpdir "$RUN_TMP" --checkpoint-root "$checkpoint" --execution-nonce "$exec_nonce" || { printf '%s\t%s\t%s\n' "$sample" "$function" "$exec_nonce" >> "$PROCESS_CLEANUP_FAILURES"; ec=1; }
    rm -rf "$pair_tmp"
    printf '[%s] [%s %s/%s] %s <-> %s : %s\n' "$sample" "$function" "$count" "$total" "$left_id" "$right_id" "$status"
    return "$ec"
}
wait_slot() {
    if (( ACTIVE_JOBS >= PARALLEL_JOBS )); then
        if ! wait -n; then RUN_PAIR_FAILURES=$((RUN_PAIR_FAILURES + 1)); fi
        ACTIVE_JOBS=$((ACTIVE_JOBS - 1))
    fi
}
wait_all() {
    while (( ACTIVE_JOBS > 0 )); do
        if ! wait -n; then RUN_PAIR_FAILURES=$((RUN_PAIR_FAILURES + 1)); fi
        ACTIVE_JOBS=$((ACTIVE_JOBS - 1))
    done
}

ANALYSIS_SOURCE_DIGEST="$("$PYTHON_BIN" -m scripts.function_tracer_pcode.validation.execution_identity --repo-root "$SCRIPT_DIR" --print-source-digest)"
RUN_MANIFEST="$OUTPUT_BASE_DIR/run_manifest.txt"
cat > "$RUN_MANIFEST" <<EOF
run_kind=neqbench_all_cross_matrix_current
run_scope=$NEQ_RUN_SCOPE
build_policy=$NEQ_BUILD_POLICY
neq_root=$NEQ_ROOT
output_base_dir=$OUTPUT_BASE_DIR
parallel_jobs=$PARALLEL_JOBS
resource_admission_jobs=$RESOURCE_ADMISSION_JOBS
validation_summary_level=$VALIDATION_SUMMARY_LEVEL
pair_process_timeout=$PAIR_PROCESS_TIMEOUT
pair_process_kill_after=$PAIR_PROCESS_KILL_AFTER
pair_process_timeout_seconds=$PAIR_PROCESS_TIMEOUT_SECONDS
pair_process_kill_after_seconds=$PAIR_PROCESS_KILL_AFTER_SECONDS
equiv_timeout=$EQUIV_TIMEOUT
decompile_timeout=$DECOMPILE_TIMEOUT
pairwise_timeout=$PAIRWISE_TIMEOUT
pairwise_timeout_hard=$PAIRWISE_TIMEOUT_HARD
skip_completed_results=$SKIP_COMPLETED_RESULTS
debug=$EQBENCH_DEBUG
max_samples=$NEQ_MAX_SAMPLES
sample_filter=$NEQ_SAMPLE_FILTER
pair_filter=$NEQ_PAIR_FILTER
dry_run=$DRY_RUN
prefilter_source_count=$SOURCE_PAIR_COUNT
prefilter_source_census_digest=$PREFILTER_SOURCE_CENSUS_DIGEST
target_sources=$SOURCE_PAIR_COUNT
compile_axes=arm64,mips64 x clang,gcc x O0,O1,O2,O3
new_binary_count=16
old_binary_count=16
expected_cross_pairs_per_function=256
source_pair_count=$SOURCE_PAIR_COUNT
source_pair_census_digest=$CENSUS_DIGEST
runner_script_sha256=$(sha256sum "$SCRIPT_DIR/neqbench_run_all_32jobs.sh" | awk '{print $1}')
analysis_source_digest_start=$ANALYSIS_SOURCE_DIGEST
EOF
CONFIG_DIGEST="$("$PYTHON_BIN" -m scripts.function_tracer_pcode.validation.execution_receipt --run-manifest "$RUN_MANIFEST" --print-analysis-config-digest)"
printf 'analysis_config_digest=%s\n' "$CONFIG_DIGEST" >> "$RUN_MANIFEST"

ACTIVE_JOBS=0
RUN_PAIR_FAILURES=0
RUN_COMPILE_FAILURES=0
FUNCTION_CENSUS_FAILURES=0
MISSING_BINARY_COUNT=0
EXPECTED_BINARY_COUNT=0
COMPILED_BINARY_COUNT=0
TOTAL_FUNCTIONS=0
COMPLETED_SAMPLES=0
SKIPPED_SAMPLES=0
TOTAL_PAIR_JOBS=0
TOTAL_SCHEDULED_PAIR_JOBS=0
TOTAL_SKIPPED_PAIR_JOBS=0
CURRENT_PAIR_INDEX=0
while IFS="$(printf '\t')" read -r sample new_source old_source; do
    [[ -n "$sample" ]] || continue
    dir="$(dirname "$new_source")"; new="$(basename "$new_source" .c)"; old="$(basename "$old_source" .c)"
    source_dir="$dir/source"; OUTPUT_SAMPLE="$OUTPUT_BASE_DIR/$sample"; mkdir -p "$source_dir" "$OUTPUT_SAMPLE"
    cmp -s "$new_source" "$source_dir/$new.c" || cp "$new_source" "$source_dir/$new.c"
    cmp -s "$old_source" "$source_dir/$old.c" || cp "$old_source" "$source_dir/$old.c"
    cp "$COMPILE_TEMPLATE" "$source_dir/compile_all.sh"; chmod +x "$source_dir/compile_all.sh"
    manifest="$source_dir/.$new-$old.neq-source-pair-manifest.json"; write_source_manifest "$manifest" "$new_source" "$old_source"
    CURRENT_PAIR_INDEX=$((CURRENT_PAIR_INDEX + 1))
    "$PYTHON_BIN" "$FUNCTION_LISTER" "$new_source" | sort -u > "$RUN_TMP/new.functions"
    "$PYTHON_BIN" "$FUNCTION_LISTER" "$old_source" | sort -u > "$RUN_TMP/old.functions"
    if ! cmp -s "$RUN_TMP/new.functions" "$RUN_TMP/old.functions"; then
        diff -u "$RUN_TMP/new.functions" "$RUN_TMP/old.functions" > "$OUTPUT_SAMPLE/function-census.diff" || true
        printf '%s\n' "$sample" >> "$FUNCTION_CENSUS_FAILURES_FILE"
        FUNCTION_CENSUS_FAILURES=$((FUNCTION_CENSUS_FAILURES + 1))
        RUN_PAIR_FAILURES=$((RUN_PAIR_FAILURES + 1))
        continue
    fi
    EXPECTED_BINARY_COUNT=$((EXPECTED_BINARY_COUNT + 32))
    new_ready=1
    if ! prepare_variant "$new_source" "$new" "$source_dir" "$sample"; then
        new_ready=0
        printf '%s/%s\n' "$sample" "$new" >> "$COMPILE_FAILURE_SAMPLES_FILE"
        RUN_COMPILE_FAILURES=$((RUN_COMPILE_FAILURES + 1))
        record_missing_variant_axes "$sample" "$new" "$source_dir"
    else
        COMPILED_BINARY_COUNT=$((COMPILED_BINARY_COUNT + 16))
        printf '%s\n' "$VARIANT_BUILD_RECEIPT_JSON" >> "$USED_BUILD_RECEIPTS_FILE"
    fi
    old_ready=1
    if ! prepare_variant "$old_source" "$old" "$source_dir" "$sample"; then
        old_ready=0
        printf '%s/%s\n' "$sample" "$old" >> "$COMPILE_FAILURE_SAMPLES_FILE"
        RUN_COMPILE_FAILURES=$((RUN_COMPILE_FAILURES + 1))
        record_missing_variant_axes "$sample" "$old" "$source_dir"
    else
        COMPILED_BINARY_COUNT=$((COMPILED_BINARY_COUNT + 16))
        printf '%s\n' "$VARIANT_BUILD_RECEIPT_JSON" >> "$USED_BUILD_RECEIPTS_FILE"
    fi
    if (( new_ready == 0 || old_ready == 0 )); then
        RUN_PAIR_FAILURES=$((RUN_PAIR_FAILURES + 1))
        continue
    fi
    COMPLETED_SAMPLES=$((COMPLETED_SAMPLES + 1))
    while IFS= read -r function; do
        [[ -n "$function" ]] || continue
        TOTAL_FUNCTIONS=$((TOTAL_FUNCTIONS + 1))
        function_dir="$OUTPUT_SAMPLE/$function"; mkdir -p "$function_dir"; total="$(pair_count)"; count=0
        if [[ "$SKIP_COMPLETED_RESULTS" != 0 ]] \
            && -n "${COMPLETED_FUNCTION_SUMMARY_DIRS[$function_dir]:-}"; then
            function_skipped_pairs=0
            while read -r a; do while read -r b; do
                left_id="N_$a"; right_id="O_$b"; pair="$left_id"_"$right_id"; pair_selected "$pair" || continue
                status_file="$function_dir/$function"_"$pair.pair-status.json"
                printf '%s\n' "${status_file#$OUTPUT_BASE_DIR/}" >> "$EXPECTED_STATUS"
                printf '%s\n' "${status_file#$OUTPUT_BASE_DIR/}" >> "$VERIFIED_SKIPPED_STATUS"
                TOTAL_PAIR_JOBS=$((TOTAL_PAIR_JOBS + 1))
                TOTAL_SKIPPED_PAIR_JOBS=$((TOTAL_SKIPPED_PAIR_JOBS + 1))
                function_skipped_pairs=$((function_skipped_pairs + 1))
            done < <(printf '%s\n' $IDS); done < <(printf '%s\n' $IDS)
            echo "[$sample] [$function] Skipped completed function: results_summary.txt exists; pairs=$function_skipped_pairs/$total"
            continue
        fi
        while read -r a; do while read -r b; do
            left_id="N_$a"; right_id="O_$b"; pair="$left_id"_"$right_id"; pair_selected "$pair" || continue
            left="$source_dir/$(binary_name "$new" "$a")"; right="$source_dir/$(binary_name "$old" "$b")"; count=$((count + 1)); TOTAL_PAIR_JOBS=$((TOTAL_PAIR_JOBS + 1))
            log="$function_dir/$function"_"$pair.log"; status_file="$function_dir/$function"_"$pair.pair-status.json"; target="$RUN_TMP/$TOTAL_PAIR_JOBS.target.json"
            printf '%s\n' "$status_file" | sed "s#^$OUTPUT_BASE_DIR/##" >> "$EXPECTED_STATUS"
            "$PYTHON_BIN" -m scripts.function_tracer_pcode.validation.execution_identity --repo-root "$SCRIPT_DIR" --build-pair-target --sample-identity "$sample" --output-sample-relative-path "$sample" --function-name "$function" --left-binary-id "$left_id" --right-binary-id "$right_id" --source-path "$manifest" --left-binary-path "$left" --right-binary-path "$right" --analysis-source-digest "$ANALYSIS_SOURCE_DIGEST" --analysis-config-digest "$CONFIG_DIGEST" > "$target"
            if [[ "$SKIP_COMPLETED_RESULTS" != 0 ]] && pair_status_is_terminal_result "$log" "$target"; then
                printf '%s\n' "${status_file#$OUTPUT_BASE_DIR/}" >> "$VERIFIED_SKIPPED_STATUS"
                TOTAL_SKIPPED_PAIR_JOBS=$((TOTAL_SKIPPED_PAIR_JOBS + 1))
                continue
            fi
            wait_slot
            TOTAL_SCHEDULED_PAIR_JOBS=$((TOTAL_SCHEDULED_PAIR_JOBS + 1))
            run_pair "$sample" "$function" "$left_id" "$right_id" "$left" "$right" "$function_dir" "$count" "$total" "$target" &
            ACTIVE_JOBS=$((ACTIVE_JOBS + 1))
        done < <(printf '%s\n' $IDS); done < <(printf '%s\n' $IDS)
        wait_all
        find "$function_dir" -maxdepth 1 -type f -name '*.log' -print0 > "$function_dir/.summary-log-paths.list0"
        "$PYTHON_BIN" -m scripts.function_tracer_pcode.validation.result_summary --function-summary --canonical-only --function-name "$function" --summary-level compact --log-list0 "$function_dir/.summary-log-paths.list0" > "$function_dir/results_summary.txt" || true
    done < "$RUN_TMP/new.functions"
done < "$CENSUS"
wait_all
find "$OUTPUT_BASE_DIR" -type f -name '*.log' ! -name 'compile_*.log' ! -name 'run_stdout.log' -print0 > "$OUTPUT_BASE_DIR/.overall-summary-log-paths.list0"
"$PYTHON_BIN" -m scripts.function_tracer_pcode.validation.result_summary \
    --overall-summary --canonical-only --summary-level "$VALIDATION_SUMMARY_LEVEL" \
    --health-summary-json "$OUTPUT_BASE_DIR/run_health_summary.json" \
    --health-summary-text "$OUTPUT_BASE_DIR/run_health_summary.txt" \
    --log-list0 "$OUTPUT_BASE_DIR/.overall-summary-log-paths.list0" \
    > "$OUTPUT_BASE_DIR/overall_summary.txt" || true
cat >> "$RUN_MANIFEST" <<EOF
completed_samples=$COMPLETED_SAMPLES
skipped_samples=$SKIPPED_SAMPLES
total_functions=$TOTAL_FUNCTIONS
total_pair_jobs=$TOTAL_PAIR_JOBS
total_scheduled_pair_jobs=$TOTAL_SCHEDULED_PAIR_JOBS
total_skipped_pair_jobs=$TOTAL_SKIPPED_PAIR_JOBS
expected_pairs_per_function=256
expected_binary_count=$EXPECTED_BINARY_COUNT
compiled_binary_count=$COMPILED_BINARY_COUNT
compile_failure_count=$RUN_COMPILE_FAILURES
missing_binary_count=$MISSING_BINARY_COUNT
function_census_failure_count=$FUNCTION_CENSUS_FAILURES
run_pair_failures=$RUN_PAIR_FAILURES
run_failures=$RUN_PAIR_FAILURES
analysis_source_digest_end=$("$PYTHON_BIN" -m scripts.function_tracer_pcode.validation.execution_identity --repo-root "$SCRIPT_DIR" --print-source-digest)
EOF
exit_status=0
if (( RUN_PAIR_FAILURES > 0 || RUN_COMPILE_FAILURES > 0 || MISSING_BINARY_COUNT > 0 || FUNCTION_CENSUS_FAILURES > 0 )); then
    exit_status=1
fi
"$PYTHON_BIN" -m scripts.function_tracer_pcode.validation.execution_receipt --repo-root "$SCRIPT_DIR" --private-key "$PAIR_PRIVATE_KEY" --public-key "$PAIR_PUBLIC_KEY" --output "$OUTPUT_BASE_DIR/validation-execution-receipt.json" --matrix-root "$OUTPUT_BASE_DIR" --source-digest-start "$ANALYSIS_SOURCE_DIGEST" --analysis-config-digest "$CONFIG_DIGEST" --exit-status "$exit_status" -- "env" "NEQ_RUN_SCOPE=$NEQ_RUN_SCOPE" "NEQ_BUILD_POLICY=$NEQ_BUILD_POLICY" "./neqbench_run_all_32jobs.sh"
echo "NeqBench cross matrix finished: $OUTPUT_BASE_DIR"
exit "$exit_status"

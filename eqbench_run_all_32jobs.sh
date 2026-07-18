#!/usr/bin/env bash
# Compile every EqBench Eq/newV.c or Eq/new.c sample into Eq/source and run a
# pairwise equivalence matrix for every non-main source-defined function.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"
source "$SCRIPT_DIR/scripts/validation_matrix_common.sh" || exit 1

if (( BASH_VERSINFO[0] < 4 || (BASH_VERSINFO[0] == 4 && BASH_VERSINFO[1] < 3) )); then
    echo "Error: bash 4.3 or newer is required for wait -n" >&2
    exit 1
fi

DEFAULT_PYTHON_BIN="python3"
if [[ -x "$SCRIPT_DIR/.venv-pyghidra/bin/python" ]]; then
    DEFAULT_PYTHON_BIN="$SCRIPT_DIR/.venv-pyghidra/bin/python"
fi

EQBENCH_ROOT="${EQBENCH_ROOT:-$SCRIPT_DIR/targets/EqBench/benchmarks}"
OUTPUT_BASE_DIR="${OUTPUT_BASE_DIR:-$SCRIPT_DIR/logs/EqBench/all_eq_matrix_current}"
PYTHON_BIN="${PYTHON_BIN:-$DEFAULT_PYTHON_BIN}"
PARALLEL_JOBS="${PARALLEL_JOBS:-32}"
VALIDATION_SUMMARY_LEVEL="${VALIDATION_SUMMARY_LEVEL:-compact}"
EQBENCH_MAX_SAMPLES="${EQBENCH_MAX_SAMPLES:-0}"
DRY_RUN="${DRY_RUN:-0}"
PAIR_PROCESS_TIMEOUT="${PAIR_PROCESS_TIMEOUT:-300s}"
PAIR_PROCESS_KILL_AFTER="${PAIR_PROCESS_KILL_AFTER:-30s}"
PAIR_PROCESS_TIMEOUT_SECONDS="${PAIR_PROCESS_TIMEOUT%s}"
PAIR_PROCESS_KILL_AFTER_SECONDS="${PAIR_PROCESS_KILL_AFTER%s}"
EQUIV_TIMEOUT="${EQUIV_TIMEOUT:-10}"
DECOMPILE_TIMEOUT="${DECOMPILE_TIMEOUT:-60}"
PAIRWISE_TIMEOUT="${PAIRWISE_TIMEOUT:-5}"
PAIRWISE_TIMEOUT_HARD="${PAIRWISE_TIMEOUT_HARD:-30}"
SKIP_COMPLETED_RESULTS="${SKIP_COMPLETED_RESULTS:-1}"
DEFAULT_TMPDIR="$SCRIPT_DIR/tmp"
if [[ -d /workspace && -w /workspace ]]; then
    DEFAULT_TMPDIR="/workspace/tmp"
fi
EQBENCH_TMPDIR="${EQBENCH_TMPDIR:-$DEFAULT_TMPDIR}"

COMPILE_TEMPLATE="$SCRIPT_DIR/scripts/eqbench/compile_all_arm_mips.sh"
FUNCTION_LISTER="$SCRIPT_DIR/scripts/eqbench/list_c_functions.py"

if [[ ! -f "$COMPILE_TEMPLATE" ]]; then
    echo "Error: compile template not found: $COMPILE_TEMPLATE" >&2
    exit 1
fi
if [[ ! -f "$FUNCTION_LISTER" ]]; then
    echo "Error: function lister not found: $FUNCTION_LISTER" >&2
    exit 1
fi
if [[ ! "$PAIR_PROCESS_TIMEOUT_SECONDS" =~ ^[0-9]+([.][0-9]+)?$ ]] \
    || [[ ! "$PAIR_PROCESS_KILL_AFTER_SECONDS" =~ ^[0-9]+([.][0-9]+)?$ ]]; then
    echo "Error: pair process timeout values must be seconds, for example 300s" >&2
    exit 1
fi

mkdir -p "$EQBENCH_TMPDIR"
chmod 1777 "$EQBENCH_TMPDIR" 2>/dev/null || true
if ! tmp_probe="$(mktemp "$EQBENCH_TMPDIR/eqbench-tmp.XXXXXX" 2>/dev/null)"; then
    echo "Error: cannot create temporary files in EQBENCH_TMPDIR=$EQBENCH_TMPDIR" >&2
    exit 1
fi
rm -f "$tmp_probe"
export TMPDIR="$EQBENCH_TMPDIR"
export TEMP="$EQBENCH_TMPDIR"
export TMP="$EQBENCH_TMPDIR"

IDS=(B1 B2 B3 B4 B5 B6 B7 B8 B9 B10 B11 B12 B13 B14 B15 B16)
declare -A ARCH_BY_ID=(
    [B1]=arm64 [B2]=arm64 [B3]=arm64 [B4]=arm64
    [B5]=arm64 [B6]=arm64 [B7]=arm64 [B8]=arm64
    [B9]=mips64 [B10]=mips64 [B11]=mips64 [B12]=mips64
    [B13]=mips64 [B14]=mips64 [B15]=mips64 [B16]=mips64
)
declare -A COMPILER_BY_ID=(
    [B1]=clang [B2]=clang [B3]=clang [B4]=clang
    [B5]=gcc [B6]=gcc [B7]=gcc [B8]=gcc
    [B9]=clang [B10]=clang [B11]=clang [B12]=clang
    [B13]=gcc [B14]=gcc [B15]=gcc [B16]=gcc
)
declare -A OPT_BY_ID=(
    [B1]=O0 [B2]=O1 [B3]=O2 [B4]=O3
    [B5]=O0 [B6]=O1 [B7]=O2 [B8]=O3
    [B9]=O0 [B10]=O1 [B11]=O2 [B12]=O3
    [B13]=O0 [B14]=O1 [B15]=O2 [B16]=O3
)

active_jobs=0
RUN_PAIR_FAILURES=0
TOTAL_PAIR_JOBS=0
TOTAL_SKIPPED_PAIR_JOBS=0
TOTAL_FUNCTIONS=0
TOTAL_SAMPLES=0
SKIPPED_SAMPLES=0

status_from_log() {
    local log_file="$1"
    case "$(validation_classify_log_result "$log_file")" in
        EQ)
            echo "EQUIVALENT"
            ;;
        NOT_EQ)
            echo "NOT EQUIVALENT"
            ;;
        ERROR)
            echo "ERROR"
            ;;
        TIMEOUT)
            echo "TIMEOUT"
            ;;
        UNKNOWN)
            echo "UNKNOWN"
            ;;
        *)
            echo "INCOMPLETE"
            ;;
    esac
}

run_pair() {
    local sample_label="$1"
    local function_name="$2"
    local left_id="$3"
    local right_id="$4"
    local left_bin="$5"
    local right_bin="$6"
    local output_dir="$7"
    local count="$8"
    local total="$9"
    local log_file="${output_dir}/${function_name}_${left_id}_${right_id}.log"
    local identity_line result_occurrence_id source_snapshot_fingerprint stream_id
    identity_line="$(PYTHONWARNINGS="ignore::RuntimeWarning" "$PYTHON_BIN" -m \
        scripts.function_tracer_pcode.equivalence.v2.phase8_cutover \
        --print-production-execution-identity \
        --binary1-path "$left_bin" --binary2-path "$right_bin" \
        --binary1-id "$left_id" --binary2-id "$right_id" \
        --function-name1 "$function_name" --function-name2 "$function_name")"
    IFS=$'\t' read -r result_occurrence_id source_snapshot_fingerprint stream_id \
        <<< "$identity_line"
    local execution_nonce checkpoint_root authority_output
    execution_nonce="${result_occurrence_id#production-pilot-}"
    checkpoint_root="${output_dir}/.process-authority"
    authority_output="${checkpoint_root}/${execution_nonce}/supervisor-projection.json"
    mkdir -p "$checkpoint_root"

    local -a equiv_cmd=(
        "$PYTHON_BIN" -m scripts.function_tracer_pcode.cli.main
        --equiv "$left_bin" "$right_bin" \
        --binary-ids "$left_id" "$right_id" \
        -f "$function_name" -d --emit-result-json
        --equiv-timeout "$EQUIV_TIMEOUT"
        --timeout "$DECOMPILE_TIMEOUT"
        --pairwise-timeout "$PAIRWISE_TIMEOUT"
        --pairwise-timeout-hard "$PAIRWISE_TIMEOUT_HARD"
    )

    local ec
    if "$PYTHON_BIN" -m \
        scripts.function_tracer_pcode.equivalence.v2.process_supervisor_command \
        --checkpoint-root "$checkpoint_root" \
        --authority-output "$authority_output" \
        --working-directory "$SCRIPT_DIR" \
        --execution-nonce "$execution_nonce" \
        --result-occurrence-id "$result_occurrence_id" \
        --source-snapshot-fingerprint "$source_snapshot_fingerprint" \
        --stream-id "$stream_id" \
        --deadline-policy-digest "$PAIR_PROCESS_DEADLINE_POLICY_DIGEST" \
        --supervisor-signing-key-id "$PROCESS_SUPERVISOR_KEY_ID" \
        --supervisor-signing-key-file "$PROCESS_SUPERVISOR_KEY_FILE" \
        --worker-signing-key-id "$PROCESS_WORKER_KEY_ID" \
        --worker-signing-key-file "$PROCESS_WORKER_KEY_FILE" \
        --timeout-seconds "$PAIR_PROCESS_TIMEOUT_SECONDS" \
        --kill-grace-seconds "$PAIR_PROCESS_KILL_AFTER_SECONDS" \
        -- "${equiv_cmd[@]}" > "$log_file" 2>&1; then
        ec=0
    else
        ec=$?
    fi

    if (( ec == 124 || ec == 137 )); then
        {
            echo ""
            echo "Pair process timeout: exceeded PAIR_PROCESS_TIMEOUT=$PAIR_PROCESS_TIMEOUT"
            echo "Timeout kill-after: PAIR_PROCESS_KILL_AFTER=$PAIR_PROCESS_KILL_AFTER"
            echo "Result: TIMEOUT (pair process exceeded wall-clock time limit)"
        } >> "$log_file"
        PYTHONWARNINGS="ignore::RuntimeWarning" "$PYTHON_BIN" -m \
            scripts.function_tracer_pcode.equivalence.v2.phase8_cutover \
            --emit-process-timeout-json \
            --checkpoint-root "$checkpoint_root" \
            --execution-nonce "$execution_nonce" \
            --supervisor-signing-key-id "$PROCESS_SUPERVISOR_KEY_ID" \
            --supervisor-signing-key-file "$PROCESS_SUPERVISOR_KEY_FILE" \
            --worker-signing-key-id "$PROCESS_WORKER_KEY_ID" \
            --worker-signing-key-file "$PROCESS_WORKER_KEY_FILE" \
            >> "$log_file"
    fi

    validation_ensure_final_result_line "$log_file" "$ec"

    local status
    status="$(status_from_log "$log_file")"
    printf '[%s] [%s %s/%s] %s <-> %s : %s' \
        "$sample_label" "$function_name" "$count" "$total" "$left_id" "$right_id" "$status"
    if (( ec != 0 )); then
        printf ' (exit=%s)' "$ec"
    fi
    printf '\n'
    return 0
}

wait_for_slot() {
    if (( active_jobs >= PARALLEL_JOBS )); then
        if ! wait -n; then
            RUN_PAIR_FAILURES=$((RUN_PAIR_FAILURES + 1))
        fi
        active_jobs=$((active_jobs - 1))
    fi
}

wait_for_all_jobs() {
    while (( active_jobs > 0 )); do
        if ! wait -n; then
            RUN_PAIR_FAILURES=$((RUN_PAIR_FAILURES + 1))
        fi
        active_jobs=$((active_jobs - 1))
    done
}

binary_name_for_id() {
    local source_base="$1"
    local id="$2"
    printf '%s-%s-%s-%s' "$source_base" "${ARCH_BY_ID[$id]}" "${COMPILER_BY_ID[$id]}" "${OPT_BY_ID[$id]}"
}

write_summary_file() {
    local output_file="$1"
    shift
    local tmp_file
    tmp_file="$(mktemp "${output_file}.tmp.XXXXXX")" || return 1
    if "$@" > "$tmp_file"; then
        tee "$output_file" < "$tmp_file"
        rm -f "$tmp_file"
        return 0
    fi
    local status=$?
    rm -f "$tmp_file"
    echo "Error: summary generation failed for $output_file (exit=$status)" >&2
    return "$status"
}

mapfile -t SAMPLE_SOURCES < <(
    find "$EQBENCH_ROOT" \
        -path '*/Eq/source/*' -prune -o \
        \( -path '*/Eq/newV.c' -o -path '*/Eq/new.c' \) \
        -type f -print | sort
)

if (( EQBENCH_MAX_SAMPLES > 0 && ${#SAMPLE_SOURCES[@]} > EQBENCH_MAX_SAMPLES )); then
    SAMPLE_SOURCES=("${SAMPLE_SOURCES[@]:0:EQBENCH_MAX_SAMPLES}")
fi

mkdir -p "$OUTPUT_BASE_DIR"
PROCESS_AUTHORITY_ROOT="$OUTPUT_BASE_DIR/.process-authority-keys"
mkdir -p "$PROCESS_AUTHORITY_ROOT"
chmod 700 "$PROCESS_AUTHORITY_ROOT"
PROCESS_SUPERVISOR_KEY_ID="eqbench-phase8-supervisor-v1"
PROCESS_WORKER_KEY_ID="eqbench-phase8-worker-v1"
PROCESS_SUPERVISOR_KEY_FILE="$PROCESS_AUTHORITY_ROOT/supervisor.key"
PROCESS_WORKER_KEY_FILE="$PROCESS_AUTHORITY_ROOT/worker.key"
if [[ ! -s "$PROCESS_SUPERVISOR_KEY_FILE" ]]; then
    umask 077
    head -c 32 /dev/urandom > "$PROCESS_SUPERVISOR_KEY_FILE"
fi
if [[ ! -s "$PROCESS_WORKER_KEY_FILE" ]]; then
    umask 077
    head -c 32 /dev/urandom > "$PROCESS_WORKER_KEY_FILE"
fi
PAIR_PROCESS_DEADLINE_POLICY_DIGEST="$(printf '%s' \
    "phase8:${PAIR_PROCESS_TIMEOUT_SECONDS}:${PAIR_PROCESS_KILL_AFTER_SECONDS}" \
    | sha256sum | awk '{print $1}')"
export PROCESS_SUPERVISOR_KEY_ID PROCESS_WORKER_KEY_ID
export PROCESS_SUPERVISOR_KEY_FILE PROCESS_WORKER_KEY_FILE
export PAIR_PROCESS_DEADLINE_POLICY_DIGEST

cat > "$OUTPUT_BASE_DIR/run_manifest.txt" <<EOF
run_kind=eqbench_all_eq_matrix_current
eqbench_root=$EQBENCH_ROOT
output_base_dir=$OUTPUT_BASE_DIR
python_bin=$PYTHON_BIN
parallel_jobs=$PARALLEL_JOBS
pair_process_timeout=$PAIR_PROCESS_TIMEOUT
pair_process_kill_after=$PAIR_PROCESS_KILL_AFTER
equiv_timeout=$EQUIV_TIMEOUT
decompile_timeout=$DECOMPILE_TIMEOUT
pairwise_timeout=$PAIRWISE_TIMEOUT
pairwise_timeout_hard=$PAIRWISE_TIMEOUT_HARD
skip_completed_results=$SKIP_COMPLETED_RESULTS
eqbench_tmpdir=$EQBENCH_TMPDIR
compile_axes=arm64,mips64 x clang,gcc x O0,O1,O2,O3
target_sources=${#SAMPLE_SOURCES[@]}
function_policy=all top-level source-defined functions except main
binary_policy=pairwise among B1..B16 when both binaries exist
dry_run=$DRY_RUN
EOF

echo "============================================================"
echo "EqBench all-sample matrix"
echo "============================================================"
echo "EqBench root: $EQBENCH_ROOT"
echo "Output base: $OUTPUT_BASE_DIR"
echo "Python: $PYTHON_BIN"
echo "Parallel jobs: $PARALLEL_JOBS"
echo "Pair process timeout: $PAIR_PROCESS_TIMEOUT (kill after $PAIR_PROCESS_KILL_AFTER)"
echo "Equiv timeout: $EQUIV_TIMEOUT"
echo "Decompile timeout: $DECOMPILE_TIMEOUT"
echo "Pairwise timeout: $PAIRWISE_TIMEOUT (hard $PAIRWISE_TIMEOUT_HARD)"
echo "Skip completed results: $SKIP_COMPLETED_RESULTS"
echo "Temporary directory: $EQBENCH_TMPDIR"
echo "Target sources: ${#SAMPLE_SOURCES[@]}"
echo "Dry run: $DRY_RUN"
echo "============================================================"

if (( DRY_RUN != 0 )); then
    printf '%s\n' "${SAMPLE_SOURCES[@]}" > "$OUTPUT_BASE_DIR/dry_run_sources.txt"
    echo "Dry run wrote: $OUTPUT_BASE_DIR/dry_run_sources.txt"
    exit 0
fi

for source_path in "${SAMPLE_SOURCES[@]}"; do
    eq_dir="$(dirname "$source_path")"
    source_name="$(basename "$source_path")"
    source_base="${source_name%.c}"
    rel_eq_dir="${eq_dir#$EQBENCH_ROOT/}"
    sample_label="$rel_eq_dir/$source_base"
    source_dir="$eq_dir/source"
    output_sample_dir="$OUTPUT_BASE_DIR/$rel_eq_dir/$source_base"
    compile_log="$output_sample_dir/compile_all.log"
    functions_file="$output_sample_dir/functions.txt"

    TOTAL_SAMPLES=$((TOTAL_SAMPLES + 1))
    mkdir -p "$source_dir" "$output_sample_dir"

    if ! cmp -s "$source_path" "$source_dir/$source_name"; then
        cp "$source_path" "$source_dir/$source_name"
    fi
    cp "$COMPILE_TEMPLATE" "$source_dir/compile_all.sh"
    chmod +x "$source_dir/compile_all.sh"

    echo ""
    echo "============================================================"
    echo "[$TOTAL_SAMPLES/${#SAMPLE_SOURCES[@]}] Sample: $sample_label"
    echo "Source dir: $source_dir"
    echo "Output dir: $output_sample_dir"
    echo "============================================================"

    if ! (cd "$source_dir" && ./compile_all.sh "$source_name") > "$compile_log" 2>&1; then
        echo "Compile finished with failures; missing binaries will be skipped. Log: $compile_log" >&2
    fi

    mapfile -t FUNCTIONS < <("$PYTHON_BIN" "$FUNCTION_LISTER" "$source_dir/$source_name" | sort -u)
    printf '%s\n' "${FUNCTIONS[@]}" > "$functions_file"

    if (( ${#FUNCTIONS[@]} == 0 )); then
        echo "No non-main functions found; skipping sample."
        SKIPPED_SAMPLES=$((SKIPPED_SAMPLES + 1))
        continue
    fi

    echo "Functions: ${FUNCTIONS[*]}"

    for function_name in "${FUNCTIONS[@]}"; do
        TOTAL_FUNCTIONS=$((TOTAL_FUNCTIONS + 1))
        output_function_dir="$output_sample_dir/$function_name"
        mkdir -p "$output_function_dir"
        pair_count=0
        total_pairs=0

        for ((i = 0; i < ${#IDS[@]} - 1; i++)); do
            left_id="${IDS[$i]}"
            left_name="$(binary_name_for_id "$source_base" "$left_id")"
            left_bin="$source_dir/$left_name"
            [[ -f "$left_bin" ]] || continue

            for ((j = i + 1; j < ${#IDS[@]}; j++)); do
                right_id="${IDS[$j]}"
                right_name="$(binary_name_for_id "$source_base" "$right_id")"
                right_bin="$source_dir/$right_name"
                [[ -f "$right_bin" ]] || continue
                total_pairs=$((total_pairs + 1))
            done
        done

        if (( total_pairs == 0 )); then
            echo "[$sample_label] [$function_name] No complete binary pairs found; skipping."
            continue
        fi

        skipped_completed_pairs=0
        for ((i = 0; i < ${#IDS[@]} - 1; i++)); do
            left_id="${IDS[$i]}"
            left_name="$(binary_name_for_id "$source_base" "$left_id")"
            left_bin="$source_dir/$left_name"
            [[ -f "$left_bin" ]] || continue

            for ((j = i + 1; j < ${#IDS[@]}; j++)); do
                right_id="${IDS[$j]}"
                right_name="$(binary_name_for_id "$source_base" "$right_id")"
                right_bin="$source_dir/$right_name"
                [[ -f "$right_bin" ]] || continue

                pair_count=$((pair_count + 1))
                log_file="${output_function_dir}/${function_name}_${left_id}_${right_id}.log"
                if [[ "$SKIP_COMPLETED_RESULTS" != "0" ]] && validation_result_log_is_complete "$log_file"; then
                    skipped_completed_pairs=$((skipped_completed_pairs + 1))
                    TOTAL_SKIPPED_PAIR_JOBS=$((TOTAL_SKIPPED_PAIR_JOBS + 1))
                    continue
                fi

                TOTAL_PAIR_JOBS=$((TOTAL_PAIR_JOBS + 1))
                wait_for_slot
                run_pair "$sample_label" "$function_name" "$left_id" "$right_id" \
                    "$left_bin" "$right_bin" "$output_function_dir" "$pair_count" "$total_pairs" &
                active_jobs=$((active_jobs + 1))
            done
        done

        if (( skipped_completed_pairs > 0 )); then
            echo "[$sample_label] [$function_name] Skipped completed pairs: $skipped_completed_pairs/$total_pairs"
        fi

        wait_for_all_jobs

        shopt -s nullglob
        function_logs=("$output_function_dir"/*.log)
        shopt -u nullglob
        if (( ${#function_logs[@]} > 0 )); then
            write_summary_file "$output_function_dir/results_summary.txt" \
                "$PYTHON_BIN" -m scripts.function_tracer_pcode.validation.result_summary \
                    --function-summary \
                    --canonical-only \
                    --function-name "$function_name" \
                    --summary-level "$VALIDATION_SUMMARY_LEVEL" \
                    "${function_logs[@]}"
        fi
    done
done

wait_for_all_jobs

mapfile -t ALL_LOG_FILES < <(find "$OUTPUT_BASE_DIR" -type f -name "*.log" ! -name "compile_all.log" | sort)
if (( ${#ALL_LOG_FILES[@]} > 0 )); then
    write_summary_file "$OUTPUT_BASE_DIR/overall_summary.txt" \
        "$PYTHON_BIN" -m scripts.function_tracer_pcode.validation.result_summary \
            --overall-summary \
            --canonical-only \
            --summary-level "$VALIDATION_SUMMARY_LEVEL" \
            --health-summary-json "$OUTPUT_BASE_DIR/run_health_summary.json" \
            --health-summary-text "$OUTPUT_BASE_DIR/run_health_summary.txt" \
            "${ALL_LOG_FILES[@]}"
fi

cat >> "$OUTPUT_BASE_DIR/run_manifest.txt" <<EOF
completed_samples=$TOTAL_SAMPLES
skipped_samples=$SKIPPED_SAMPLES
total_functions=$TOTAL_FUNCTIONS
total_pair_jobs=$TOTAL_PAIR_JOBS
total_skipped_pair_jobs=$TOTAL_SKIPPED_PAIR_JOBS
run_pair_failures=$RUN_PAIR_FAILURES
EOF

echo ""
echo "EqBench all-sample matrix finished."
echo "Output directory: $OUTPUT_BASE_DIR"
echo "Overall summary: $OUTPUT_BASE_DIR/overall_summary.txt"
echo "Run manifest: $OUTPUT_BASE_DIR/run_manifest.txt"
